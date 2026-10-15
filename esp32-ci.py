#!/usr/bin/env -S uv run --script
#
# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "flask",
#     "GitPython",
#     "tinkerforge_util >= 1.7.0",
#     "ansi2html",
#     "junit2html"
# ]
# ///

"""
Install instructions (assuming Debian >= 13.6)
- install git, curl, uv
- create ci user
- create 'workspace' directory in /home/ci
- clone gits into the workspace (use ssh to clone!)
  - at least esp32-ci and esp32-firmware
- create a config.jsonc in the workspace (see class Config)
- run esp32-ci.py --workspace /path/to/workspace
  or copy esp32-ci.service to /etc/systemd/system and run
  systemctl daemon-reload && systemctl enable esp32-ci.service

- on each testbox
    - if ESP is warp2-AbCd, set Pi's hostname to warp2-AbCd-pi
    - set password to the one in vaultwarden
    - install raspbian lite 64 bit
    - sudo apt update && sudo apt upgrade
    - install uv
    - install brickd
- for each testbox
    - make sure this machine can ssh into the testbox (ssh-copy-id pi@testbox-host)
- on each testbox
    - enable ram overlay
- if testbox for environment with secure boot and flash encryption:
    - add zzz_overrides in workspace, symlink into esp32-firmware/software
    - add entry such as
        [env:warp4]
        board_build.partitions = default_16MB_encrypted.csv
        custom_fast_flash = off
        upload_protocol = custom
        upload_command = esptool --port $UPLOAD_PORT --baud $UPLOAD_SPEED write-flash 0x1000 build_latest/warp4*_esptool_secure_*.bin
        # Expected format of the custom_secure_boot setting: "<UID/name>,<efuses block3>,<factory MAC>,<optional non-derived flash encryption key (efuses block1)>"
        # Example:
        custom_secure_boot = "8555,0000123456789abcdef0123456789abcdef012345678ab00cdef012345678900,a8:03:2a:12:34:56"
    - non-derived flash encryption is is necessary if esp32/secure_device was called with "deterministic": false while provisioning the ESP. This is the common case!
"""

"""
TODO
- esp-idf-size abs + diff https://docs.espressif.com/projects/esp-idf/en/v5.2/esp32/api-guides/performance/size.html#comparing-two-binaries
    -> per commit would be nice but slow
- local commits are not dropped

"""

import argparse
from collections import deque
from dataclasses import dataclass, asdict, KW_ONLY, field
from datetime import datetime
from email.message import EmailMessage
from email.policy import SMTP
import itertools
import json
import os
from pathlib import Path
from queue import Queue, Empty
import re
import subprocess
import smtplib
import sys
from textwrap import dedent, indent
import time
import threading
import typing
import io
import traceback
import html
from tempfile import NamedTemporaryFile, TemporaryDirectory
import signal

from flask import Flask, Response
import git
import tinkerforge_util as tfutil
from ansi2html import Ansi2HTMLConverter
from junit2htmlreport.matrix import TextReportMatrix, HtmlReportMatrix
from junit2htmlreport.case_result import CaseResult

REPO_NAME = 'esp32-ci'


def flatten(list_of_lists):
    return sum(list_of_lists, [])


def read_jsonc(path: Path):
    # Matches /* */ and // comments
    return json.loads(re.sub(r"/\*.*?\*/|//[^\n]*", "", path.read_text(), flags=re.DOTALL))


@dataclass
class CIState:
    next_task_number: int = 1

    @staticmethod
    def read(workspace_dir: Path):
        f = workspace_dir / "ci_state.json"
        if f.exists():
            return CIState(**json.loads(f.read_text()))
        return CIState()

    def write(self, workspace_dir: Path):
        f = workspace_dir / "ci_state.json"
        (workspace_dir / "ci_state.json").write_text(json.dumps(asdict(self)))


@dataclass
class Config:
    # Fall-back mail address to send mails to when something breaks
    maintainer_mail: str = ""

    # Mails are only sent to those domains
    # Used to not send mails to somebody when accepting pull-requests
    mail_domain_allowlist: list[str] = field(default_factory=list)

    # Hostnames of the ESPs in testboxes
    # We assume that for the ESP 'warp-AbCd',
    # the corresponding RPI has the hostname 'warp-AbCd-pi',
    # the username 'pi' and the machine that this script runs on
    # has ssh keys configured to connect to warp-AbCd-pi.
    testboxes: list[str] = field(default_factory=list)

    # Map of ESP host prefixes to pio environments.
    # By default, we do a prefix-match with the host's [A-Za-z0-9] prefix
    # to the same prefix of the environment to know which firmwares can be flashed on which device.
    # For example the ESP 'warp-AbCd' will be considered for the environments
    # 'warp', 'warp_with_ocpp' and 'warp_signed', but not 'warp2', 'warp2_signed' or 'esp32'
    # To reduce the amount of hardware required, add overrides here:
    # For example if "env_prefix_overrides" is {"esp32": "warp", "esp32_ethernet": "warp2"}
    # will consider the ESP 'warp-AbCd' as a valid target to flash a firmware built from the "esp32_signed" environment.
    env_prefix_overrides: dict[str, str] = field(default_factory=dict)

    smtp_server: str = ""
    smtp_user: str = ""
    smtp_pass: str = ""

    # If true, does not send mails but writes .eml files to /tmp/
    smtp_debug: bool = True

    # How many tasks are allowed to run in parallel
    task_processors: int = field(default_factory=os.cpu_count)

    @staticmethod
    def read(workspace_dir: Path):
        f = workspace_dir / "config.jsonc"
        if f.exists():
            return Config(**read_jsonc(f))
        return Config()


@dataclass
class Environment:
    # Name of the pio environment
    name: str
    # Keep artifacts
    artifacts: bool
    # Build nightly firmware (i.e. with debug module)
    nightly: bool
    # Pass "-e name" to pio
    # Set to false to build default environment
    pass_env: bool
    # Path to run pio in
    working_dir: Path


@dataclass
class Testbox:
    esp_host: str
    type_: str = field(init=False)
    pi_host: str = field(init=False)
    pi_user: str = 'pi'

    def __post_init__(self):
        self.type_ = self.esp_host.split("-")[0]

        if "." in self.esp_host:
            esp_hostname, rest = self.esp_host.split(".", maxsplit=1)
            rest = '.' + rest
        else:
            esp_hostname, rest = self.esp_host, ""

        self.pi_host = f'{esp_hostname}-pi{rest}'


@dataclass
class Resources:
    testboxes: list[Testbox]

    compiler: int = 1

    all_testbox_types: list[str] = field(init=False)

    def __post_init__(self):
        self.all_testbox_types = [t.type_ for t in self.testboxes]


@dataclass
class Task:
    # Back-reference to Main, use to get workspace, task_queue, etc
    m: 'Main'

    _: KW_ONLY

    name: str
    name_prefix: str = ""

    task_number: int = field(init=False)

    keep_in_completed_when_skipped: bool = True
    keep_in_completed_when_finished: bool = True

    # in seconds. Set to -1 to run without timeout
    timeout: float

    _then: typing.Callable[[typing.Self], typing.Self | list[typing.Self]] = None
    _finally: typing.Callable[[typing.Self], typing.Self | list[typing.Self]] = None

    # head SHA of each managed repo at the time the task was created
    # Initialized in __post_init__. TODO: can we call get_repo_heads as the default factory?
    repo_heads: dict = field(default_factory=dict, init=False)

    State = typing.Literal[
        'enqueued',  # default state before task.start() was called
        'running',   # set when task.start() is called
        'finished', 'skipped',  # both count as success
        'timed_out', 'failed', 'aborted'  # all count als failure
    ]

    __on_started_fns: list[typing.Callable[[typing.Self], None]] = field(default_factory=list)
    __on_done_fns: list[typing.Callable[[typing.Self], State | None]] = field(default_factory=list)

    # Set when start is called
    start_timestamp: float = None
    start_datetime: datetime = None
    state: State = 'enqueued'
    _log: io.StringIO = field(default_factory=io.StringIO)

    __post_init_called: bool = False

    def __post_init__(self):
        if self.name_prefix != "":
            self.name = f"{self.name_prefix}: {self.name}"

        self.repo_heads = self.get_repo_heads()
        self.task_number = self.m.next_task_number()

        self.__post_init_called = True

    # Called just before this task's tick function will return 'finished' for the first time.
    # This task is passed as parameter as if then is a member function.
    # Return a task or list of tasks to run after this task is finished.
    def then(self, fn: typing.Callable[[typing.Self], typing.Self | list[typing.Self]]) -> typing.Self:
        self._then = fn
        return self

    # Called just before this task's tick function will return something else than 'running' for the first time.
    # This task is passed as parameter as if then is a member function.
    # Return a task or list of tasks to run after this task is done.
    # If tick returned 'finished' and 'then' was called on this task, the then-tasks are created first
    # and finally_ is called on them.
    # In other words: A task with then-tasks does not execute finally-tasks if it finishes, the finally-tasks are
    # pushed to the then-tasks instead.
    # A task without then-tasks or one that did not finish successfully, will execute finally-tasks.
    def finally_(self, fn: typing.Callable[[typing.Self], typing.Self | list[typing.Self]]) -> typing.Self:
        self._finally = fn
        return self

    @staticmethod
    def __verify_state(x):
        if x not in typing.get_args(Task.State):
            raise Exception(f"Unknown state {repr(x)}")
        return x

    def start_datestr(self) -> str:
        return self.start_datetime.isoformat(" ") if self.state != 'enqueued' else 'enqueued'

    def __set_state(self, new_state: State):
        if new_state == self.state:
            return

        old_state = self.state
        self.state = new_state

        if old_state == 'enqueued' and new_state == 'running':
            for fn in self.__on_started_fns:
                fn(self, self.m.resources)
            return

        if old_state != 'running':
            return

        for fn in self.__on_done_fns:
            new_state = fn(self, self.m.resources)

            if new_state is not None:
                self.state = self.__verify_state(new_state)
                if new_state != 'finished':
                    break

        new_tasks = []

        # then-tasks are only enqueued when this task succeeded
        if self._then is not None and self.state == 'finished':
            try:
                new_tasks = self._then(self)
            except Exception as e:
                self.log(datetime.now().isoformat(sep=' '), "Failed to create continuation tasks (by calling self._then):\n", traceback.format_exc())
                self.state = 'failed'

            if isinstance(new_tasks, Task):
                new_tasks = [new_tasks]

        # finally-tasks are either chained to the then tasks created above,
        # or are enqueued now if this task failed or there are no then-tasks
        if self._finally is not None:
            if len(new_tasks) > 0:
                for t in new_tasks:
                    if t._finally is not None:
                        raise Exception("More than one finally not supported yet!")
                    t.finally_(self._finally)
            else:
                try:
                    new_tasks = self._finally(self)
                except Exception as e:
                    self.log(datetime.now().isoformat(sep=' '), "Failed to create continuation tasks (by calling self._finally):\n", traceback.format_exc())
                    self.state = 'failed'

                if isinstance(new_tasks, Task):
                    new_tasks = [new_tasks]

        for t in new_tasks:
            self.m.enqueue(t)

    def can_start(self, resources: Resources):
        if not self.__post_init_called:
            self.log("Task.__post_init__ was not called. Was this function overwritten without a super().__post_init__() call?")
            new_state = 'failed'

        return self._can_start(resources)

    def start(self):
        new_state = self.state

        if self.state == 'enqueued':
            self.start_timestamp = time.monotonic()
            self.start_datetime = datetime.now().replace(microsecond=0)
            try:
                new_state = self.__verify_state(self._start())
            except Exception as e:
                self.log(datetime.now().isoformat(sep=' '), "Failed to start task:\n", traceback.format_exc())
                new_state = 'failed'

        self.__set_state(new_state)
        return self.state

    def abort(self):
        new_state = self.state

        if self.state == 'running':
            try:
                new_state = self.__verify_state(self._abort())
            except Exception as e:
                self.log(datetime.now().isoformat(sep=' '), "Failed to abort task:\n", traceback.format_exc())
                new_state = 'failed'

        self.__set_state(new_state)
        return self.state

    def tick(self):
        new_state = self.state

        if self.state == 'running':
            if self.timeout > -1 and time.monotonic() - self.start_timestamp > self.timeout:
                return self.abort()

            try:
                new_state = self.__verify_state(self._tick())
            except Exception as e:
                self.log(datetime.now().isoformat(sep=' '), "Failed to tick task:\n", traceback.format_exc())
                new_state = 'failed'

        self.__set_state(new_state)
        return self.state

    def log(self, *args, **kwargs):
        print(*args, **kwargs, file=self._log)

    def get_repo_heads(self):
        result = {}
        for d in self.m.workspace.iterdir():
            if not d.is_dir():
                continue

            if not (d / ".git").is_dir():
                continue

            result[str(d)] = git.Repo(d).head.object.hexsha
        return result

    # Implement/override these methods when writing a task

    # Will only be called when state is 'enqueued' and self._can_start() returned True.
    # Return 'running' when start succeeded.
    # Return something else when not.
    def _start(self) -> State:
        return 'running'

    # Will only be called when state is 'running'.
    # Return 'aborted' when abort succedded.
    # Return something else when not.
    def _abort(self) -> State:
        return 'aborted'

    # Will only be called when state is 'running'.
    # Return 'running' when not done.
    # Return something else when done.
    def _tick(self):
        return 'finished'

    # Called after self.state transitioned from 'enqueued' to 'running'.
    # Acquire resources here.
    # This is not called if _start returned something else than 'running', i.e. when the start failed.
    def on_started(self, fn: typing.Callable[[typing.Self, Resources], None]):
        self.__on_started_fns.append(fn)

    # Called after self.state transitioned from 'running' to some other state
    # Release resources here.
    # This is not called if _start returned something else than 'running', i.e. when the start failed.
    # Return new state for example if post-processing fails. Return None (= omit return) to leave state as-is.
    def on_done(self, fn: typing.Callable[[typing.Self, Resources], State | None]):
        self.__on_done_fns.append(fn)

    # BEGIN RESOURCE MANAGEMENT

    # Return true if all resources to start are available.
    # Don't acquire them yet!
    def _can_start(self, resources: Resources):
        return True

    # END RESOURCE MANAGEMENT

    def mail_subject(self):
        return f"{self.name}"

    # Return plain text and HTML version
    def mail_body(self) -> (str, (str, str), str):
        plain = f"{self.name} {self.state} {self.start_datestr()} Task #{self.task_number}"

        html = f'<b>{self.name}</b> {self.state_html()} {self.start_datestr()} Task #{self.task_number}'
        if self._log.tell() != 0:
            html = dedent(f"""\
                <details>
                    <summary>{html}</summary>
                    <pre>
                        {self._log.getvalue()}
                    </pre>
                </details>
            """)

        return plain, ('', ''), html

    def mail_add_attachments(self, msg: EmailMessage):
        msg.add_attachment(self._log.getvalue().encode('utf-8'), maintype="text", subtype="plain", filename=f"{self.task_number}-log.txt")

    def mail_recipients(self) -> list[str]:
        if self.state in ['timed_out', 'failed']:
            return [self.m.config.maintainer_mail]

        return []

    def __str__(self):
        align = max(len(x) for x in typing.get_args(self.State))
        return f"{self.state:>{align}} {self.task_number} {type(self).__name__}"

    def state_html(self):
        match self.state:
            case 'enqueued' | 'running' | 'skipped':
                return f'<span style="color:dimgray">{self.state}</span>'
            case 'finished':
                return f'<span style="color:green">{self.state}</span>'
            case 'timed_out' | 'failed':
                return f'<span style="color:red">{self.state}</span>'
            case 'aborted':
                return f'<span style="color:darkorange">{self.state}</span>'


@dataclass
class RunProcess(Task):
    _: KW_ONLY

    name: str = "Run process"

    working_dir: Path
    cmd: str | list[str]
    env_vars: dict[str, str] = field(default_factory=lambda: os.environ)
    redirect_stderr_to_stdout: bool = True
    popen_args: dict = field(default_factory=dict)

    proc: subprocess.Popen = None
    stdout: bytes | str = bytes()
    stderr: bytes | str = bytes()

    def __post_init__(self):
        super().__post_init__()

        self.on_done(lambda self, resources: self._log_output())

    def _start(self):
        with tfutil.ChangedDirectory(self.working_dir):
            self.log(f"{datetime.now().isoformat()} Starting {self.name} ({self.cmd if isinstance(self.cmd, str) else ' '.join(self.cmd)}) in {self.working_dir.resolve(strict=True)}")

            os_environ_set = set(os.environ.items())
            env_set = set(self.env_vars.items())
            added = env_set - os_environ_set
            removed = os_environ_set - env_set
            if len(added) != 0:
                self.log(f"Environment variables added {added}")
            if len(removed) != 0:
                self.log(f"Environment variables removed {removed}")

            self.proc = subprocess.Popen(self.cmd,
                                         env=self.env_vars,
                                         stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT if self.redirect_stderr_to_stdout else subprocess.PIPE,
                                         start_new_session=True,
                                         **self.popen_args)

            os.set_blocking(self.proc.stdout.fileno(), False)
            if not self.redirect_stderr_to_stdout:
                os.set_blocking(self.proc.stderr.fileno(), False)

        return 'running'

    def _tick(self):
        self._communicate()

        if self.proc.returncode is None:
            # process still running
            if self.timeout > -1 and time.monotonic() - self.start_timestamp > self.timeout:
                self.log(f"{datetime.now().isoformat()} Process timed out; aborting")
                os.killpg(os.getpgid(self.proc.pid), signal.SIGKILL)
                self._communicate()
                return 'timed_out'

            try:
                self.proc.wait(timeout=0.1)
            except subprocess.TimeoutExpired:
                pass

            return 'running'

        # process done
        return 'finished' if self.proc.returncode == 0 else 'failed'

    def _abort(self):
        if self.proc.returncode is None:
            self.log(f"{datetime.now().isoformat()} Aborting process")
            os.killpg(os.getpgid(self.proc.pid), signal.SIGKILL)
            self._communicate()

        return 'aborted'

    def _log_output(self):
        if self.redirect_stderr_to_stdout:
            self.log("=========== Begin Output ===========")
            self.log(self.stdout.decode('utf-8'))
            self.log("===========  End Output  ===========")
        else:
            self.log("=========== Begin stdout ===========")
            self.log(self.stdout.decode('utf-8'))
            self.log("============ End stdout ============")
            self.log("=========== Begin stderr ===========")
            self.log(self.stderr.decode('utf-8'))
            self.log("============ End stderr ============")


    def _communicate(self):
        output = self.proc.stdout.read()
        if output is not None:
            self.stdout += output

        if not self.redirect_stderr_to_stdout:
            output = self.proc.stderr.read()
            if output is not None:
                self.stderr += output


    def _mail_body_html_details(self, content):
        return dedent(f"""\
            <details>
                <summary><b>{self.name}</b> {self.state_html()} {self.start_datestr()} Task #{self.task_number}</summary>
                {content}
            </details>
        """)

    def mail_body(self):
        plain = super().mail_body()[0]

        html = self._mail_body_html_details(f"""<div class="body_foreground body_background" style="font-size: normal; padding: 10px;">
                    <pre class="ansi2html-content">{Ansi2HTMLConverter().convert(self._log.getvalue().strip(), full=False)}</pre>
                </div>""")

        return plain, ('run_process', Ansi2HTMLConverter().produce_headers()), html

    def mail_add_attachments(self, msg: EmailMessage):
        msg.add_attachment(self._log.getvalue().encode('utf-8'), maintype="text", subtype="plain", filename=f"{self.task_number}-{self.name}-log.txt")

    def mail_recipients(self):
        return []

    def __str__(self):
        return super().__str__() + f" {self.name}"


@dataclass
class CompileFirmware(RunProcess):
    _: KW_ONLY

    env: Environment

    name: str = "Compile firmware"
    working_dir: Path = field(init=False)
    cmd: list[str] = field(init=False)
    timeout: float = 5 * 60

    # Filled when build finishes successfully
    artifacts: list[Path] = field(default_factory=list)

    redirect_stderr_to_stdout: bool = False

    compilers_acquired: int = 0

    def __post_init__(self):
        super().__post_init__()

        self.working_dir = self.env.working_dir

        self.env_vars = os.environ | {
            "PLATFORMIO_WORKSPACE_DIR": f".pio{self.env.name}",
            "PLATFORMIO_CORE_DIR": str(self.m.workspace / ".platformio"),
            "PLATFORMIO_FORCE_ANSI": "true",
            "PLATFORMIO_DISABLE_PROGRESSBAR": "true"
        }

        if self.env.nightly:
            self.env_vars |= {"PLATFORMIO_BUILD_FLAGS": "-DNIGHTLY"}

        self.cmd = ["uv", "run", "pio", "run"]
        if self.env.pass_env:
            self.cmd += ["-e", self.env.name]

        self.on_started(lambda self, resources: self._acquire_compiler(resources))
        self.on_done(lambda self, resources: self._release_compiler(resources))

        self.on_done(lambda self, resources: self._collect_artifacts(resources))

    def _can_start(self, resources: Resources):
        return resources.compiler >= 1

    def _acquire_compiler(self, resources: Resources):
        resources.compiler -= 1
        self.compilers_acquired += 1

    def _release_compiler(self, resources: Resources):
        resources.compiler += self.compilers_acquired
        self.compilers_acquired = 0

    def _communicate(self):
        result = super()._communicate()

        if self.compilers_acquired > 0 and f"Linking .pio{self.env.name}/build/{self.env.name}/firmware.elf".encode('utf-8') in self.stdout:
            self._release_compiler(self.m.resources)

        return result

    def _collect_artifacts(self, resources: Resources):
        if self.state == 'finished':
            self.artifacts = [f.resolve(strict=True) for f in (self.working_dir / "build").glob("firmware_latest*")]
            self.log("Produced artifacts", ", ".join(str(x) for x in self.artifacts))


@dataclass
class AcquireTestbox(Task):
    _: KW_ONLY

    name: str = "Acquire Testbox"
    timeout: float = 1
    keep_in_completed_when_finished: bool = False

    required_testbox_type: str

    testbox: Testbox | None = None

    def __post_init__(self):
        super().__post_init__()
        self.on_started(lambda self, resources: self._acquire(resources))

    def _can_start(self, resources: Resources):
        return any(t.type_ == self.required_testbox_type for t in resources.testboxes)

    def _acquire(self, resources: Resources):
        self.testbox = next(t for t in resources.testboxes if t.type_ == self.required_testbox_type)
        resources.testboxes.remove(self.testbox)


@dataclass
class RunOnTestbox(RunProcess):
    _: KW_ONLY

    testbox: Testbox



@dataclass
class ReleaseTestbox(Task):
    _: KW_ONLY

    name: str = "Release Testbox"
    timeout: float = 1
    keep_in_completed_when_finished: bool = False

    testbox: Testbox

    def __post_init__(self):
        super().__post_init__()
        self.on_done(lambda self, resources: self._release(resources))

    def _release(self, resources: Resources):
        if self.testbox is not None:
            resources.testboxes.append(self.testbox)
            self.testbox = None


@dataclass
class PrepareRPI(RunOnTestbox):
    _: KW_ONLY

    esp32_master_repo: Path

    timeout: float = 10
    name: str = "Prepare Raspberry Pi"
    working_dir: Path = Path(".")
    cmd: list[str] = field(init=False)
    keep_in_completed_when_finished: bool = False

    def __post_init__(self):
        super().__post_init__()
        self.cmd = f'git archive HEAD . | ssh {self.testbox.pi_user}@{self.testbox.pi_host} '\
            '"'\
            'mv ~/tf/esp32-firmware/software/.venv /tmp/.venv; ' \
            'rm -rf ~/tf/esp32-firmware && ' \
            'mkdir -p ~/tf/esp32-firmware/software && ' \
            'mv /tmp/.venv ~/tf/esp32-firmware/software/.venv; '\
            'cd ~/tf/esp32-firmware/software && '\
            'tar -xf -' \
            '"'


        self.working_dir = self.esp32_master_repo.resolve(strict=True)
        self.popen_args = {"shell": True}


@dataclass
class UploadFirmware(RunOnTestbox):
    _: KW_ONLY

    file: Path

    timeout: float = 10
    name: str = "Upload firmware"
    working_dir: Path = Path(".")
    cmd: list[str] = field(init=False)
    keep_in_completed_when_finished: bool = False

    def __post_init__(self):
        super().__post_init__()
        self.cmd = [
            "scp",
            str(self.file.resolve(strict=True)),
            f"{self.testbox.pi_user}@{self.testbox.pi_host}:/tmp/firmware.bin"
        ]


@dataclass
class FlashFirmware(RunOnTestbox):
    _: KW_ONLY

    timeout: float = 120
    name: str = "Flash firmware"
    working_dir: Path = Path(".")
    cmd: list[str] = field(init=False)
    keep_in_completed_when_finished: bool = False

    def __post_init__(self):
        super().__post_init__()
        self.cmd = [
            "ssh",
            f"{self.testbox.pi_user}@{self.testbox.pi_host}",
            "-t",
            f"bash -lc \"cd ~/tf/esp32-firmware/software; ./ff --no-serial --port /dev/ttyUSB0 /tmp/firmware.bin\""
        ]


@dataclass
class RunTests(RunOnTestbox):
    _: KW_ONLY

    test_filter: str = '*/*/*'

    timeout: float = -1
    name: str = "Run tests"
    working_dir: Path = Path(".")
    cmd: list[str] = field(init=False)

    plain_summary: str = None
    html_summary: str = None
    html_details: str = None

    def __post_init__(self):
        super().__post_init__()

        tf = ""
        if self.test_filter != "":
            tf = f"'{self.test_filter}'"

        self.cmd = [
            "ssh",
            "-q",
            f"{self.testbox.pi_user}@{self.testbox.pi_host}",
            "-t",
            f"bash -lc \"cd tf/esp32-firmware/software; test_runner/test_runner.py {tf} --host {self.testbox.esp_host} --brickd localhost --junit-xml\""
        ]

        self.on_done(lambda self, _: self._convert_to_html())

    def _convert_to_html(self):
        if self.state != 'finished':
            return

        with TemporaryDirectory() as d:
            plain_matrix = TextReportMatrix()
            html_matrix = HtmlReportMatrix(d)

            with NamedTemporaryFile(dir=d, delete_on_close=False) as f:
                f.write(self.stdout)
                f.close()
                try:
                    plain_matrix.add_report(f.name)
                    html_matrix.add_report(f.name, show_toc=False)
                except Exception:
                    self.log(traceback.format_exc())
                    return 'failed'

                self.plain_summary = plain_matrix.summary()
                self.html_summary = html_matrix.summary()
                self.html_details = (Path(d) / (f.name + '.html')).read_text()

        if plain_matrix.result_stats[CaseResult.FAILED] != 0:
            return 'failed'

    def mail_body(self):
        tests_executed = self.state == 'finished' or self.state == 'failed' and self.html_details is not None

        if not tests_executed:
            return super().mail_body()



        style_start = self.html_summary.index('<style type="text/css">')
        style_end = self.html_summary.index('</style>') + len('</style>')

        style = self.html_summary[style_start:style_end]

        # limit this style to only apply in the junit div
        style = re.sub(r"^(.* )\{$", r"div.junit \1{", style, flags=re.MULTILINE)
        style = style.replace(",", ", div.junit ")

        table_start = self.html_summary.index('<table class="mx-table">')
        table_end = self.html_summary.rindex('</table>') + len('</table>')
        table = self.html_summary[table_start:table_end]

        # Inject checkboxes to show/hide by result type
        # Also add script that hides passed tests by default.
        for result in ['passed', 'failed', 'skipped']:
            table = table.replace(
                f'<th class="{result}">{result.title()}</th>',
                dedent(f'''\
                <td>
                    <input
                        type="checkbox"
                        {'checked=""' if result != 'passed' else ''}
                        onchange="document.querySelectorAll(\'tr:has(td.mx-res-{result})\').forEach(x => x.hidden = !event.target.checked)"
                    >
                </td>
                <th class="{result}">{result.title()}</th>''')
            )
        style += "<script>window.addEventListener(\"load\", (event) => document.querySelectorAll('tr:has(td.mx-res-passed)').forEach(x => x.hidden = true));</script>"


        details_start = self.html_details.index('</h1>') + len('</h1>')
        details_end = self.html_details.index('<p class="footer">')
        details = self.html_details[details_start:details_end]

        table = f'<div class="junit">{table} <details><summary>Test results</summary>{details}</details></div>'

        table = re.sub(r'href="[^#]*', 'href="', table)

        plain, _style, _html = super().mail_body()
        plain += "\n" + indent(self.plain_summary, "    ")

        return plain, ('run_tests', style), super()._mail_body_html_details(table)

    def mail_add_attachments(self, msg: EmailMessage):
        if self.state != 'finished':
            return super().mail_add_attachments(msg)

        msg.add_attachment(self.stdout, maintype="application", subtype="junit+xml", filename=f"{self.task_number}-{self.name}-junit.xml")


@dataclass
class PullRepos(Task):
    _: KW_ONLY

    name: str = 'Pull Repos'

    timeout: float = 30

    keep_in_completed_when_skipped: bool = False

    thread: threading.Thread = None
    fetch_timeout: float = 10
    pull_timeout: float = 60

    repo_heads_post: dict = field(default_factory=dict)

    def __post_init__(self):
        super().__post_init__()
        self.on_done(lambda self, _: self._update_repos_post_build())

    def _start(self):
        self.log(f"{datetime.now().isoformat()} Starting to pull repos")
        self._q = Queue()
        self._stop_event = threading.Event()
        self.thread = threading.Thread(target=self._pull_repos, args=(self.m.workspace,))
        self.thread.start()
        return 'running'

    def _tick(self):
        if self.thread.is_alive():
            return 'running'

        self.thread.join()
        result = self._q.get()

        if result == 'restart':
            # sys.exit only raises an exception, we want to stop all threads.
            os._exit(os.EX_OK)
            return 'skipped'

        return result

    def _update_repos_post_build(self):
        self.repo_heads_post = self.get_repo_heads()

    def _abort(self):
        self._stop_event.set()
        self.thread.join()
        return 'aborted'

    def _pull_repo(self, d) -> typing.Literal['error', 'nothing', 'something']:
        if self._stop_event.is_set():
            self._q.put('aborted')
            return 'error'

        if not d.is_dir():
            self.log(f"Skipping {d}: not a directory")
            return 'nothing'

        if not (d / ".git").is_dir():
            self.log(f"Skipping {d}: not a git repository (no .git directory found)")
            return 'nothing'

        repo = git.Repo(d)
        origin = repo.remotes.origin
        origin.fetch(kill_after_timeout=self.fetch_timeout)

        head = repo.head.ref
        tracking = head.tracking_branch()

        c = list(tracking.commit.iter_items(repo, f'{head.path}..{tracking.path}'))

        if len(c) == 0:
            self.log(f"Skipping {d}: Fetch returned no new commits")
            return 'nothing'

        # Check stop_event again in case it was set while fetching.
        if self._stop_event.is_set():
            self._q.put('aborted')
            return 'error'

        self.log(f"Pulling {d}: {head.path}..{tracking.path}")

        info = origin.pull(repo.head.ref, kill_after_timeout=self.pull_timeout)[0]
        if info.flags & (info.ERROR | info.REJECTED) != 0:
            self.log(f"Failed to pull repo: {info.flags=}")
            self._q.put('failed')
            return 'error'

        return 'something'

    def _pull_repos(self, workspace):
        found_commits = False

        try:
            match self._pull_repo(workspace / REPO_NAME):
                case 'error':
                    return
                case 'nothing':
                    pass
                case 'something':
                    self._q.put('restart')
                    return

            for d in workspace.iterdir():
                if d == workspace / REPO_NAME:
                    continue

                match self._pull_repo(d):
                    case 'error':
                        return
                    case 'nothing':
                        pass
                    case 'something':
                        found_commits = True

        except Exception as e:
            self.log(traceback.format_exc())
            self._q.put('failed')
            return

        self._q.put('finished' if found_commits else 'skipped')

    def read_ci_config(self):
        envs = []

        for d in self.m.workspace.iterdir():
            if not d.is_dir():
                continue

            if not (d / "esp32_ci_config.jsonc").is_file():
                continue

            cfg = read_jsonc(d / "esp32_ci_config.jsonc")
            default_defaults = {
                "working_dir": ".",
                "pass_env": False,
                "artifacts": False,
                "nightly": False
            }
            defaults = default_defaults | {k: v for k, v in cfg.items() if k != "environments"}

            new_envs = [Environment(name=k, **(defaults | v)) for k, v in cfg["environments"].items()]
            for n in new_envs:
                n.working_dir = self.m.workspace / d / n.working_dir

            envs += new_envs

        return envs

    def mail_body(self):
        if self.state != 'finished':
            return super().mail_body()

        commits = self.get_commits()

        commits_plain, commits_html = self.format_commits(commits)

        html = dedent(f"""\
            <details style="display: block;" open>
                <summary><b>Pulling repos</b> {self.state_html()} {self.start_datestr()} Task #{self.task_number}</summary>
                <div style="padding-left: 64px" class="commits">{commits_html}</div>
            </details>
        """)

        plain = super().mail_body()[0]
        plain += f"\n{indent(commits_plain, "    ")}"

        return plain, ("pull_repos", "<style>.commits div:nth-child(odd) {background: #eeeeee;}</style>"), html

    def mail_recipients(self):
        result = set()

        commits = self.get_commits()
        for k, v in commits.items():
            for c in v:
                if c.author != c.committer:
                    result.add(c.committer.email)
                else:
                    result.add(c.author.email)
                    result.update(x.author.email for x in c.co_authors)

        return list(result)

    def get_commits(self):
        result = {}

        for d in self.m.workspace.iterdir():
            if not d.is_dir():
                continue

            if not (d / ".git").is_dir():
                continue

            d = str(d)
            if d not in self.repo_heads or d not in self.repo_heads_post:
                continue

            repo = git.Repo(d)
            head = repo.head.ref

            result[d] = list(head.tracking_branch().commit.iter_items(repo, f'{self.repo_heads[d]}..{self.repo_heads_post[d]}'))

        return result

    def format_commits(self, commits: dict[str, list[git.Commit]]):
        def actor_to_str(actor: git.Actor):
            return f"{c.author.email:>24}"

        changes_plain = []
        changes_html = []

        for repo, commit_list in commits.items():
            for c in commit_list:
                actors = [actor_to_str(a) for a in [c.author, *c.co_authors]]

                if c.author != c.committer:
                    actors.append("Committer: " + actor_to_str(c.committer))

                summary = c.summary.strip()
                message = c.message.strip()

                if len(message) > len(summary):
                    message = message.split("\n", maxsplit=1)[1].strip()
                else:
                    message = ""

                if len(summary) > 72:
                    message = summary[72:] + '\n' + message
                    summary = summary[:72] + '…'

                actors = " ".join([actor_to_str(a) for a in actors])

                plain = f'{summary:<73} {actors} {c.hexsha[:8]} +{c.stats.total['insertions']} -{c.stats.total['deletions']}'
                url = c.repo.remotes[0].url

                if "git@github.com" in url:
                    repo = url.split(":", maxsplit=1)[1]
                    link = f'<a href="https://github.com/{repo}/commit/{c.hexsha}">{c.hexsha[:8]}</a>'
                else:
                    link = f'{c.hexsha[:8]}'

                html_summary = f'<code style="height: 1.2rem; display: inline-block; align-content: center;">{summary}{"&nbsp;" * (73 - len(summary))} {actors.replace(" ", "&nbsp;")} {link}</code>'

                if len(message) > 0:
                    html = dedent(f"""\
                        <div><details>
                            <summary>
                                {html_summary}
                            </summary>
                            <pre style="padding-left: 18px;">{message}</pre>
                        </details></div>""")
                else:
                    html = f'<div style="padding-left: 18px;">{html_summary}</div>'

                changes_plain.append(plain)
                changes_html.append(html)

        return "\n".join(changes_plain), "\n".join(changes_html)



def format_html(tasks: list[Task]) -> (str, str, str):
    styles = {
        "base": dedent("""\
            <style>
                details {
                    display: block;
                    width: fit-content;
                }
            </style>""")
    }

    plain = ""
    html = ""

    for t in tasks:
        p, s, h = t.mail_body()
        styles[s[0]] = s[1]
        plain += "\n" + p
        html += "\n" + h

    return plain, styles, html


@dataclass
class SendEmail(Task):
    _: KW_ONLY

    name: str = 'Send email'

    sent_ci_fixed: bool = True

    timeout: float = -1

    def _start(self):
        return 'running'

    def _tick(self):
        last_fixed_sent = -1
        for i, task in enumerate(self.m.completed_tasks):
            if isinstance(task, SendEmail) and (task.state == 'skipped' or (task.state == 'finished' and task.sent_ci_fixed)):
                last_fixed_sent = i

        self.log(f"{last_fixed_sent=}")

        last_sent = -1
        for i, task in enumerate(self.m.completed_tasks):
            if isinstance(task, SendEmail) and task.state in ('skipped', 'finished'):
                last_sent = i

        self.log(f"{last_sent=}")

        def task_succeeded(t: Task):
            # TODO: is 'aborted' a failure or a success?
            return t.state in ('finished', 'aborted', 'skipped')

        tasks = [t for t in itertools.islice(self.m.completed_tasks, last_sent + 1, None)]

        self.log({t.task_number: task_succeeded(t) for t in tasks})

        self.sent_ci_fixed = all(task_succeeded(t) for t in tasks)

        self.log(f"{self.sent_ci_fixed=}")

        if last_sent != -1 and last_fixed_sent == last_sent and self.sent_ci_fixed:
            self.log("Nothing to send")
            return 'skipped'

        tasks = [t for t in itertools.islice(self.m.completed_tasks, last_fixed_sent + 1, None) if t.state != 'skipped']

        msg = EmailMessage()

        plain, styles, html = format_html(reversed(tasks))

        html = dedent(f"""\
            <html>
            <head>
            <meta charset="UTF-8">
            {"\n".join(styles.values())}
            </head>
            <body>
            {html}
            </body>
            </html>
            """)

        msg.set_content(plain)

        Path("/tmp/foo.html").write_text(html)
        msg.add_alternative(html, subtype='html')

        msg['From'] = self.m.config.smtp_user

        recipients = [x for x in set(flatten(t.mail_recipients() for t in tasks)) if x.split('@')[1] in self.m.config.mail_domain_allowlist]
        if self.m.config.smtp_debug or len(recipients) == 0:
            msg['To'] = [self.m.config.maintainer_mail]
        else:
            msg['To'] = recipients

        if self.sent_ci_fixed:
            msg['Subject'] = f"ESP32 CI {'(restarted) ' if last_sent == -1 else ''}fixed!"
        else:
            msg['Subject'] = f"ESP32 CI {'(restarted) ' if last_sent == -1 else ''}broken! [{", ".join(sorted(set(x.mail_subject() for x in tasks if not task_succeeded(x))))}]"

        for t in tasks:
            t.mail_add_attachments(msg)

        if self.m.config.smtp_debug:
            with open(f"/tmp/{self.task_number}.eml", 'wb') as fp:
                fp.write(msg.as_bytes(policy=SMTP))

        with smtplib.SMTP_SSL(self.m.config.smtp_server) as smtp:
            smtp.login(self.m.config.smtp_user, self.m.config.smtp_pass)
            smtp.send_message(msg)

        return 'finished'



def build_pipeline(m: 'Main'):
    def env_to_testbox_type(e: Environment, config: Config):
        env_name = e.name

        # Longest replacement prefix first:
        # Fixes replacing energy_manager_v2 with wem.
        for k in sorted(config.env_prefix_overrides.keys(), key=lambda x: len(x), reverse=True):
            v = config.env_prefix_overrides[k]

            if env_name.startswith(k):
                env_name = v + env_name.removeprefix(k)
                break

        return re.split(r"[^A-Za-z0-9]", env_name)[0]

    def artifacts_to_firmware(artifacts: list[Path]):
        try:
            return next(f for f in artifacts if "_esptool_secure_" in str(f) and str(f).endswith(".bin"))
        except StopIteration:
            pass

        return next(f for f in artifacts if str(f).endswith("_merged.bin"))

    def env_pipeline(e: Environment):
        tb_type = env_to_testbox_type(e, m.config)

        print(tb_type, m.resources.all_testbox_types)

        if tb_type not in m.resources.all_testbox_types:
            return CompileFirmware(m, name_prefix=e.name, env=e)

        return \
            CompileFirmware(m, name_prefix=e.name, env=e).then(lambda compile_firmware:
            AcquireTestbox(m, name_prefix=e.name, required_testbox_type=tb_type)
                .finally_(lambda at: ReleaseTestbox(m, name_prefix=e.name, testbox=at.testbox))
                .then(lambda at:
            PrepareRPI(m, name_prefix=e.name, testbox=at.testbox,
                esp32_master_repo=e.working_dir).then(lambda _:
            UploadFirmware(m, name_prefix=e.name, testbox=at.testbox,
                file=artifacts_to_firmware(compile_firmware.artifacts)).then(lambda _:
            FlashFirmware(m, name_prefix=e.name, testbox=at.testbox).then(lambda _:
            RunTests(m, name_prefix=e.name, testbox=at.testbox)
            )))))

    if m.force_build:
        m.force_build = False
        return \
            PullRepos(m).finally_(lambda pull_repos: [
                env_pipeline(e) for e in pull_repos.read_ci_config()
            ])

    return \
        PullRepos(m).then(lambda pull_repos: [
            env_pipeline(e) for e in pull_repos.read_ci_config()
        ])


class Main:
    def __init__(self, q: Queue, workspace: Path, force_build: bool = False):
        self.workspace = workspace.resolve(strict=True)
        self.ci_state = CIState.read(self.workspace)
        self.force_build = force_build

        self.config = Config.read(self.workspace)
        self.resources = Resources([
            Testbox(esp_host) for esp_host in self.config.testboxes
        ])

        self.q = q
        self.thread = threading.Thread(target=self.main, daemon=True)
        self.thread.start()

    def next_task_number(self):
        result = self.ci_state.next_task_number
        self.ci_state.next_task_number += 1
        self.ci_state.write(self.workspace)
        return result

    def enqueue(self, task):
        print(datetime.now().isoformat(sep=' '), task)
        self._task_queue.append(task)

    def main(self):
        last_pull = 0

        self._task_queue: deque[Task] = deque()
        self.running_tasks: list[Task] = []
        self.completed_tasks: deque[Task] = deque(maxlen=100)

        while True:
            try:
                match self.q.get(timeout=0.1):
                    case ['join']:
                        print('join')
                        return

                    # case ['build', env_names]:
                    #     print('build', env_names)
                    #     if 'all' in env_names:
                    #         env_names = [e.name for e in self.environments]
                    #
                    #     unknown_envs = [e for e in self.environments if e.name not in env_names]
                    #     if len(unknown_envs) != 0:
                    #         print("Unknown environments", *unknown_envs)
                    #
                    #     envs = [e for e in self.environments if e.name in env_names]
                    #
                    #     task = Build(
                    #             number=self.ci_state.build_number,
                    #             timeout=3 * 60 * len(envs),
                    #             jobs=[Job(build_number=self.ci_state.build_number, number=i, env=e, workspace=self.workspace) for i, e in enumerate(envs)]
                    #     )
                    #
                    #     print("Enqueueing", task)
                    #     task_queue.append(task)

                    case ['abort']:
                        print('abort')
                        for t in self.running_tasks:
                            t.abort()
                        self.running_tasks.clear()

                        self._task_queue = Queue()

                    case ['html', q_out]:
                        print('html')

                        styles = {}
                        html = ""

                        html += "<h3>Enqueued Tasks</h3>"
                        _, s, h = format_html(reversed(self._task_queue))
                        styles.update(s)
                        html += h

                        html += "<h3>Running Tasks</h3>"
                        _, s, h = format_html(reversed(self.running_tasks))
                        styles.update(s)
                        html += h

                        html += "<h3>Completed Tasks</h3>"
                        _, s, h = format_html(reversed(self.completed_tasks))
                        styles.update(s)
                        html += h

                        html = dedent(f"""\
                            <html>
                            <head>
                            <meta charset="UTF-8">
                            {"\n".join(styles.values())}
                            </head>
                            <body>
                            {html}
                            </body>
                            </html>
                            """)

                        q_out.put(html)


                    # case ['completed_tasks', q_out]:
                    #     print('completed_tasks', q_out)
                    #     q_out.put("<hr/>" + "<hr/>".join(t.get_row() for t in completed_tasks) + "<hr/>")
                    #
                    # case ['task_queue', q_out]:
                    #     print('task_queue', q_out)
                    #     q_out.put(task_queue)
                    #
                    # case ['current_task', q_out]:
                    #     print('current_task', q_out)
                    #     q_out.put(current_task)

                    case x:
                        print("hier", x)
            except Empty:
                pass

            # Work on current tasks
            for t in self.running_tasks:
                t.tick()

            done = [t for t in self.running_tasks if t.state in ['finished', 'timed_out', 'failed', 'aborted', 'skipped']]
            self.running_tasks = [t for t in self.running_tasks if t.state not in ['finished', 'timed_out', 'failed', 'aborted', 'skipped']]

            for t in done:
                print(datetime.now().isoformat(sep=" "), t)
                match t.state:
                    case 'skipped':
                        if t.keep_in_completed_when_skipped:
                            self.completed_tasks.append(t)
                    case 'finished':
                        if t.keep_in_completed_when_finished:
                            self.completed_tasks.append(t)
                    case _:
                        self.completed_tasks.append(t)


            # Task done? Start next task
            if len(self.running_tasks) < self.config.task_processors and len(self._task_queue) > 0:
                for t in self._task_queue:
                    if not t.can_start(self.resources):
                        continue

                    self._task_queue.remove(t)
                    t.start()
                    print(datetime.now().isoformat(sep=" "), t)
                    self.running_tasks.append(t)
                    break

            # Pull every 10 minutes if nothing else to do
            if len(self.running_tasks) == 0 and len(self._task_queue) == 0 and time.monotonic() - last_pull > 60 * 10:
                print("10 minutes elapsed, fetching repos")
                last_pull = time.monotonic()
                self.enqueue(build_pipeline(self))

            # Send email if nothing else to-do and not already done.
            if len(self.running_tasks) == 0 and len(self._task_queue) == 0 and len(self.completed_tasks) > 0 and not isinstance(self.completed_tasks[-1], SendEmail):
                self.enqueue(SendEmail(self))


app = Flask(__name__, static_folder="./static")


@app.route("/")
def index():
    from_main = Queue()
    to_main.put(['html', from_main])
    return Response(from_main.get(), "text/html")


# @app.route("/build/<envs>")
# def build(envs: str):
#     to_main.put(['build', envs.split(',')])
#     return "OK"
#
#
# @app.route("/completed_tasks")
# def completed_tasks():
#     from_main = Queue()
#     to_main.put(['completed_tasks', from_main])
#     return from_main.get()
#
#
# @app.route("/task_queue")
# def task_queue():
#     from_main = Queue()
#     to_main.put(['task_queue', from_main])
#     return from_main.get()
#
#
# @app.route("/current_task")
# def current_task():
#     from_main = Queue()
#     to_main.put(['current_task', from_main])
#     return from_main.get()
#
#
# @app.route("/result/<build_number>/<job_number>")
# def result(build_number, job_number):
#     from_main = Queue()
#     to_main.put(['job_details', build_number, job_number])
#     return from_main.get()

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-w', '--workspace')
    parser.add_argument('-l', '--listen-port', default=5000)
    parser.add_argument('-f', '--force-build', action='store_true', help="Force running the build pipeline once after starting up.")
    args = parser.parse_args()
    ws = Path(args.workspace)

    if not ws.exists() or not ws.is_dir():
        print(f"Workspace {ws} does not exist or is not a directory")
        sys.exit(1)

    to_main = Queue()
    main = Main(to_main, ws, args.force_build)

    app.run(host='::', port=args.listen_port)
