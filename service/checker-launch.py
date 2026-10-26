#!/usr/bin/env python3
"""Bounded process/byte transport. Only Shen decides a claim's validity."""
import ctypes
import hashlib
import os
from pathlib import Path
import platform
import selectors
import select
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import time

MAX_FRAME = 8192
MAX_DIAGNOSTIC = 4096
DEFAULT_DEADLINE = 10
MAX_DEADLINE = 120
OVERLAY_SHA256 = "480e26c610b593b66f87118ea2fbeacaf34201e42f2279a09decfb9481879168"
ARCHIVE_SHA256 = {
    ("Linux", "x86_64"): "c57f47586894534b9797daf5c0cc65c58dc6fb89d6ea6f0c2b48ac64de66d010",
    ("Linux", "aarch64"): "c57f47586894534b9797daf5c0cc65c58dc6fb89d6ea6f0c2b48ac64de66d010",
    ("Darwin", "arm64"): "1dbbdfd4dbfc64383edf2ee08a788cb410bb3f5104e3b6b32204e443baeb3ff9",
}


class ServiceError(Exception):
    """No semantic result is available from this failed transport."""


def validate_reply(reply, request_id):
    if (len(reply) != 4 or reply[:2] != bytes((86, 1))
            or reply[2] != request_id or reply[3] not in (0, 1, 2)):
        raise ServiceError("invalid worker response")
    return reply


class Interrupted(ServiceError):
    """The launcher was asked to stop; the worker group is still reaped."""


def interrupt(signum, _frame):
    raise Interrupted("launcher signal %d" % signum)


def install_signal_handlers():
    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, interrupt)


def die_with_parent(parent):
    """Best-effort Linux parent-death signal; the group kill remains primary."""
    def setup():
        if platform.system() != "Linux":
            return
        try:
            libc = ctypes.CDLL(None, use_errno=True)
            libc.prctl(1, signal.SIGKILL, 0, 0, 0)  # PR_SET_PDEATHSIG
        except (OSError, AttributeError):
            return
        if os.getppid() != parent:
            os._exit(1)
    return setup


def stage_file(source, target, expected):
    """Hash the exact bytes written to a private copy; the copy is what runs."""
    data = Path(source).read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise ServiceError("host identity mismatch")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)


def stage_host(root, stage, system=None, machine=None):
    """Stage the bootstrap-recorded host files and the pinned overlay."""
    key = (system or platform.system(), machine or platform.machine())
    archive = ARCHIVE_SHA256.get(key)
    suffix = key[0] + "-" + key[1]
    host = Path((root / ".tools" / ("host-path-" + suffix)).read_text().strip())
    if not host.is_absolute():
        host = root / host
    tools_root = (root / ".tools").resolve()
    host = host.resolve()
    host_root = host.parent.parent
    if not host.is_relative_to(tools_root):
        raise ServiceError("host path escapes trusted tools")
    lines = (root / ".tools" / ("host-identity-" + suffix)).read_text().splitlines()
    if archive is None or not lines or lines[0] != "archive " + archive:
        raise ServiceError("host identity mismatch")
    staged = set()
    for line in lines[1:]:
        digest, _, name = line.partition(" ")
        parts = Path(name).parts
        if (not parts or parts[0] not in ("bin", "lib") or ".." in parts
                or Path(name).is_absolute()):
            raise ServiceError("host identity mismatch")
        source = (host_root / name).resolve()
        if not source.is_relative_to(tools_root):
            raise ServiceError("host identity path escapes trusted tools")
        stage_file(source, stage / "host" / name, digest)
        staged.add(name)
    if "bin/shen-scheme" not in staged:
        raise ServiceError("host identity mismatch")
    binary = stage / "host" / "bin" / "shen-scheme"
    binary.chmod(0o700)
    overlay = stage / "t-star-pr117.shen"
    stage_file(root / ".tools" / "t-star-pr117.shen", overlay, OVERLAY_SHA256)
    return binary, overlay


def kill_group(pid):
    try:
        os.killpg(pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def run_worker(command, body, root, timeout=DEFAULT_DEADLINE):
    """Capture one exact response; never salvage output from a failed child."""
    if not body:
        raise ServiceError("missing request identity")
    child = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, start_new_session=True,
                             bufsize=0, preexec_fn=die_with_parent(os.getpid()))
    selector = selectors.DefaultSelector()
    buffers = {"out": bytearray(), "err": bytearray()}
    deadline = time.monotonic() + timeout
    complete = False
    try:
        for stream, name in ((child.stdout, "out"), (child.stderr, "err")):
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, name)
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise ServiceError("worker timeout")
            for key, _ in selector.select(remaining):
                try:
                    chunk = os.read(key.fd, MAX_DIAGNOSTIC + 1)
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                buffers[key.data].extend(chunk)
                limit = 4 if key.data == "out" else MAX_DIAGNOSTIC
                if len(buffers[key.data]) > limit:
                    raise ServiceError("worker output limit")
        try:
            status = child.wait(timeout=max(0, deadline - time.monotonic()))
        except subprocess.TimeoutExpired as error:
            raise ServiceError("worker exit timeout") from error
        if status != 0:
            raise ServiceError("worker failed")
        reply = validate_reply(bytes(buffers["out"]), body[0])
        complete = True
        return reply, bytes(buffers["err"])
    finally:
        selector.close()
        # The worker owns the fresh process group.  The leader can have exited
        # (and been reaped) while descendants still hold neither pipe open;
        # cleanup terminates them after success as well as failure.
        kill_group(child.pid)
        if not complete:
            try:
                child.wait(timeout=1)
            except subprocess.TimeoutExpired:
                # Preserve failure: a kill request is not a successful reap.
                raise ServiceError("worker cleanup incomplete")
        for stream in (child.stdout, child.stderr):
            if stream is not None and not stream.closed:
                stream.close()


def read_exact(stream, size):
    data = bytearray()
    while len(data) < size:
        chunk = stream.read(size - len(data))
        if not chunk:
            raise ServiceError("truncated frame")
        data.extend(chunk)
    return bytes(data)


def read_request(stream):
    size = struct.unpack(">I", read_exact(stream, 4))[0]
    if not 1 <= size <= MAX_FRAME:
        raise ServiceError("invalid frame size")
    body = read_exact(stream, size)
    if stream.read(1):
        raise ServiceError("trailing frame data")
    return body


def read_request_timed(fd, timeout=5):
    """One deadline covers header, body, and the mandatory EOF."""
    deadline = time.monotonic() + timeout

    class DeadlineReader:
        def read(self, size):
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise ServiceError("input timeout")
                try:
                    ready, _, _ = select.select([fd], [], [], remaining)
                    if not ready:
                        raise ServiceError("input timeout")
                    return os.read(fd, size)
                except InterruptedError:
                    continue

    return read_request(DeadlineReader())


def parse_arguments(argv):
    """[--deadline SECONDS] CONFIG; the deadline is supervisor policy."""
    deadline = DEFAULT_DEADLINE
    if len(argv) == 3 and argv[0] == "--deadline":
        if not argv[1].isdigit() or not 1 <= int(argv[1]) <= MAX_DEADLINE:
            raise ValueError("invalid deadline")
        deadline, argv = int(argv[1]), argv[2:]
    if len(argv) != 1:
        raise ValueError("usage")
    return deadline, argv[0]


def main():
    install_signal_handlers()
    try:
        deadline, config = parse_arguments(sys.argv[1:])
    except ValueError:
        return 2
    # Resolve configuration in the caller's directory before selecting repo cwd.
    config = Path(config).resolve()
    root = Path(__file__).resolve().parent.parent
    stage = None
    try:
        body = read_request_timed(sys.stdin.fileno())
        stage = Path(tempfile.mkdtemp(prefix="vor-service-"))
        host, overlay = stage_host(root, stage)
        # Hex is an inert argv byte carrier. No supplied text becomes source.
        command = [str(host), "script", "service/checker.shen", str(overlay),
                   str(config), body.hex()]
        reply, _diagnostics = run_worker(command, body, root, deadline)
    except (OSError, ServiceError, ValueError):
        # No partial/forged acceptance and no potentially sensitive payload logs.
        return 2
    finally:
        if stage is not None:
            shutil.rmtree(stage, ignore_errors=True)
    sys.stdout.buffer.write(reply)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
