#!/usr/bin/env python3
"""Bounded process/byte transport. Only Shen decides a claim's validity."""
import hashlib
import os
from pathlib import Path
import platform
import selectors
import select
import signal
import struct
import subprocess
import sys
import time

MAX_FRAME = 8192
MAX_DIAGNOSTIC = 4096
OVERLAY_SHA256 = "480e26c610b593b66f87118ea2fbeacaf34201e42f2279a09decfb9481879168"


class ServiceError(Exception):
    """No semantic result is available from this failed transport."""


def validate_reply(reply, request_id):
    if (len(reply) != 4 or reply[:2] != bytes((86, 1))
            or reply[2] != request_id or reply[3] not in (0, 1, 2)):
        raise ServiceError("invalid worker response")
    return reply


def run_worker(command, body, root, timeout=5):
    """Capture one exact response; never salvage output from a failed child."""
    if not body:
        raise ServiceError("missing request identity")
    child = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, start_new_session=True,
                             bufsize=0)
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
        if not complete and child.returncode is None:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
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


def main():
    if len(sys.argv) != 2:
        return 2
    # Resolve configuration in the caller's directory before selecting repo cwd.
    config = Path(sys.argv[1]).resolve()
    root = Path(__file__).resolve().parent.parent
    try:
        body = read_request_timed(sys.stdin.fileno())
        cache = root / ".tools" / ("host-path-" + platform.system() + "-" + platform.machine())
        host = Path(cache.read_text().strip())
        if not host.is_absolute():
            host = root / host
        overlay = root / ".tools/t-star-pr117.shen"
        if hashlib.sha256(overlay.read_bytes()).hexdigest() != OVERLAY_SHA256:
            raise ServiceError("kernel overlay mismatch")
        # Hex is an inert argv byte carrier. No supplied text becomes source.
        command = [str(host), "script", "service/checker.shen", str(config), body.hex()]
        reply, _diagnostics = run_worker(command, body, root)
    except (OSError, ServiceError, ValueError):
        # No partial/forged acceptance and no potentially sensitive payload logs.
        return 2
    sys.stdout.buffer.write(reply)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
