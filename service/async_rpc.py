#!/usr/bin/env python3
"""async-wire/1 transport. Only the unchanged trusted Shen checker decides claims."""
import argparse
import hashlib
import os
from pathlib import Path
import platform
import select
import selectors
import signal
import struct
import subprocess
import sys
import time

MAX_FRAME = 1048576
MAX_PAYLOAD = 262144
MAX_DIAGNOSTIC = 4096
OVERLAY_SHA256 = "480e26c610b593b66f87118ea2fbeacaf34201e42f2279a09decfb9481879168"


class ProtocolError(Exception):
    """A transport failure supplies no semantic result."""


def decode_request(body):
    """Decode canonical opaque payload; no symbols are interned or evaluated."""
    pos = 0

    def take(n):
        nonlocal pos
        if pos + n > len(body):
            raise ProtocolError("truncated field")
        value = body[pos:pos+n]
        pos += n
        return value

    if take(3) != b"\x00\x01\x01":
        raise ProtocolError("version or direction")
    ids = []
    for _ in range(6):
        size = struct.unpack(">H", take(2))[0]
        if not 1 <= size <= 256:
            raise ProtocolError("identity length")
        raw = take(size)
        if any(x < 32 or x > 126 for x in raw):
            raise ProtocolError("identity alphabet")
        ids.append(raw.decode("ascii"))
    nonce = struct.unpack(">Q", take(8))[0]
    if nonce == 0:
        raise ProtocolError("zero nonce")
    request_hash = take(32)
    limits = struct.unpack(">HIHH", take(10))
    if not all(1 <= value <= bound for value, bound in zip(limits, (64, 256, 32, 16))):
        raise ProtocolError("resource limits")
    kind = take(1)[0]
    if kind not in (1, 3):
        raise ProtocolError("checker accepts produce/observe requests only")
    size = struct.unpack(">I", take(4))[0]
    if not 1 <= size <= MAX_PAYLOAD:
        raise ProtocolError("payload length")
    payload = take(size)
    if pos != len(body) or hashlib.sha256(payload).digest() != request_hash:
        raise ProtocolError("payload binding")
    # The reply echoes this exact canonical binding, not a reconstructed subset.
    binding_end = pos - size - 5
    return ids, nonce, limits, payload, body[3:binding_end], kind


def encode_reply(binding, status, payload=b""):
    if status not in (1, 2, 3, 4):
        raise ProtocolError("checker status")
    if len(payload) > MAX_PAYLOAD:
        raise ProtocolError("reply payload budget")
    body = b"\x00\x01\x02" + binding + bytes((status,)) + struct.pack(">I", len(payload)) + payload
    return struct.pack(">I", len(body)) + body


def read_exact(fd, size, deadline, allow_eof=False):
    data = bytearray()
    while len(data) < size:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise ProtocolError("input deadline")
        ready, _, _ = select.select([fd], [], [], remaining)
        if not ready:
            raise ProtocolError("input deadline")
        chunk = os.read(fd, size - len(data))
        if not chunk:
            if allow_eof and not data:
                return None
            raise ProtocolError("truncated frame")
        data.extend(chunk)
    return bytes(data)


def read_frame(fd, timeout):
    deadline = time.monotonic() + timeout
    header = read_exact(fd, 4, deadline, allow_eof=True)
    if header is None:
        return None
    size = struct.unpack(">I", header)[0]
    if not 1 <= size <= MAX_FRAME:
        raise ProtocolError("frame length")
    return read_exact(fd, size, deadline)


class Worker:
    """One owned long-lived Shen process; per-history state is a function input."""
    def __init__(self, command, root, timeout):
        status_read, status_write = os.pipe()
        try:
            self.child = subprocess.Popen(
                [sys.executable, str(Path(root) / "service/async_guard.py"), str(os.getpid()), str(status_write), *command],
                cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                pass_fds=(status_write,), start_new_session=True, bufsize=0)
        except BaseException:
            os.close(status_read)
            raise
        finally:
            os.close(status_write)
        self.status_fd = status_read
        os.set_blocking(status_read, False)
        self.closed = False
        self.diagnostics = 0
        self.timeout = timeout
        self.seq = 0
        for stream in (self.child.stdin, self.child.stdout, self.child.stderr):
            os.set_blocking(stream.fileno(), False)
        try:
            if self.exchange(b"", 0, startup=True) != b"VA\x01\x00\x00":
                raise ProtocolError("checker startup")
        except BaseException:
            self.close()
            raise

    def exchange(self, packet, seq, startup=False):
        deadline = time.monotonic() + self.timeout
        out = bytearray()
        offset = 0
        expected = 5 if startup else 9
        with selectors.DefaultSelector() as selector:
            selector.register(self.child.stdout, selectors.EVENT_READ, "out")
            selector.register(self.child.stderr, selectors.EVENT_READ, "err")
            selector.register(self.status_fd, selectors.EVENT_READ, "status")
            if packet:
                selector.register(self.child.stdin, selectors.EVENT_WRITE, "in")
            while len(out) < expected or offset < len(packet):
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise ProtocolError("checker deadline")
                for key, _ in selector.select(min(remaining, .1)):
                    if key.data == "status":
                        raise ProtocolError("checker exited before transcript completion")
                    if key.data == "in":
                        try:
                            offset += os.write(key.fd, packet[offset:offset+65536])
                        except BlockingIOError:
                            continue
                        if offset == len(packet):
                            selector.unregister(key.fileobj)
                    else:
                        try:
                            data = os.read(key.fd, MAX_DIAGNOSTIC + 1)
                        except BlockingIOError:
                            continue
                        if not data:
                            raise ProtocolError("checker closed pipe")
                        if key.data == "err":
                            self.diagnostics += len(data)
                            if self.diagnostics > MAX_DIAGNOSTIC:
                                raise ProtocolError("checker diagnostics budget")
                        else:
                            out.extend(data)
                            if not startup and len(out) >= 9:
                                size = struct.unpack(">I", out[5:9])[0]
                                if size > MAX_PAYLOAD:
                                    raise ProtocolError("checker output budget")
                                expected = 9 + size
                            if len(out) > expected:
                                raise ProtocolError("checker output budget")
            if out[:3] != b"VA\x01" or out[4] != seq:
                raise ProtocolError("checker reply binding")
            return bytes(out)

    def check(self, payload, kind=3):
        if self.seq >= 256:
            raise ProtocolError("request budget")
        request = bytes((kind,)) + payload
        reply = self.exchange(struct.pack(">I", len(request)) + request, self.seq)
        if reply[3] not in (1, 2, 3, 4):
            raise ProtocolError("checker result")
        self.seq += 1
        return reply[3], reply[9:]

    def finish(self):
        """Require worker EOF and a zero actual-worker exit before using evidence."""
        self.child.stdin.close()
        deadline = time.monotonic() + self.timeout
        exit_packet = bytearray()
        with selectors.DefaultSelector() as selector:
            for stream, kind in ((self.child.stdout, "out"), (self.child.stderr, "err"), (self.status_fd, "status")):
                selector.register(stream, selectors.EVENT_READ, kind)
            while selector.get_map():
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise ProtocolError("checker EOF deadline")
                for key, _ in selector.select(min(remaining, .1)):
                    try:
                        chunk = os.read(key.fd, MAX_DIAGNOSTIC + 1)
                    except BlockingIOError:
                        continue
                    if not chunk:
                        selector.unregister(key.fileobj)
                    elif key.data == "out":
                        raise ProtocolError("trailing checker output")
                    elif key.data == "status":
                        exit_packet.extend(chunk)
                        if len(exit_packet) > 4:
                            raise ProtocolError("invalid checker exit packet")
                    else:
                        self.diagnostics += len(chunk)
                        if self.diagnostics > MAX_DIAGNOSTIC:
                            raise ProtocolError("checker diagnostics budget")
        if len(exit_packet) != 4 or struct.unpack(">i", exit_packet)[0] != 0:
            raise ProtocolError("checker failed on completion")

    def close(self):
        if self.closed:
            return
        self.closed = True
        failure = None
        try:
            # The guardian has never been reaped and deliberately stays alive,
            # so this group identity cannot refer to an unrelated reused PID.
            try:
                os.killpg(self.child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except OSError as error:
                failure = error
                try:
                    self.child.kill()
                except OSError:
                    pass
            try:
                self.child.wait(timeout=2)
            except subprocess.TimeoutExpired as error:
                failure = error
        finally:
            for stream in (self.child.stdin, self.child.stdout, self.child.stderr):
                stream.close()
            os.close(self.status_fd)
        if failure is not None:
            raise ProtocolError("checker cleanup incomplete") from failure


def source_identity(root):
    """Measure the operator-selected tracked image; artifact bytes never choose it."""
    paths = subprocess.check_output(["git", "ls-files", "-z"], cwd=root, timeout=10).split(b"\0")
    digest = hashlib.sha256()
    for raw in sorted(path for path in paths if path):
        path = Path(root) / os.fsdecode(raw)
        if path.is_symlink():
            raise ProtocolError("source image contains a symlink")
        size = path.stat().st_size
        if size > 16 * 1024 * 1024:
            raise ProtocolError("source file budget")
        data = path.read_bytes()
        digest.update(struct.pack(">I", len(raw)) + raw + struct.pack(">Q", len(data)))
        digest.update(hashlib.sha256(data).digest())
    return digest.hexdigest()


def file_identity(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def runtime_identity(directory):
    """Bind executable and boot bundle, without following external symlinks."""
    directory = Path(directory).resolve(strict=True)
    digest = hashlib.sha256()
    paths = sorted(directory.rglob("*"))
    if len(paths) > 4096:
        raise ProtocolError("runtime file count")
    total = 0
    for path in paths:
        if path.is_symlink():
            raise ProtocolError("runtime symlink")
        if path.is_file():
            size = path.stat().st_size
            total += size
            if size > 64 * 1024 * 1024 or total > 256 * 1024 * 1024:
                raise ProtocolError("runtime size")
            name = path.relative_to(directory).as_posix().encode("utf-8")
            digest.update(struct.pack(">I", len(name)) + name + struct.pack(">Q", size))
            digest.update(bytes.fromhex(file_identity(path)))
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--source-id", required=True)
    parser.add_argument("--config-sha256", required=True)
    parser.add_argument("--host-sha256", required=True)
    parser.add_argument("--runtime-root", required=True, type=Path)
    parser.add_argument("--runtime-sha256", required=True)
    parser.add_argument("--model-id", required=True)
    parser.add_argument("--adapter-id", required=True)
    parser.add_argument("--fresh", action="store_true")
    parser.add_argument("--timeout", type=float, default=5)
    args = parser.parse_args()
    if not .1 <= args.timeout <= 30:
        parser.error("timeout must be .1..30 seconds")
    root = Path(__file__).resolve().parent.parent
    worker = None
    try:
        if args.config.is_symlink() or not args.config.is_file():
            raise ProtocolError("configuration must be a regular file")
        config = args.config.resolve(strict=True)
        if hashlib.sha256((root / ".tools/t-star-pr117.shen").read_bytes()).hexdigest() != OVERLAY_SHA256:
            raise ProtocolError("kernel overlay")
        host = Path((root / ".tools" / ("host-path-" + platform.system() + "-" + platform.machine())).read_text().strip())
        if not host.is_absolute():
            host = root / host
        if (file_identity(config) != args.config_sha256
                or file_identity(host) != args.host_sha256
                or source_identity(root) != args.source_id
                or runtime_identity(args.runtime_root) != args.runtime_sha256
                or not host.resolve().is_relative_to(args.runtime_root.resolve())):
            raise ProtocolError("trusted image measurement mismatch")
        command = [str(host), "script", "service/async-checker.shen", str(config)]
        session = None
        seen = set()
        for _ in range(256):
            body = read_frame(sys.stdin.fileno(), args.timeout)
            if body is None:
                if worker is not None:
                    worker.finish()
                    worker.close()
                    worker = None
                return 0
            ids, nonce, limits, payload, binding, kind = decode_request(body)
            if ids[3:] != [args.source_id, args.model_id, args.adapter_id]:
                raise ProtocolError("trusted policy identity")
            stable = (ids[0], ids[1], nonce, limits)
            if session is None:
                session = stable
            if session != stable or ids[2] in seen:
                raise ProtocolError("stale or duplicate request")
            seen.add(ids[2])
            if worker is None:
                worker = Worker(command, root, args.timeout)
            status, result_payload = worker.check(payload, kind)
            if args.fresh:
                worker.finish()
                worker.close()
                worker = None
            reply = encode_reply(binding, status, result_payload)
            # Bound a client that stops reading replies as well as input stalls.
            deadline = time.monotonic() + args.timeout
            offset = 0
            os.set_blocking(sys.stdout.fileno(), False)
            while offset < len(reply):
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([], [sys.stdout.fileno()], [], max(0, remaining))[1]:
                    raise ProtocolError("reply deadline")
                try:
                    offset += os.write(sys.stdout.fileno(), reply[offset:])
                except BlockingIOError:
                    continue
        # At the exact request budget EOF is required; extra requests are errors.
        if read_frame(sys.stdin.fileno(), args.timeout) is not None:
            raise ProtocolError("request budget")
        if worker is not None:
            worker.finish()
            worker.close()
            worker = None
        return 0
    except (ProtocolError, OSError, ValueError, BrokenPipeError):
        return 2
    finally:
        if worker is not None:
            worker.close()


if __name__ == "__main__":
    sys.exit(main())
