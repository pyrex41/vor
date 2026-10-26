"""Transport and real-worker checks. This file never decides Shen semantics."""
import hashlib
import importlib.util
import os
import platform
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("async_rpc", ROOT / "service/async_rpc.py")
rpc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rpc)


def request(payload=b"\0", request_id="q", nonce=7, source="source", kind=3):
    ids = ("session", "run", request_id, source, "model", "adapter")
    body = b"\x00\x01\x01" + b"".join(struct.pack(">H", len(x)) + x.encode() for x in ids)
    body += struct.pack(">Q", nonce) + hashlib.sha256(payload).digest()
    return body + struct.pack(">HIHH", 64, 256, 32, 16) + bytes((kind,)) + struct.pack(">I", len(payload)) + payload


class WireTests(unittest.TestCase):
    def test_configuration_symlink_is_rejected_before_runtime_start(self):
        with tempfile.TemporaryDirectory() as directory:
            actual = Path(directory) / "actual.shen"
            actual.write_text('(simple-error "must never load")')
            link = Path(directory) / "config.shen"
            link.symlink_to(actual)
            command = [sys.executable, str(ROOT / "service/async_rpc.py"),
                       "--config", str(link), "--source-id", "x",
                       "--config-sha256", rpc.file_identity(actual), "--host-sha256", "x",
                       "--runtime-root", directory, "--runtime-sha256", "x",
                       "--model-id", "model", "--adapter-id", "adapter"]
            result = subprocess.run(command, input=b"", capture_output=True, timeout=3)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, b"")

    def test_exact_echo_and_four_statuses(self):
        body = request()
        ids, nonce, limits, payload, binding, kind = rpc.decode_request(body)
        self.assertEqual(ids, ["session", "run", "q", "source", "model", "adapter"])
        self.assertEqual((nonce, limits, payload), (7, (64, 256, 32, 16), b"\0"))
        for status in (1, 2, 3, 4):
            frame = rpc.encode_reply(binding, status)
            self.assertEqual(struct.unpack(">I", frame[:4])[0], len(frame) - 4)
            self.assertEqual(frame[7:-5], binding)
            self.assertEqual(frame[-5:], bytes([status, 0, 0, 0, 0]))

    def test_invalid_frames(self):
        body = request()
        for malformed in (b"", body[:-1], body+b"x", body[:2]+b"\2"+body[3:], body[:-1]+b"x"):
            with self.subTest(body=malformed[:8]), self.assertRaises(rpc.ProtocolError):
                rpc.decode_request(malformed)
        for cut in range(len(body)):
            with self.assertRaises(rpc.ProtocolError):
                rpc.decode_request(body[:cut])

    def test_zero_nonce_and_payload_identity_mismatch(self):
        with self.assertRaises(rpc.ProtocolError):
            rpc.decode_request(request(nonce=0))
        body = bytearray(request())
        body[-1] ^= 1
        with self.assertRaises(rpc.ProtocolError):
            rpc.decode_request(bytes(body))

    def test_delayed_extra_output_cannot_finish_cleanly(self):
        code = "import os,time;os.write(1,b'VA\\x01\\x00\\x00');os.read(0,1);time.sleep(.05);os.write(1,b'extra')"
        worker = rpc.Worker([sys.executable, "-c", code], ROOT, 1)
        try:
            with self.assertRaises(rpc.ProtocolError):
                worker.finish()
        finally:
            worker.close()

    def test_input_deadline_and_length_bound(self):
        reader, writer = os.pipe()
        try:
            with self.assertRaises(rpc.ProtocolError):
                rpc.read_frame(reader, .05)
            os.write(writer, struct.pack(">I", rpc.MAX_FRAME + 1))
            with self.assertRaises(rpc.ProtocolError):
                rpc.read_frame(reader, .05)
        finally:
            os.close(reader)
            os.close(writer)

    def test_worker_bad_output_and_death(self):
        for code in ("import os;os.write(1,b'x'*4097)", "raise SystemExit(1)", "import time;time.sleep(5)"):
            with self.subTest(code=code), self.assertRaises(rpc.ProtocolError):
                rpc.Worker([sys.executable, "-c", code], ROOT, .2)

    def test_parent_death_kills_worker_group(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "escaped"
            started = Path(directory) / "started"
            worker_code = f"from pathlib import Path;import time;Path({str(started)!r}).touch();time.sleep(.5);Path({str(marker)!r}).touch();time.sleep(3)"
            parent_code = (
                "import os,subprocess,sys,time\n"
                "from pathlib import Path\n"
                "r,w=os.pipe()\n"
                "subprocess.Popen([sys.executable,sys.argv[1],str(os.getpid()),str(w),sys.executable,'-c',sys.argv[2]],pass_fds=(w,),start_new_session=True)\n"
                "os.close(w)\n"
                "deadline=time.monotonic()+5\n"
                "while not Path(sys.argv[3]).exists() and time.monotonic()<deadline: time.sleep(.01)\n"
                "os._exit(0 if Path(sys.argv[3]).exists() else 2)\n"
            )
            parent = subprocess.Popen([sys.executable, "-c", parent_code, str(ROOT / "service/async_guard.py"), worker_code, str(started)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            self.assertEqual(parent.wait(timeout=8), 0, "worker readiness was not established")
            time.sleep(.7)
            self.assertTrue(started.exists())
            self.assertFalse(marker.exists())


class RealCheckerTests(unittest.TestCase):
    def test_finish_returns_the_actual_bounded_checker_result(self):
        spec = importlib.util.spec_from_file_location("report_fixture", ROOT / "tests/test_service.py")
        old = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(old)
        source = rpc.source_identity(ROOT)
        payload = old.enc(old.envelope_value())
        host = Path((ROOT / ".tools" / ("host-path-" + platform.system() + "-" + platform.machine())).read_text().strip())
        if not host.is_absolute(): host = ROOT / host
        config = ROOT / "service/async-config-example.shen"
        bodies = [request(payload, "ordinary", source=source),
                  request(payload, "report", source=source, kind=4),
                  request(b"\0", "invalid-report", source=source, kind=4)]
        command = [sys.executable, str(ROOT / "service/async_rpc.py"), "--config", str(config),
                   "--source-id", source, "--config-sha256", rpc.file_identity(config),
                   "--host-sha256", rpc.file_identity(host), "--runtime-root", str(host.parent.parent),
                   "--runtime-sha256", rpc.runtime_identity(host.parent.parent), "--model-id", "model",
                   "--adapter-id", "adapter", "--timeout", "30"]
        raw = b"".join(struct.pack(">I", len(body)) + body for body in bodies)
        result = subprocess.run(command, input=raw, capture_output=True, cwd=ROOT, timeout=45)
        self.assertEqual(result.returncode, 0, result.stderr)
        frames = []
        offset = 0
        while offset < len(result.stdout):
            size = struct.unpack(">I", result.stdout[offset:offset+4])[0]
            frames.append(result.stdout[offset:offset+size+4]); offset += size+4
        self.assertEqual(len(frames), 3)
        self.assertEqual(frames[0], rpc.encode_reply(rpc.decode_request(bodies[0])[4], 1))
        for frame, status, symbol, body in zip(frames[1:], (1, 2), (b"checked", b"rejected"), bodies[1:]):
            binding = rpc.decode_request(body)[4]
            marker = 4 + 3 + len(binding)
            self.assertEqual(frame[marker], status)
            size = struct.unpack(">I", frame[marker+1:marker+5])[0]
            encoded = frame[marker+5:]
            self.assertGreater(size, 0)
            self.assertEqual(size, len(encoded))
            self.assertLessEqual(size, rpc.MAX_PAYLOAD)
            self.assertEqual(encoded[0], 6)
            self.assertGreaterEqual(struct.unpack(">H", encoded[1:3])[0], 1)
            self.assertTrue(encoded[3:].startswith(b"\x04" + struct.pack(">H", len(symbol)) + symbol))

    def test_producer_payload_never_carries_acceptance(self):
        spec = importlib.util.spec_from_file_location("old_service_producer", ROOT / "tests/test_service.py")
        old = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(old)
        payload = old.enc(old.envelope_value())
        source = rpc.source_identity(ROOT)
        host = Path((ROOT / ".tools" / ("host-path-" + platform.system() + "-" + platform.machine())).read_text().strip())
        if not host.is_absolute(): host = ROOT / host
        config = ROOT / "service/async-config-example.shen"
        bodies = [request(payload, "produce", source=source, kind=1), request(payload, "check", source=source)]
        command = [sys.executable, str(ROOT / "service/async_rpc.py"), "--config", str(config), "--source-id", source,
                   "--config-sha256", rpc.file_identity(config), "--host-sha256", rpc.file_identity(host),
                   "--runtime-root", str(host.parent.parent), "--runtime-sha256", rpc.runtime_identity(host.parent.parent),
                   "--model-id", "model", "--adapter-id", "adapter", "--timeout", "30"]
        raw = b"".join(struct.pack(">I", len(body)) + body for body in bodies)
        result = subprocess.run(command, input=raw, capture_output=True, cwd=ROOT, timeout=40)
        self.assertEqual(result.returncode, 0, result.stderr)
        expected = rpc.encode_reply(rpc.decode_request(bodies[0])[4], 3, payload)
        expected += rpc.encode_reply(rpc.decode_request(bodies[1])[4], 1)
        self.assertEqual(result.stdout, expected)

    def test_fresh_persistent_equivalence_and_duplicate_rejection(self):
        spec = importlib.util.spec_from_file_location("old_service", ROOT / "tests/test_service.py")
        old = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(old)
        payload = old.enc(old.envelope_value())
        source = rpc.source_identity(ROOT)
        host = Path((ROOT / ".tools" / ("host-path-" + platform.system() + "-" + platform.machine())).read_text().strip())
        if not host.is_absolute():
            host = ROOT / host
        config = ROOT / "service/async-config-example.shen"
        requests = [request(payload, "q1", source=source), request(b"\0", "q2", source=source)]
        raw = b"".join(struct.pack(">I", len(body)) + body for body in requests)
        command = [sys.executable, str(ROOT / "service/async_rpc.py"), "--config", str(ROOT / "service/async-config-example.shen"), "--source-id", source, "--config-sha256", rpc.file_identity(config), "--host-sha256", rpc.file_identity(host), "--runtime-root", str(host.parent.parent), "--runtime-sha256", rpc.runtime_identity(host.parent.parent), "--model-id", "model", "--adapter-id", "adapter", "--timeout", "30"]
        replies = []
        for mode in ([], ["--fresh"]):
            result = subprocess.run(command+mode, input=raw, capture_output=True, cwd=ROOT, timeout=70)
            self.assertEqual(result.returncode, 0, result.stderr)
            replies.append(result.stdout)
        self.assertEqual(replies[0], replies[1])
        offset = 0
        statuses = []
        while offset < len(replies[0]):
            size = struct.unpack(">I", replies[0][offset:offset+4])[0]
            statuses.append(replies[0][offset+4+size-5])
            offset += size+4
        self.assertEqual(statuses, [1, 2])
        duplicate = requests[0]
        raw_duplicate = (struct.pack(">I", len(duplicate)) + duplicate)*2
        result = subprocess.run(command, input=raw_duplicate, capture_output=True, cwd=ROOT, timeout=40)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(len(result.stdout), len(rpc.encode_reply(rpc.decode_request(duplicate)[4], 1)))


if __name__ == "__main__":
    unittest.main()
