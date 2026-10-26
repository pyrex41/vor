#!/usr/bin/env python3
"""Independent transport corpus; it never decides VOR semantic validity."""
import copy, hashlib, importlib.util, io, os, platform, shutil, signal, struct, subprocess, sys, tempfile, threading, time, unittest
from pathlib import Path

ROOT = os.path.dirname(os.path.dirname(__file__))
SHIM = os.path.join(ROOT, "service", "checker-launch.py")
CFG = os.path.join(ROOT, "service", "config-example.shen")

def sym(s): return ("s", s)
def enc(x):
    if x == []: return b"\0"
    if x is False: return b"\1"
    if x is True: return b"\2"
    if isinstance(x, int): return b"\3" + struct.pack(">H", x)
    if isinstance(x, tuple) and x[0] == "s":
        b = x[1].encode("ascii"); return b"\4" + struct.pack(">H", len(b)) + b
    if isinstance(x, str):
        b = x.encode("ascii"); return b"\5" + struct.pack(">H", len(b)) + b
    if isinstance(x, list):
        return b"\6" + struct.pack(">H", len(x)) + b"".join(enc(v) for v in x)
    raise TypeError(x)

def run(body, timeout=30):
    p = subprocess.run([SHIM, CFG], input=struct.pack(">I", len(body)) + body,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=timeout)
    return p.returncode, p.stdout, p.stderr

def envelope_value():
    model = [sym("vor-model"), 0, [sym("alice"), sym("bob")], [[False, False]], [
      [sym("rule"), sym("alice-enter"), [sym("neg"), [sym("var"), sym("bob")]], [[sym("alice"), [sym("lit"), True]]]],
      [sym("rule"), sym("alice-leave"), [sym("lit"), True], [[sym("alice"), [sym("lit"), False]]]],
      [sym("rule"), sym("bob-enter"), [sym("neg"), [sym("var"), sym("alice")]], [[sym("bob"), [sym("lit"), True]]]],
      [sym("rule"), sym("bob-leave"), [sym("lit"), True], [[sym("bob"), [sym("lit"), False]]]],
    ], [sym("neg"), [sym("conj"), [sym("var"), sym("alice")], [sym("var"), sym("bob")]]]]
    root = [sym("vor-root"), 0, "reviewed-vor/0", "shen-scheme-43.1-pr117"]
    claim = [sym("vor-claim"), 0, root, [sym("model"), model], [],
             [[sym("runtime"), sym("unchanged-trusted-image")]], sym("boolean-states"), [sym("invariant")], sym("finite-proof")]
    cert = [sym("vor-certificate"), 0, model, [[False, False], [True, False], [False, True]]]
    return [sym("vor-evidence"), 0, claim, cert]


def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


def pid_state(pid):
    out = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], stdout=subprocess.PIPE,
                         text=True).stdout.strip()
    return out[:1]


def group_states(pgid):
    """Process states for a group, from ps; empty when nothing is listed."""
    out = subprocess.run(["ps", "-eo", "pgid=,stat="], stdout=subprocess.PIPE,
                         text=True).stdout
    return [stat[0] for line in out.splitlines()
            for group, stat in [line.split()] if int(group) == pgid]


SPEC = importlib.util.spec_from_file_location("vor_checker_launch", SHIM)
launcher = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(launcher)


class TransportTests(unittest.TestCase):
    def worker(self, code, timeout=1):
        return launcher.run_worker([sys.executable, "-c", code], bytes([17]), ROOT, timeout)

    def test_input_deadline_includes_header_body_and_eof(self):
        for prefix in (b"", b"\0\0", struct.pack(">I", 2) + b"x",
                       struct.pack(">I", 1) + b"x"):
            with self.subTest(prefix=prefix):
                reader, writer = os.pipe()
                try:
                    os.write(writer, prefix)
                    start = time.monotonic()
                    with self.assertRaises(launcher.ServiceError):
                        launcher.read_request_timed(reader, .1)
                    self.assertLess(time.monotonic() - start, 2)
                finally:
                    os.close(reader)
                    os.close(writer)

    def test_fragmented_request_and_reply(self):
        reader, writer = os.pipe()
        body = bytes([17, 0])
        raw = struct.pack(">I", len(body)) + body

        def send():
            try:
                for byte in raw:
                    os.write(writer, bytes([byte]))
                    time.sleep(.01)
            finally:
                os.close(writer)

        sender = threading.Thread(target=send)
        sender.start()
        try:
            self.assertEqual(launcher.read_request_timed(reader, 1), body)
        finally:
            sender.join(timeout=1)
            os.close(reader)
        self.assertFalse(sender.is_alive())
        code = "import os,time; [(os.write(1,bytes([b])),time.sleep(.01)) for b in [86,1,17,0]]"
        self.assertEqual(self.worker(code)[0], bytes([86, 1, 17, 0]))

    def test_exact_reply(self):
        self.assertEqual(self.worker("import os; os.write(1, bytes([86,1,17,0]))")[0], bytes([86,1,17,0]))

    def test_bad_workers_never_produce_a_result(self):
        programs = {
            "prefix": "import os; os.write(1,b'x'+bytes([86,1,17,0]))",
            "suffix": "import os; os.write(1,bytes([86,1,17,0])+b'x')",
            "failure": "import os; os.write(1,bytes([86,1,17,0])); os._exit(1)",
            "signal": "import os,signal; os.kill(os.getpid(),signal.SIGTERM)",
            "wrong-id": "import os; os.write(1,bytes([86,1,18,0]))",
            "unknown-status": "import os; os.write(1,bytes([86,1,17,3]))",
            "wrong-version": "import os; os.write(1,bytes([86,2,17,0]))",
            "partial": "import os; os.write(1,b'V')",
            "stdout-flood": "import os; os.write(1,b'x'*65536)",
            "stderr-flood": "import os; os.write(2,b'x'*65536)",
        }
        for name, code in programs.items():
            with self.subTest(name=name), self.assertRaises(launcher.ServiceError):
                self.worker(code)

    def test_partial_write_cannot_bypass_deadline(self):
        start = time.monotonic()
        with self.assertRaises(launcher.ServiceError):
            self.worker("import os,time; os.write(1,b'V'); time.sleep(10)", .2)
        self.assertLess(time.monotonic()-start, 2)

    def test_closed_pipes_cannot_bypass_exit_deadline(self):
        start = time.monotonic()
        with self.assertRaises(launcher.ServiceError):
            self.worker("import os,time; os.close(1); os.close(2); time.sleep(10)", .2)
        self.assertLess(time.monotonic()-start, 2)

    def test_failed_reaped_leader_does_not_leak_process_group(self):
        with tempfile.TemporaryDirectory() as directory:
            pid_path = Path(directory) / "descendant.pid"
            marker_path = Path(directory) / "descendant.alive"
            code = (
                "import os,time\n"
                "pid=os.fork()\n"
                "if pid: os._exit(1)\n"
                "with open(%r, 'w') as f: f.write(str(os.getpid()))\n"
                "os.close(1); os.close(2)\n"
                "time.sleep(.6)\n"
                "open(%r, 'w').close()\n"
            ) % (str(pid_path), str(marker_path))
            with self.assertRaises(launcher.ServiceError):
                self.worker(code, 2)
            deadline = time.monotonic() + 1
            while time.monotonic() < deadline and not pid_path.exists():
                time.sleep(.01)
            self.assertTrue(pid_path.exists())
            time.sleep(.8)
            self.assertFalse(marker_path.exists())
            if pid_path.exists():
                try:
                    os.kill(int(pid_path.read_text()), signal.SIGKILL)
                except (OSError, ValueError):
                    pass

    def wait_for(self, path, seconds=2):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline and not path.exists():
            time.sleep(.01)
        self.assertTrue(path.exists())
        return int(path.read_text())

    def assert_group_gone(self, pgid, seconds=2):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            try:
                os.killpg(pgid, 0)
            except ProcessLookupError:
                return
            # Killed members can linger as zombies until their reaper runs.
            if all(state == "Z" for state in group_states(pgid)):
                return
            time.sleep(.02)
        self.fail("worker process group %d survived" % pgid)

    def assert_pid_gone(self, pid, seconds=2):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            if not alive(pid) or pid_state(pid) == "Z":
                return
            time.sleep(.02)
        self.fail("worker descendant %d survived" % pid)

    def test_successful_reply_still_reaps_process_group(self):
        with tempfile.TemporaryDirectory() as directory:
            pid_path = Path(directory) / "descendant.pid"
            code = (
                "import os,time\n"
                "if os.fork() == 0:\n"
                "    os.close(1); os.close(2)\n"
                "    open(%r,'w').write(str(os.getpid()))\n"
                "    time.sleep(30)\n"
                "    os._exit(0)\n"
                "while not os.path.exists(%r): time.sleep(.01)\n"
                "os.write(1, bytes([86,1,17,0]))\n"
            ) % (str(pid_path), str(pid_path))
            self.assertEqual(self.worker(code, 5)[0], bytes([86, 1, 17, 0]))
            self.assert_pid_gone(self.wait_for(pid_path))

    def launcher_process(self, directory, code):
        """A launcher-shaped parent: real handlers, real run_worker."""
        parent = (
            "import importlib.util,sys\n"
            "spec=importlib.util.spec_from_file_location('l',%r)\n"
            "l=importlib.util.module_from_spec(spec); spec.loader.exec_module(l)\n"
            "l.install_signal_handlers()\n"
            "try: l.run_worker([sys.executable,'-c',%r],bytes([17]),%r,30)\n"
            "except l.ServiceError: sys.exit(2)\n"
        ) % (SHIM, code, ROOT)
        return subprocess.Popen([sys.executable, "-c", parent], cwd=directory)

    def test_signal_to_launcher_reaps_worker_group(self):
        code = ("import os,time\n"
                "open('leader.pid','w').write(str(os.getpid()))\n"
                "if os.fork() == 0: time.sleep(30)\n"
                "time.sleep(30)\n")
        for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            with self.subTest(signal=signum), tempfile.TemporaryDirectory() as directory:
                # run_worker uses ROOT as cwd; the worker writes there.
                pid_path = Path(ROOT) / "leader.pid"
                self.addCleanup(lambda: pid_path.exists() and pid_path.unlink())
                parent = self.launcher_process(directory, code)
                leader = self.wait_for(pid_path)
                pid_path.unlink()
                parent.send_signal(signum)
                self.assertEqual(parent.wait(timeout=5), 2)
                self.assert_group_gone(leader)

    @unittest.skipUnless(platform.system() == "Linux", "PR_SET_PDEATHSIG is Linux-only")
    def test_killed_launcher_takes_worker_leader(self):
        code = ("import os,time\n"
                "open('leader.pid','w').write(str(os.getpid()))\n"
                "time.sleep(30)\n")
        with tempfile.TemporaryDirectory() as directory:
            pid_path = Path(ROOT) / "leader.pid"
            self.addCleanup(lambda: pid_path.exists() and pid_path.unlink())
            parent = self.launcher_process(directory, code)
            leader = self.wait_for(pid_path)
            pid_path.unlink()
            parent.kill()
            parent.wait(timeout=5)
            self.assert_group_gone(leader)

    def test_transport_truncation_trailing_and_bounds(self):
        good = bytes([17])+enc(envelope_value())
        for raw in [b"", b"\0", struct.pack(">I", 0), struct.pack(">I",8193),
                    struct.pack(">I",len(good)+1)+good,
                    struct.pack(">I",len(good))+good+b"x"]:
            with self.subTest(raw=raw[:5]), self.assertRaises(launcher.ServiceError):
                launcher.read_request(io.BytesIO(raw))
        self.assertEqual(launcher.read_request(io.BytesIO(struct.pack(">I",len(good))+good)),good)


class StagingTests(unittest.TestCase):
    """Launch runs private copies whose bytes were hashed; never repo paths."""
    def fake_root(self, directory, identity=None):
        root = Path(directory)
        tools = root / ".tools"
        (tools / "h/bin").mkdir(parents=True)
        (tools / "h/lib/x").mkdir(parents=True)
        files = {"bin/shen-scheme": b"host", "lib/x/boot": b"boot"}
        for name, data in files.items():
            (tools / "h" / name).write_bytes(data)
        shutil.copyfile(os.path.join(ROOT, ".tools", "t-star-pr117.shen"), tools / "t-star-pr117.shen")
        (tools / "host-path-Linux-x86_64").write_text(".tools/h/bin/shen-scheme\n")
        if identity is None:
            identity = ["archive " + launcher.ARCHIVE_SHA256[("Linux", "x86_64")]] + [
                hashlib.sha256(data).hexdigest() + " " + name for name, data in sorted(files.items())]
        (tools / "host-identity-Linux-x86_64").write_text("\n".join(identity) + "\n")
        return root

    def stage(self, root):
        stage = Path(tempfile.mkdtemp(prefix="vor-stage-test-"))
        self.addCleanup(shutil.rmtree, stage, True)
        return launcher.stage_host(root, stage, "Linux", "x86_64"), stage

    def test_recorded_identity_is_staged(self):
        with tempfile.TemporaryDirectory() as directory:
            (host, overlay), stage = self.stage(self.fake_root(directory))
            self.assertEqual(host.read_bytes(), b"host")
            self.assertEqual((stage / "host/lib/x/boot").read_bytes(), b"boot")
            self.assertEqual(hashlib.sha256(overlay.read_bytes()).hexdigest(), launcher.OVERLAY_SHA256)

    def test_changed_host_files_are_refused(self):
        for name in ("h/bin/shen-scheme", "h/lib/x/boot", "t-star-pr117.shen"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = self.fake_root(directory)
                with open(root / ".tools" / name, "ab") as stream:
                    stream.write(b" ")
                with self.assertRaises(launcher.ServiceError):
                    self.stage(root)

    def test_foreign_or_incomplete_identity_is_refused(self):
        digest = hashlib.sha256(b"host").hexdigest()
        archive = "archive " + launcher.ARCHIVE_SHA256[("Linux", "x86_64")]
        for identity in (["archive " + "0" * 64, digest + " bin/shen-scheme"],
                         [digest + " bin/shen-scheme"],
                         [archive],
                         [archive, digest + " bin/../bin/shen-scheme"],
                         [archive, digest + " /bin/shen-scheme"],
                         [archive, digest + " etc/shen-scheme"]):
            with self.subTest(identity=identity), tempfile.TemporaryDirectory() as directory:
                with self.assertRaises((launcher.ServiceError, OSError)):
                    self.stage(self.fake_root(directory, identity))

    def test_foreign_host_and_boot_symlink_are_refused(self):
        for mode in ("host", "boot"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as directory:
                base = Path(directory)
                root = self.fake_root(base / "repo")
                foreign = base / "foreign"
                (foreign / "bin").mkdir(parents=True)
                (foreign / "bin/shen-scheme").write_bytes(b"host")
                (foreign / "boot").write_bytes(b"boot")
                if mode == "host":
                    (root / ".tools/host-path-Linux-x86_64").write_text(str(foreign / "bin/shen-scheme"))
                else:
                    boot = root / ".tools/h/lib/x/boot"
                    boot.unlink()
                    boot.symlink_to(foreign / "boot")
                with self.assertRaises(launcher.ServiceError):
                    self.stage(root)

    def test_deadline_is_bounded_supervisor_policy(self):
        self.assertEqual(launcher.parse_arguments(["c"]), (launcher.DEFAULT_DEADLINE, "c"))
        self.assertEqual(launcher.parse_arguments(["--deadline", "30", "c"]), (30, "c"))
        for argv in ([], ["--deadline", "0", "c"], ["--deadline", "121", "c"],
                     ["--deadline", "1.5", "c"], ["--deadline", "c"], ["a", "b"]):
            with self.subTest(argv=argv), self.assertRaises(ValueError):
                launcher.parse_arguments(argv)


class SemanticProcessTests(unittest.TestCase):
    def run_case(self, value, status, config=CFG, cwd=ROOT):
        raw = struct.pack(">I",len(value)+1)+bytes([17])+value
        result = subprocess.run([SHIM,config],input=raw,stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,cwd=cwd,timeout=60)
        self.assertEqual((result.returncode,result.stdout,result.stderr),
                         (0,bytes([86,1,17,status]),b""))

    def config_variant(self, replacements):
        text = Path(CFG).read_text()
        for old,new in replacements:
            self.assertIn(old,text)
            text=text.replace(old,new)
        directory=tempfile.TemporaryDirectory(prefix="vor-service-config-")
        self.addCleanup(directory.cleanup)
        path=Path(directory.name)/"trusted.shen"
        path.write_text(text)
        return str(path)

    def test_healthy_from_unrelated_cwd(self):
        with tempfile.TemporaryDirectory() as cwd:
            self.run_case(enc(envelope_value()),0,cwd=cwd)

    def test_wrong_root_claim_and_forged_evidence(self):
        value=envelope_value()
        value[2][2][2]="another-reviewed-root"
        self.run_case(enc(value),1)
        value=envelope_value()
        value[2][4]=[[sym("runtime"),"another-dependency"]]
        self.run_case(enc(value),1)
        value=envelope_value()
        value[3]=[sym("finite-proof")]
        self.run_case(enc(value),1)

    def test_malformed_unknown_executable_and_truncated_artifacts(self):
        for value in [b"\x09",enc(sym("new-untrusted-symbol")),enc('(load "x")'),
                      enc(envelope_value())[:-1],enc(envelope_value())+b"\0"]:
            with self.subTest(value=value[:20]): self.run_case(value,1)

    def test_decode_exhaustion_remains_unknown(self):
        for old,new in [("depth-limit -> 64","depth-limit -> 1"),
                        ("node-limit -> 10000","node-limit -> 1")]:
            with self.subTest(limit=old):
                cfg=self.config_variant([(old,new)])
                self.run_case(enc(envelope_value()),2,cfg)

    def test_invalid_known_symbol_table(self):
        cfg=self.config_variant([("-> [vor-root vor-claim", "-> [42 vor-root vor-claim")])
        self.run_case(enc(envelope_value()),1,cfg)

    def test_proof_budget_is_not_a_rejection(self):
        root=[sym("vor-root"),0,"reviewed-vor/0","shen-scheme-43.1-pr117"]
        proposition=[sym("implies"),[sym("atom"),sym("p")],[sym("atom"),sym("p")]]
        claim=[sym("vor-claim"),0,root,sym("logic"),[],[],sym("intuitionistic-propositions"),
               [sym("derives"),sym("empty"),proposition],sym("concrete-derivation")]
        value=[sym("vor-evidence"),0,claim,[sym("intro"),[sym("hyp")]]]
        config = """(define vor.service.root -> [vor-root 0 \"reviewed-vor/0\" \"shen-scheme-43.1-pr117\"])
(define vor.service.expected -> [vor-claim 0 (vor.service.root) logic [] [] intuitionistic-propositions [derives empty [implies [atom p] [atom p]]] concrete-derivation])
(define vor.service.symbols -> [vor-evidence vor-root vor-claim logic intuitionistic-propositions derives empty implies atom p concrete-derivation intro hyp])
(define vor.service.byte-limit -> 8192)
(define vor.service.depth-limit -> 64)
(define vor.service.node-limit -> 10000)
(define vor.service.proof-limit -> BUDGET)
""".replace('\"','"')
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/"logic.shen"
            for budget,status in [(30,0),(1,2)]:
                path.write_text(config.replace("BUDGET",str(budget)))
                self.run_case(enc(value),status,str(path))


    def test_closed_program_evaluation_witness(self):
        s = sym
        name = s("r03.service")
        source = [s("shen-source"), 0, [[s("define"), name, s("->"), s("good")]]]
        body = [s("literal"), s("good")]
        clauses = [[s("clause"), [], [s("literal"), True], body]]
        program = [s("vor-program"), 0, source, [[s("function"), name, 0, clauses]]]
        root = [s("vor-root"), 0, "reviewed-r03", "shared-43.1-pr117"]
        outcome = [s("value"), s("good")]
        claim = [s("vor-claim"), 0, root, [s("program"), program], [], [],
                 s("admitted-shen-0"), [s("evaluates"), name, [], outcome], s("concrete-derivation")]
        frame = [[s("guard"), name, body, [], [], []]]
        states = [
            [s("machine"), [s("call"), name, []], []],
            [s("machine"), [s("choose"), name, clauses, []], []],
            [s("machine"), [s("eval"), [s("literal"), True], []], frame],
            [s("machine"), [s("return"), True], frame],
            [s("machine"), [s("eval"), body, []], []],
            [s("machine"), [s("return"), s("good")], []],
        ]
        witness = [s("vor-evaluation"), 0, program, name, [], outcome, states]
        envelope = [s("vor-evidence"), 0, claim, witness]
        config = """(define vor.service.root -> [vor-root 0 "reviewed-r03" "shared-43.1-pr117"])
(define vor.service.program -> (hd (tl (vor.normalize [shen-source 0 [[define r03.service -> good]]]))))
(define vor.service.expected -> [vor-claim 0 (vor.service.root) [program (vor.service.program)] [] [] admitted-shen-0 [evaluates r03.service [] [value good]] concrete-derivation])
(define vor.service.symbols -> [vor-root vor-claim vor-evidence vor-program shen-source define -> good function clause literal program admitted-shen-0 evaluates value concrete-derivation vor-evaluation r03.service machine call choose eval guard return])
(define vor.service.byte-limit -> 8192)
(define vor.service.depth-limit -> 64)
(define vor.service.node-limit -> 10000)
(define vor.service.proof-limit -> BUDGET)
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "evaluation.shen"
            path.write_text(config.replace("BUDGET", "100"))
            self.run_case(enc(envelope), 0, str(path))
            tampered = copy.deepcopy(envelope)
            del tampered[3][6][1]
            self.run_case(enc(tampered), 1, str(path))
            path.write_text(config.replace("BUDGET", "1"))
            self.run_case(enc(envelope), 2, str(path))


    def test_generic_total_admission(self):
        # Independent fixture: no Shen proof producer is trusted by this test.
        import json
        s = sym
        v = lambda n: [s("v"), n]
        app = lambda c, xs: [s("app"), s(c), xs]
        eq = lambda a, b: [s("equal"), s("natural"), a, b]
        name = s("service.identity")
        source = [s("shen-source"), 0, [[s("define"), name,
            s("zero"), s("->"), s("zero"),
            [s("cons"), s("succ"), [s("cons"), s("X"), []]], s("->"),
            [s("cons"), s("succ"), [s("cons"), s("X"), []]]]]]
        lit = lambda x: [s("literal"), x]
        body = [s("primitive"), s("cons"), [lit(s("succ")),
            [s("primitive"), s("cons"), [[s("local"), 0], lit([])]]]]
        pattern = [s("pcons"), lit(s("succ")), [s("pcons"), [s("pvar"), 0], lit([])]]
        program = [s("vor-program"), 0, source, [[s("function"), name, 1, [
            [s("clause"), [lit(s("zero"))], lit(True), lit(s("zero"))],
            [s("clause"), [pattern], lit(True), body]]]]]
        data = [[s("data"), s("natural"), [[s("zero"), []], [s("succ"), [s("natural")]]]]]
        signature = [s("fol-signature"), 1, [], [[name, [s("natural")], s("natural")]], [], data]
        contracts = [[s("contract"), name, [s("natural")], s("natural"), 0, eq(v(0), v(1))]]
        construction = [[s("definition"), name, [
            [s("case"), s("zero"), [s("constructor"), s("zero"), []]],
            [s("case"), s("succ"), [s("constructor"), s("succ"), [[s("local")]]]]]]]
        step_body = eq(app("service.identity", [app("succ", [v(0)])]), app("succ", [v(0)]))
        proof = [s("data-induct"), [
            [s("zero"), [s("hyp"), 0]],
            [s("succ"), [s("inst"), s("natural"), step_body, v(0), [s("hyp"), 2]]]]]
        evidence = [s("vor-admission"), 0, program, signature, contracts, construction,
                    [[s("post"), name, proof]]]
        root = [s("vor-root"), 0, "reviewed-r045", "shared-43.1-pr117"]
        claim = [s("vor-claim"), 0, root, [s("total-program"), program, signature, contracts],
                 [], [], s("total-shen-1"), [s("total-contracts")], s("generic-proof")]
        envelope = [s("vor-evidence"), 0, claim, evidence]

        def shen(x):
            if isinstance(x, tuple):
                return "(intern " + json.dumps(x[1]) + ")" if x[1][:1].isupper() else x[1]
            if x is True: return "true"
            if x is False: return "false"
            if isinstance(x, list): return "[" + " ".join(shen(v) for v in x) + "]"
            return json.dumps(x)

        symbols = set()
        def collect(x):
            if isinstance(x, tuple): symbols.add(x[1])
            elif isinstance(x, list):
                for item in x: collect(item)
        collect(envelope)
        config = "\n".join([
            "(define vor.service.root -> " + shen(root) + ")",
            "(define vor.service.expected -> " + shen(claim) + ")",
            "(define vor.service.symbols -> " + shen([s(n) for n in sorted(symbols)]) + ")",
            "(define vor.service.byte-limit -> 8192)",
            "(define vor.service.depth-limit -> 64)",
            "(define vor.service.node-limit -> 10000)",
            "(define vor.service.proof-limit -> BUDGET)"])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "admission.shen"
            path.write_text(config.replace("BUDGET", "100"))
            self.run_case(enc(envelope), 0, str(path))
            forged = copy.deepcopy(envelope)
            forged[3][6][0][2] = [s("verified"), True]
            # The symbol is deliberately pre-existing; rejection is semantic.
            path.write_text(config.replace("BUDGET", "100").replace(
                "vor.service.symbols -> [", "vor.service.symbols -> [verified "))
            self.run_case(enc(forged), 1, str(path))
            incomplete = copy.deepcopy(envelope)
            del incomplete[3][5][0][2][1]
            self.run_case(enc(incomplete), 1, str(path))
            path.write_text(config.replace("BUDGET", "1"))
            self.run_case(enc(envelope), 2, str(path))


if __name__ == "__main__":
    unittest.main()
