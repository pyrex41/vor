#!/usr/bin/env python3
"""Independent transport corpus; it never decides VOR semantic validity."""
import copy, importlib.util, io, os, struct, subprocess, sys, tempfile, threading, time, unittest
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

def run(body, timeout=4):
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

    def test_transport_truncation_trailing_and_bounds(self):
        good = bytes([17])+enc(envelope_value())
        for raw in [b"", b"\0", struct.pack(">I", 0), struct.pack(">I",8193),
                    struct.pack(">I",len(good)+1)+good,
                    struct.pack(">I",len(good))+good+b"x"]:
            with self.subTest(raw=raw[:5]), self.assertRaises(launcher.ServiceError):
                launcher.read_request(io.BytesIO(raw))
        self.assertEqual(launcher.read_request(io.BytesIO(struct.pack(">I",len(good))+good)),good)


class SemanticProcessTests(unittest.TestCase):
    def run_case(self, value, status, config=CFG, cwd=ROOT):
        raw = struct.pack(">I",len(value)+1)+bytes([17])+value
        result = subprocess.run([SHIM,config],input=raw,stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,cwd=cwd,timeout=8)
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
