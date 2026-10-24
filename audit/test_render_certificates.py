import copy
import unittest
from pathlib import Path
import render_certificates as r


def encode(x):
    if x == []: return b"\0"
    if x is False: return b"\1"
    if x is True: return b"\2"
    if type(x) is int: return b"\3" + x.to_bytes(2, "big")
    if isinstance(x, r.Symbol):
        s = x.name.encode("ascii"); return b"\4" + len(s).to_bytes(2,"big") + s
    if isinstance(x, str):
        s = x.encode("ascii"); return b"\5" + len(s).to_bytes(2,"big") + s
    if isinstance(x, list): return b"\6" + len(x).to_bytes(2,"big") + b"".join(encode(v) for v in x)
    raise ValueError(x)


class ReificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = (Path(__file__).resolve().parent.parent / "build/audit/fixtures.bin").read_bytes()
        cls.packet = r.decode(cls.raw)

    def test_all_symbolic_bodies(self):
        text, count = r.render(self.raw)
        self.assertEqual(count, 12)
        self.assertEqual(text.count("Theorem body_"), 12)
        self.assertEqual(text.count("forall call env v"), 12)

    def test_round_trip_independent_encoding(self):
        self.assertEqual(encode(self.packet), self.raw)

    def test_boolean_numeric_classes_stay_distinct(self):
        self.assertFalse(r.same(True, 1))
        self.assertFalse(r.same(False, 0))
        self.assertFalse(r.same([r.Symbol("literal"), True], [r.Symbol("literal"), 1]))

    def test_truncation_and_trailing(self):
        for data in [self.raw[:-1], self.raw+b"\0", b"\x06\x00\x00", b"\x07\0\0"]:
            with self.subTest(data=data[-8:]), self.assertRaises(ValueError): r.decode(data)

    def test_version_type_binding(self):
        packet = copy.deepcopy(self.packet); packet[1] = False
        with self.assertRaises(ValueError): r.render(encode(packet))

    def test_program_substitution(self):
        packet = copy.deepcopy(self.packet)
        packet[3][2][3][0][1] = r.Symbol("other.program")
        with self.assertRaises(ValueError): r.render(encode(packet))

    def test_missing_clause(self):
        packet = copy.deepcopy(self.packet); packet[3][3][0][3].pop()
        with self.assertRaises(ValueError): r.render(encode(packet))

    def test_guard_boolean_is_not_one(self):
        packet = copy.deepcopy(self.packet)
        packet[2][3][0][3][0][2][1] = 1
        packet[3][2] = packet[2]
        packet[3][3][0][3][0][2][1] = 1
        with self.assertRaises(ValueError): r.render(encode(packet))

    def test_rocq_source_injection_is_never_an_index(self):
        for invalid in [True, "0). Axiom injected : False.", r.Symbol("fake.index")]:
            packet = copy.deepcopy(self.packet)
            packet[2][3][0][3][0][3] = [r.Symbol("local"), invalid]
            packet[3][2] = packet[2]
            with self.subTest(index=invalid), self.assertRaises(ValueError): r.render(encode(packet))

    def test_instruction_arity_is_typed(self):
        packet = copy.deepcopy(self.packet)
        packet[3][3][0][3][0][3] = [[r.Symbol("call"), r.Symbol("total.copy"), "1). Check False."]]
        with self.assertRaises(ValueError): r.render(encode(packet))
