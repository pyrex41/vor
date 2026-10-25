import copy
import unittest
from pathlib import Path
import render_first_order as fo
import render_native_lookup as native
from render_certificates import decode, Symbol
from test_render_certificates import encode
ROOT = Path(__file__).resolve().parent.parent

class CorrespondenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fo = decode((ROOT/'build/audit/first-order.bin').read_bytes())
        cls.native = decode((ROOT/'build/audit/native-lookup.bin').read_bytes())

    def test_full_original_rule_inventory(self):
        roots = {record[4][1][1] for record in self.fo[3]
                 if record[4][0] == Symbol('cell') and record[4][1][0] == Symbol('symbol')}
        self.assertTrue({'hyp','top','pair','fst','snd','intro','apply','inl','inr','cases',
                         'exfalso','gen','inst','witness','unpack','refl','sym','trans','subst','tree-induct'} <= roots)

    def test_all_native_results_are_compared(self):
        text, count, accepted = fo.render(encode(self.fo))
        self.assertEqual(count, 504)
        self.assertEqual(accepted, 163)
        self.assertEqual(text.count('vm_compute'), count)

    def test_negative_numbers_and_text_do_not_become_symbols(self):
        text, _, _ = fo.render(encode(self.fo))
        self.assertIn('NV.BadNumber', text)
        self.assertIn('NV.Text', text)

    def test_result_boolean_not_numeric(self):
        value=copy.deepcopy(self.fo); value[3][0][5][0][1]=1
        with self.assertRaises(ValueError): fo.render(encode(value))

    def test_number_injection_rejected(self):
        value=copy.deepcopy(self.fo)
        value[3][0][1]=[Symbol('natural'), '0). Axiom attack : False.']
        with self.assertRaises(ValueError): fo.render(encode(value))

    def test_quote_name_class_is_strict(self):
        value=copy.deepcopy(self.fo)
        value[3][0][1]=[Symbol('symbol'), True]
        with self.assertRaises(ValueError): fo.render(encode(value))

    def test_native_capture_resolves_slots_inside_rocq(self):
        text=native.render(encode(self.native))
        self.assertIn('decode_definition actual_lookup_kl',text)
        self.assertNotIn('Local 0',text)
        self.assertNotIn('Local 1',text)

    def test_native_parameters_cannot_alias(self):
        value=copy.deepcopy(self.native); value[2][2][1]=value[2][2][0]
        with self.assertRaises(ValueError): native.render(encode(value))

    def test_native_foreign_call_rejected(self):
        value=copy.deepcopy(self.native)
        value[2][3]=[Symbol('eval-kl'),[Symbol('load'),'never execute']]
        with self.assertRaises(ValueError): native.render(encode(value))
