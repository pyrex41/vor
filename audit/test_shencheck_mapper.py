import copy
import tempfile
import unittest
from pathlib import Path

from render_certificates import Symbol, decode
from render_shencheck_mapper import render
from test_render_certificates import encode


class ShenCheckMapperCaptureTests(unittest.TestCase):
    def test_constructor_rename_rejected_before_proof(self):
        packet = decode((Path(__file__).parent.parent / "build/audit/shencheck-mapper.bin").read_bytes())

        def rename(value):
            if isinstance(value, Symbol) and value.name == "sc-observation":
                return Symbol("evil-observation")
            if isinstance(value, list):
                return [rename(item) for item in value]
            return value

        mutated = encode(rename(copy.deepcopy(packet)))
        with tempfile.NamedTemporaryFile() as source:
            Path(source.name).write_bytes(mutated)
            with self.assertRaises(ValueError):
                render(source.name)

    def test_parameter_reserved_alias_rejected_before_proof(self):
        packet = decode((Path(__file__).parent.parent / "build/audit/shencheck-mapper.bin").read_bytes())
        packet[2][2][0] = Symbol("sc-observation")
        mutated = encode(packet)
        with tempfile.NamedTemporaryFile() as source:
            Path(source.name).write_bytes(mutated)
            with self.assertRaises(ValueError):
                render(source.name)

    def test_unknown_branch_mutation_changes_captured_prefix(self):
        packet = decode((Path(__file__).parent.parent / "build/audit/shencheck-mapper.bin").read_bytes())
        changed = [False]

        def drop_one(value):
            if isinstance(value, Symbol) and value.name == "not-applied" and not changed[0]:
                changed[0] = True
                return Symbol("applied")
            if isinstance(value, list):
                return [drop_one(item) for item in value]
            return value

        mutated = encode(drop_one(copy.deepcopy(packet)))
        with tempfile.NamedTemporaryFile() as source, tempfile.NamedTemporaryFile() as output:
            Path(source.name).write_bytes(mutated)
            digest, captured = render(source.name)
            versioned = (Path(__file__).parent / "rocq/ShenCheckMapperCapture.v").read_text()
            self.assertNotEqual(captured + "\n", versioned.split("(* MAPPER_PROOF_BEGIN *)", 1)[0])


if __name__ == "__main__":
    unittest.main()
