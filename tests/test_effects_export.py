import importlib.util
from importlib.machinery import SourceFileLoader
import json
import os
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_loader("effects_export", SourceFileLoader("effects_export", str(ROOT / "scripts" / "export-effects-model")))
export = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(export)


class EffectsExportTests(unittest.TestCase):
    def run_export(self, mode, output):
        return subprocess.run([sys.executable, str(ROOT / "scripts" / "export-effects-model"),
                              "--mode", mode, "--output", str(output)],
                              cwd=ROOT, text=True, capture_output=True, timeout=10)

    def test_all_modes_are_exact_schema_and_source_bound(self):
        with tempfile.TemporaryDirectory(prefix="effects-export-") as directory:
            for mode in ("healthy", "mutant-commit", "mutant-finish", "mutant-duplicate", "mutant-lost-work"):
                output = Path(directory) / (mode + ".json")
                result = self.run_export(mode, output)
                self.assertEqual(result.returncode, 0, result.stderr)
                document = json.loads(output.read_text())
                self.assertEqual(set(document), {"schema", "model", "sources", "verification"})
                self.assertEqual(document["schema"], "vor-effects-model-v1")
                self.assertEqual(document["model"][:2], ["vor-model", 0])
                self.assertIn("scripts/export-effects-model", document["sources"])
                self.assertTrue(any(name.startswith(".tools/") for name in document["sources"]))
                self.assertFalse(any(name.startswith("/") for name in document["sources"]))

    def test_parser_rejects_hostile_or_trailing_input(self):
        for value in ("junk", "[vor-model 0] trailing", "[vor-model 0", "[a [b [c]] extra"):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    export.parse_sexpr(value)
        deep = "[" * 130 + "x" + "]" * 130
        with self.assertRaises(ValueError):
            export.parse_sexpr(deep)

    def test_existing_and_broken_symlink_outputs_are_not_overwritten(self):
        with tempfile.TemporaryDirectory(prefix="effects-output-") as directory:
            existing = Path(directory) / "existing.json"
            existing.write_text("keep")
            result = self.run_export("healthy", existing)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(existing.read_text(), "keep")
            broken = Path(directory) / "broken.json"
            broken.symlink_to(Path(directory) / "missing")
            result = self.run_export("healthy", broken)
            self.assertNotEqual(result.returncode, 0)
            self.assertTrue(broken.is_symlink())

    def test_supervisor_bounds_output_and_time(self):
        noisy = [sys.executable, "-c", "import sys; sys.stdout.write('x' * 1100000)"]
        started = time.monotonic()
        with self.assertRaises(RuntimeError):
            export._bounded_run(noisy)
        self.assertLess(time.monotonic() - started, 5)
        old = export.MAX_SECONDS
        export.MAX_SECONDS = 0.05
        try:
            started = time.monotonic()
            with self.assertRaises(RuntimeError):
                export._bounded_run([sys.executable, "-c", "import time; time.sleep(2)"])
            self.assertLess(time.monotonic() - started, 2)
        finally:
            export.MAX_SECONDS = old

    def test_supervisor_kills_one_byte_writer_and_descendant(self):
        old = export.MAX_SECONDS
        export.MAX_SECONDS = 0.05
        try:
            for code in (
                "import sys,time; sys.stdout.write('x'); sys.stdout.flush(); time.sleep(2)",
                "import subprocess,sys,time; subprocess.Popen([sys.executable,'-c','import time; time.sleep(2)']); time.sleep(2)",
            ):
                started = time.monotonic()
                with self.assertRaises(RuntimeError):
                    export._bounded_run([sys.executable, "-c", code])
                self.assertLess(time.monotonic() - started, 2)
        finally:
            export.MAX_SECONDS = old

    def test_source_drift_during_run_is_rejected(self):
        model_path = ROOT / "examples" / "effects-protocol.shen"
        original = model_path.read_bytes()
        with tempfile.TemporaryDirectory(prefix="effects-drift-") as directory:
            output = Path(directory) / "drift.json"
            real_run = export._bounded_run
            def drift(command):
                result = real_run(command)
                model_path.write_bytes(original + b"\\n")
                return result
            argv = ["export-effects-model", "--output", str(output)]
            try:
                with patch.object(export, "_bounded_run", drift), patch.object(sys, "argv", argv):
                    with self.assertRaises(SystemExit) as failure:
                        export.main()
                self.assertIn("source identity changed", str(failure.exception))
                self.assertFalse(output.exists())
            finally:
                model_path.write_bytes(original)


if __name__ == "__main__":
    unittest.main()
