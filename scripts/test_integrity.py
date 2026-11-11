"""Fast source-guard and module-coverage regressions (no Lean required)."""

from pathlib import Path
import tempfile
import unittest

from check_axioms import audit_source, project_modules
from check_integrity import check_source, main as check_integrity


class IntegrityTests(unittest.TestCase):
    def test_rejects_forbidden_terms(self):
        for token in ("sorry", "admit", "axiom", "unsafe", "implemented_by", "extern",
                      "sorryAx", "native_decide", "ofReduceBool", "ofReduceNat",
                      "debug.skipKernelTC", "debug.proofAsSorry", "warn.sorry"):
            with self.subTest(token=token):
                self.assertIsNotNone(check_source(f"namespace Other\n{token}\nend Other"))

    def test_ignores_comments_and_strings_but_not_escaped_identifiers(self):
        self.assertIsNone(check_source('/- sorry /- axiom -/ -/ -- admit\ndef s := "sorry"'))
        self.assertIsNotNone(check_source("example : False := «sorryAx» False true"))
        self.assertIsNotNone(check_source("example : False := by /- comment -/ sorry"))

    def test_covers_unimported_and_verification_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "FreeProbability").mkdir()
            (root / "Verification").mkdir()
            for file in ("FreeProbability.lean", "Verification.lean", "FreeProbability/Unimported.lean",
                         "Verification/Example.lean"):
                (root / file).write_text("", encoding="utf-8")
            modules = project_modules(root)
            self.assertEqual(modules, ["FreeProbability", "FreeProbability.Unimported",
                                       "Verification", "Verification.Example"])
            source = audit_source(modules)
            self.assertFalse(source.startswith("module\n"))
            for module in modules:
                self.assertIn(f"import {module}\n", source)

    def test_source_guard_rejects_both_top_level_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for library in ("FreeProbability", "Verification"):
                (root / library).mkdir()
                (root / f"{library}.lean").write_text("", encoding="utf-8")
            for library in ("FreeProbability", "Verification"):
                with self.subTest(library=library):
                    path = root / f"{library}.lean"
                    path.write_text("axiom extra : False\n", encoding="utf-8")
                    with self.assertRaisesRegex(SystemExit, rf"{library}\.lean: forbidden token axiom"):
                        check_integrity(root)
                    path.write_text("", encoding="utf-8")


if __name__ == "__main__":
    unittest.main()
