"""Regression tests for the intentionally source-level index."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import generate_index as indexer


class IndexTests(unittest.TestCase):
    def test_comments_scopes_attributes_and_private_names(self):
        source = '''/- theorem fake : False := by /- nested -/ -/
namespace Outer
section Variables
@[simp,
  grind]
private theorem hidden : True := by trivial
end Variables
namespace Inner
def visible := "namespace Fake\\\" end"
end Inner
end Outer
-- theorem fake2
'''
        declarations = indexer.declarations(source)
        self.assertEqual(
            [(d["name"], d["namespace"], d["line"], d["visibility"]) for d in declarations],
            [("hidden", "Outer", 6, "private"), ("visible", "Outer.Inner", 9, "public")],
        )

    def test_escaped_identifiers_and_character_literals(self):
        source = '''namespace N
def «hello--world» := 1
def «hello/-world» := 2
def quote : Char := '"'
theorem after_quote : True := by trivial
end N
'''
        self.assertEqual([d["name"] for d in indexer.declarations(source)],
                         ["«hello--world»", "«hello/-world»", "quote", "after_quote"])

    def test_deterministic_roundtrip(self):
        index = indexer.build_index()
        self.assertEqual(json.loads(indexer.render(index)), index)
        self.assertEqual(indexer.render(index), indexer.render(indexer.build_index()))

    def test_check_rejects_stale_and_missing_index(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "INDEX.json"
            with patch.object(indexer, "OUTPUT", output), patch("sys.argv", ["index", "--check"]):
                with self.assertRaisesRegex(SystemExit, "stale"):
                    indexer.main()
                output.write_text("stale\n", encoding="utf-8")
                with self.assertRaisesRegex(SystemExit, "stale"):
                    indexer.main()
                output.write_text(indexer.render(indexer.build_index()), encoding="utf-8")
                indexer.main()


if __name__ == "__main__":
    unittest.main()
