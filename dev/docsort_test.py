#!/usr/bin/env python3
"""Tests for dev/docsort. Run: python3 dev/docsort_test.py"""
import importlib.machinery
import importlib.util
import os
import unittest

here = os.path.dirname(os.path.abspath(__file__))
loader = importlib.machinery.SourceFileLoader("docsort", os.path.join(here, "docsort"))
docsort = importlib.util.module_from_spec(importlib.util.spec_from_loader("docsort", loader))
loader.exec_module(docsort)

SRC = """-- A heading without a stop

-- Adds two numbers. Costs O(n).
-- It recurses on the first argument
-- (SW-12, so the check is cheap).
-- Faster than the old one. Kept (D58).
-- Elsewhere in §2.1.
def add: Nat -> Nat -> Nat
    | Zero, n => n

-- Not a doc, a loose comment.

type T =
  -- A constructor.
  -- See docs/proposals/x.md.
  | A
  | B

def f: Nat =
  -- inside a body: untouched
  1
"""


class Sort(unittest.TestCase):
    def setUp(self):
        self.new, self.blocks, self.moved = docsort.sort_text(SRC)

    def test_decl_run(self):
        # The sentence joined to SW-12 moves below; the rest is user docs.
        self.assertIn(
            "--| Adds two numbers. Costs O(n).\n"
            "-- It recurses on the first argument\n"
            "-- (SW-12, so the check is cheap).\n"
            "-- Faster than the old one. Kept (D58).\n"
            "-- Elsewhere in §2.1.\n"
            "def add",
            self.new,
        )

    def test_member_run(self):
        self.assertIn("  --| A constructor.\n  -- See docs/proposals/x.md.\n  | A", self.new)

    def test_counts(self):
        self.assertEqual((self.blocks, self.moved), (2, 5))

    def test_lead_in_joins_next_unit(self):
        # "Cases:" follows the unit after it to the notes; "Done." stays.
        src = (
            "-- Computes x.\n-- Cases:\n-- - a, see SW-9.\n-- - b.\n"
            "-- Done.\ndef g: Nat = 1\n"
        )
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(
            new,
            "--| Computes x.\n--| - b.\n--| Done.\n"
            "-- Cases:\n-- - a, see SW-9.\ndef g: Nat = 1\n",
        )

    def test_untouched(self):
        for kept in [
            "-- A heading without a stop\n",
            "-- Not a doc, a loose comment.\n",
            "  -- inside a body: untouched\n",
        ]:
            self.assertIn(kept, self.new)

    def test_idempotent_and_only_markers_change(self):
        again, blocks, _ = docsort.sort_text(self.new)
        self.assertEqual((again, blocks), (self.new, 0))
        words = lambda t: sorted(t.replace("--|", "").replace("--", "").split())
        self.assertEqual(words(SRC), words(self.new))

    def test_code_untouched(self):
        code = lambda t: [l for l in t.split("\n") if not l.lstrip().startswith("--")]
        self.assertEqual(code(SRC), code(self.new))


if __name__ == "__main__":
    unittest.main()
