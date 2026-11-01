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
            "--| Faster than the old one. Kept.\n"
            "-- It recurses on the first argument\n"
            "-- (SW-12, so the check is cheap).\n"
            "-- (D58)\n"
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

    def test_citation_lifted_sentence_stays_user(self):
        src = (
            "-- Adds one (D58) to n, see (SW-3 and §2).\n"
            "-- Cheap.\ndef g: Nat = 1\n"
        )
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(
            new,
            "--| Adds one to n, see. Cheap.\n-- (D58)\n-- (SW-3 and §2)\n"
            "def g: Nat = 1\n",
        )

    def test_citation_period_stays_with_sentence(self):
        # Rewrapped to the width of the longest original line (21).
        src = "-- It is fast (SW-12).\n-- It is small.\ndef g: Nat = 1\n"
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(
            new,
            "--| It is fast. It is\n--| small.\n-- (SW-12)\ndef g: Nat = 1\n",
        )

    def test_mixed_bracket_is_not_a_citation(self):
        # Words besides markers: the sentence is a note, whole.
        src = "-- Works.\n-- It is lazy (D58, because of the cost).\ndef g: Nat = 1\n"
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(
            new,
            "--| Works.\n-- It is lazy (D58, because of the cost).\ndef g: Nat = 1\n",
        )

    def test_user_guide_reference_stays_user(self):
        src = "-- Syntax is in `docs/syntax.md` (see docs/syntax.md).\ndef g: Nat = 1\n"
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(new, src.replace("-- ", "--| ", 1))

    def test_sorts_by_sentence_and_rewraps(self):
        # One line holds a user sentence and a note sentence; the paragraph
        # is rewrapped to its original width (the longest line, 28).
        src = (
            "-- Adds two numbers, fast. It\n"
            "-- is kept for §2.1. More.\n"
            "def g: Nat = 1\n"
        )
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(
            new,
            "--| Adds two numbers, fast.\n"
            "--| More.\n"
            "-- It is kept for §2.1.\n"
            "def g: Nat = 1\n",
        )

    def test_blank_lines_kept(self):
        src = (
            "-- First.\n--\n-- Second, SW-1.\n--\n-- Third.\n--\n"
            "-- Fourth, D99.\n--\n-- Fifth, D98.\ndef g: Nat = 1\n"
        )
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(
            new,
            "--| First.\n--|\n--| Third.\n--\n-- Second, SW-1.\n--\n"
            "-- Fourth, D99.\n--\n-- Fifth, D98.\ndef g: Nat = 1\n",
        )

    def test_no_blank_inside_a_split_paragraph(self):
        src = "-- Adds.\n-- Kept (D58), ok, SW-4.\ndef g: Nat = 1\n"
        new, _, _ = docsort.sort_text(src)
        self.assertEqual(new, "--| Adds.\n-- Kept (D58), ok, SW-4.\ndef g: Nat = 1\n")

    def test_report(self):
        src = (
            "--| A line that is short\n"
            "--| enough to take more words in\n"
            "--| the next line, which is long.\n"
            "--| The argument: by cases.\n"
            "def a: Nat = 1\n"
            "\n"
            "-- Only notes, SW-1.\n"
            "def b: Nat = 1\n"
            "\n"
            "--| This file is Kept apart.\n"
            "def c: Nat = 1\n"
        )
        got = docsort.report_text(src)
        kinds = [k for _, k, _ in got]
        self.assertIn("ragged line", kinds)
        self.assertIn("rationale phrase 'The argument:'", kinds)
        self.assertIn("rationale phrase 'Kept apart'", kinds)
        self.assertIn("rationale phrase 'This file'", kinds)
        self.assertIn("run wholly `--` above a declaration", kinds)
        self.assertEqual(
            docsort.report_text("--| Fine.\n--| Also fine here.\ndef a: Nat = 1\n"), []
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
        words = lambda t: sorted(
            w.strip(".") for w in t.replace("--|", "").replace("--", "").split()
        )
        self.assertEqual(words(SRC), words(self.new))

    def test_code_untouched(self):
        code = lambda t: [l for l in t.split("\n") if not l.lstrip().startswith("--")]
        self.assertEqual(code(SRC), code(self.new))


if __name__ == "__main__":
    unittest.main()
