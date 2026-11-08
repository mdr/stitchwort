#!/usr/bin/env python3
"""Tests for dev/profile_top.py's --pc-map folding. Run: python3 -I dev/profile_top_test.py"""
import importlib.util
import json
import os
import tempfile
import unittest

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("profile_top", os.path.join(here, "profile_top.py"))
profile_top = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile_top)

MAP = {"bodies": [{
    "symbol": "Main.f#3",
    "size": 40,
    "instrs": ["Switch", "Call", "Return"],
    "stretches": [[0, 8, None, "prologue"], [8, 16, 0, "work"], [16, 20, 1, "check"],
                  [20, 24, 1, "call"], [24, 28, None, "untagged"], [28, 40, 2, "return"]],
}]}


class Fold(unittest.TestCase):
    def test_samples_fold_into_parts_and_instructions(self):
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
            json.dump(MAP, f)
        try:
            body = profile_top.load_pc_map(f.name)["Main.f#3"]
        finally:
            os.unlink(f.name)
        samples = [(0, 1), (12, 2), (16, 3), (23, 1), (24, 5), (39, 4), (40, 7)]
        parts, pcs, pc_parts = profile_top.fold(samples, body)
        self.assertEqual(parts, {"prologue": 1, "work": 2, "check": 3, "call": 1, "untagged": 5,
                                 "return": 4, "outside the map": 7})
        self.assertEqual(pcs, {0: 2, 1: 4, 2: 4})
        self.assertEqual(pc_parts[1], {"check": 3, "call": 1})


class UnderLoop(unittest.TestCase):
    EXE = "prog"

    def stack(self, *names):
        return [(n, self.EXE) for n in names]

    def test_function_with_loop_beneath_is_marked(self):
        # Innermost first: the continuation's body, the loop, the handler's
        # definition, the outer loop, main.
        frames = self.stack("Main.rest#2", "rt_loop", "Main.parse#7", "Main.main#1", "rt_loop")
        self.assertEqual(profile_top.under_loop_names(frames, self.EXE), {"Main.parse#7", "Main.main#1"})

    def test_plain_calls_are_not_marked(self):
        frames = self.stack("Main.leaf#3", "Main.parse#7", "Main.main#1", "rt_loop")
        self.assertEqual(profile_top.under_loop_names(frames, self.EXE), set())

    def test_runtime_functions_are_not_marked(self):
        frames = [("rt_loop", self.EXE), ("Runner::drive", self.EXE), ("start", "libsystem_c.dylib")]
        self.assertEqual(profile_top.under_loop_names(frames, self.EXE), set())


class Focus(unittest.TestCase):
    NAMES = ["Aoc.Year2024.Day09.parseDiskMap#221", "Aoc.Year2024.Day09.parseDiskMap/lambda3#222",
             "Aoc.Year2024.Day09.parseDiskMapX#9", "Std.List.get#67", "Std.List.getOr#68"]

    def test_exact_name_matches_numbered_bodies_only(self):
        found, how = profile_top.match_focus("Aoc.Year2024.Day09.parseDiskMap", self.NAMES)
        self.assertEqual(found, self.NAMES[:2])
        self.assertEqual(how, "name")

    def test_substring_fallback_finds_several_definitions(self):
        found, how = profile_top.match_focus("parseDiskMap", self.NAMES)
        self.assertEqual(found, sorted(self.NAMES[:3]))
        self.assertEqual(how, "substring")

    def test_no_match_is_empty(self):
        self.assertEqual(profile_top.match_focus("Aoc.Day9.nothing", self.NAMES)[0], [])

    def test_miss_exits_listing_closest_names(self):
        with self.assertRaises(SystemExit) as cm:
            profile_top.fail_no_match("--focus", "Std.List.gt", self.NAMES)
        self.assertIn("Std.List.get#67", str(cm.exception))
        self.assertNotEqual(cm.exception.code, 0)


if __name__ == "__main__":
    unittest.main()
