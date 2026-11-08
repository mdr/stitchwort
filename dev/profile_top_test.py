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


if __name__ == "__main__":
    unittest.main()
