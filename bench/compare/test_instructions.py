"""Tests for parsing instructions-retired output: python3 -I test_instructions.py"""

import importlib.util
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("compare", Path(__file__).resolve().parent / "compare.py")
compare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compare)

MACOS = """\
        1.23 real         1.10 user         0.05 sys
            24420352  maximum resident set size
                   0  page reclaims
          9100323451  instructions retired
          3200100222  cycles elapsed
             7864704  peak memory footprint
"""
PERF = "warning: something\n9100323451,,instructions,1234567,100.00,,\n"
PERF_UNSUPPORTED = "<not supported>,,instructions,0,0.00,,\n"


class Parse(unittest.TestCase):
    def test_macos(self):
        self.assertEqual(compare.parse_instructions(MACOS, "Darwin"), 9100323451)

    def test_perf(self):
        self.assertEqual(compare.parse_instructions(PERF, "Linux"), 9100323451)

    def test_unsupported(self):
        self.assertIsNone(compare.parse_instructions(PERF_UNSUPPORTED, "Linux"))
        self.assertIsNone(compare.parse_instructions("no counts here", "Darwin"))

    def test_table_subtracts_startup(self):
        counts = {"null": {"native": 1_000_000}, "p": {"native": 3_001_000_000, "cpython": None}}
        table, _ = compare.instruction_table(counts, ["p"], ["native", "cpython"])
        self.assertIn("3.00 G", table)
        self.assertIn("n/a", table)


class Geomean(unittest.TestCase):
    RATIOS = {
        "a": {"cpython": 2.0, "lean": 10.0},
        "b": {"cpython": 8.0, "lean": 40.0},
        "w": {"cpython": 1.0},
    }
    SETS = {"a": "core", "b": "core", "w": "wide"}

    def rows(self):
        return compare.geomean_lines(self.RATIOS, self.SETS).splitlines()

    def test_core_wide_and_all(self):
        core, wide, everything = self.rows()[2:]
        self.assertEqual(core, "| core | 4.00x (2 programs) | 20.00x (2 programs) |")
        self.assertEqual(wide, "| wide | 1.00x (1 programs) | - |")
        self.assertIn("2.52x (3 programs)", everything)
        self.assertIn("20.00x (2 programs)", everything)


if __name__ == "__main__":
    unittest.main()
