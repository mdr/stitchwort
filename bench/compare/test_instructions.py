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
        table = compare.instruction_table(counts, ["p"], ["native", "cpython"])
        self.assertIn("3.00 G", table)
        self.assertIn("n/a", table)


if __name__ == "__main__":
    unittest.main()
