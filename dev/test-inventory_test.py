#!/usr/bin/env python3
"""Tests for dev/test-inventory. Run: python3 dev/test-inventory_test.py"""
import importlib.machinery
import importlib.util
import json
import os
import tempfile
import unittest

here = os.path.dirname(os.path.abspath(__file__))
loader = importlib.machinery.SourceFileLoader("inv", os.path.join(here, "test-inventory"))
inv = importlib.util.module_from_spec(importlib.util.spec_from_loader("inv", loader))
loader.exec_module(inv)

LIST = json.dumps({"rust-suites": {
    "p::b": {"package-name": "p", "testcases": {
        "a": {"filter-match": {"status": "matches"}},
        "b": {"filter-match": {"status": "mismatch"}}}},
    "p": {"package-name": "p", "testcases": {}}}})

GROUPS = """group: corpus-sweeps (max threads = 1)
  * override for default profile with filter 'x' (from y):
      p::b:
          a
"""

JUNIT = """<testsuites timestamp="%s"><testsuite name="p::b">
<testcase name="a" classname="p::b" time="%s"/></testsuite></testsuites>"""


class T(unittest.TestCase):
    def test_list(self):
        self.assertEqual(inv.parse_list(LIST, True), {("p::b", "a"): "p"})
        self.assertEqual(len(inv.parse_list(LIST, False)), 2)

    def test_groups(self):
        self.assertEqual(inv.parse_groups(GROUPS), {("p::b", "a"): "corpus-sweeps"})

    def test_latest_wins_and_scale(self):
        store = {}
        inv.fold(store, "merge", "2026-01-02", {("p::b", "a"): 2.0})
        inv.fold(store, "merge", "2026-01-01", {("p::b", "a"): 9.0})
        self.assertEqual(store["p::b a"]["merge"]["time"], 2.0)
        inv.fold(store, "merge", "2026-01-03", {("p::b", "a"): 10.0}, 0.5)
        self.assertEqual(store["p::b a"]["merge"]["time"], 5.0)

    def test_best_time_prefers_merge(self):
        slot = {"merge": {"time": 1, "at": "1"}, "daily": {"time": 5, "at": "2"}}
        self.assertEqual(inv.best_time(slot), (1, "merge"))
        self.assertEqual(inv.best_time({"daily": {"time": 5, "at": "2"}}), (5, "daily"))
        self.assertEqual(inv.best_time(None), (None, None))

    def test_junit(self):
        with tempfile.NamedTemporaryFile("w", suffix=".xml", delete=False) as f:
            f.write(JUNIT % ("2026-01-01", "1.5"))
        stamp, times = inv.parse_junit(f.name)
        os.unlink(f.name)
        self.assertEqual((stamp, times), ("2026-01-01", {("p::b", "a"): 1.5}))

    def test_junit_tier(self):
        self.assertEqual(inv.parse_args_junit("/x/daily/junit.xml", "merge"), ("/x/daily/junit.xml", "daily", 1.0))
        self.assertEqual(inv.parse_args_junit("/x/y.xml@0.5", "merge"), ("/x/y.xml", "merge", 0.5))

    def test_estimate(self):
        tests = inv.build({("b", "t%d" % i): "p" for i in range(84)}, {"merge": set()}, {("b", "t0"): "g"},
                          {"b t%d" % i: {"merge": {"time": 1.0, "at": "1"}} for i in range(83)})
        ids = {t["id"] for t in tests}
        r = inv.estimate(tests, ids)
        self.assertEqual((r["count"], r["unknown"]), (84, 1))
        self.assertEqual(r["estimate"], 10.2)  # (83 + 3) / 8.4
        self.assertEqual(inv.estimate(tests, set())["estimate"], 0.0)


if __name__ == "__main__":
    unittest.main()
