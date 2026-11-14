#!/usr/bin/env python3
"""Tests for dev/tier-report and dev/tier-step. Run: python3 dev/tier-report_test.py"""
import importlib.machinery
import importlib.util
import os
import subprocess
import sys
import tempfile
import unittest

here = os.path.dirname(os.path.abspath(__file__))
loader = importlib.machinery.SourceFileLoader("tr", os.path.join(here, "tier-report"))
tr = importlib.util.module_from_spec(importlib.util.spec_from_loader("tr", loader))
loader.exec_module(tr)

JUNIT = """<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="nextest-run" tests="4" failures="1" time="12.5">
  <testsuite name="stitchwort-core" tests="2">
    <testcase name="kernel::a" classname="stitchwort-core" time="0.5"/>
    <testcase name="kernel::b" classname="stitchwort-core" time="1.5"/>
  </testsuite>
  <testsuite name="stitchwort-driver::proofs" tests="2">
    <testcase name="slow" classname="stitchwort-driver::proofs" time="30.0"/>
    <testcase name="bad" classname="stitchwort-driver::proofs" time="2.0"><failure message="x"/></testcase>
  </testsuite>
</testsuites>
"""

LOG = (
    "fmt\tstep\t100.0\t2.50\t0\t\n"
    "nextest build\tstep\t103.0\t20.00\t0\t\n"
    "builtins\tparallel\t125.0\t40.00\t0\t\n"
    "nextest run\tstep\t124.0\t12.50\t1\t3221225472\n"
)


class T(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.log = os.path.join(self.dir, "log.tsv")
        self.junit = os.path.join(self.dir, "junit.xml")
        open(self.log, "w").write(LOG)
        open(self.junit, "w").write(JUNIT)

    def test_reads_the_step_log_in_start_order(self):
        steps = tr.read_steps(self.log)
        self.assertEqual([s["name"] for s in steps], ["fmt", "nextest build", "nextest run", "builtins"])
        self.assertEqual(steps[2]["peak"], 3 * 1024**3)
        self.assertEqual(tr.read_steps(os.path.join(self.dir, "none")), [])

    def test_reads_junit(self):
        wall, tests = tr.read_junit(self.junit)
        self.assertEqual(wall, 12.5)
        self.assertEqual(len(tests), 4)
        self.assertEqual([t["name"] for t in tests if t["failed"]], ["bad"])

    def test_sums(self):
        _, tests = tr.read_junit(self.junit)
        self.assertEqual(tr.sum_by(tests, lambda t: t["binary"])[0], ("stitchwort-driver::proofs", 2, 32.0))

    def test_summary_leaves_parallel_steps_out_of_the_sum(self):
        _, tests = tr.read_junit(self.junit)
        sm = tr.summarise(tr.read_steps(self.log), tests, 12.5, 100.0, 140.0)
        self.assertEqual(sm["steps_total"], 2.5 + 20.0 + 12.5)
        self.assertEqual((sm["tests"], sm["failures"], sm["code"]), (4, 1, 1))
        self.assertEqual(sm["test_sum"], 34.0)
        self.assertEqual(sm["run_wall"], 12.5)

    def test_the_report_has_every_section(self):
        _, tests = tr.read_junit(self.junit)
        areas = {("stitchwort-core", "kernel::a"): "core", ("stitchwort-core", "kernel::b"): "core"}
        text, _ = tr.render("quick", "abc123", 100.0, 140.0, (1.0, 2.0, 3.0), (4.0, 5.0, 6.0),
                            tr.read_steps(self.log), tests, 12.5, areas)
        for want in ["# Tier report: quick, abc123", "| nextest build | 20.0 |", "beside: builtins",
                     "## 15 slowest tests", "`slow`", "## Test time per binary", "| core | 2 | 2.0 |",
                     "(no lane area) | 2 | 32.0", "load average (1, 5, 15 min) at the start: 1.0, 2.0, 3.0",
                     "peak memory under the guard: 3.00 GB", "failed (exit 1)", "(between steps)"]:
            self.assertIn(want, text)

    def test_history_row_and_view(self):
        _, tests = tr.read_junit(self.junit)
        steps = tr.read_steps(self.log)
        sm = tr.summarise(steps, tests, 12.5, 100.0, 140.0)
        row = tr.history_row("quick", "abc123", 100.0, steps, sm)
        self.assertEqual(row[1:8], ["quick", "abc123", "1", "40", "4", "1", "34"])
        self.assertIn("nextest_build=20", row[9])
        self.assertNotIn("builtins", row[9])
        path = os.path.join(self.dir, "h.tsv")
        tr.append_history(path, row)
        tr.append_history(path, row)
        self.assertEqual(len(open(path).read().splitlines()), 3)

    def test_a_report_without_junit_still_writes(self):
        out = os.path.join(self.dir, "out")
        path, text = tr.write_report("quick", self.log, None, 100.0, 140.0, (0, 0, 0), (0, 0, 0),
                                     areas_fn=lambda: {}, out=out, history=os.path.join(out, "h.tsv"))
        self.assertTrue(os.path.exists(path))
        self.assertTrue(os.path.exists(os.path.join(out, "latest-quick.md")))
        self.assertIn("No JUnit file", text)

    def test_tier_step_logs_and_keeps_the_exit_code(self):
        step = os.path.join(here, "tier-step")
        env = dict(os.environ, STITCHWORT_TIER_LOG=self.log + ".new")
        r = subprocess.run([step, "boom", "--", sys.executable, "-c", "import sys; sys.exit(7)"], env=env)
        self.assertEqual(r.returncode, 7)
        r = subprocess.run([step, "--parallel", "ok", "--", "true"], env=env)
        self.assertEqual(r.returncode, 0)
        steps = tr.read_steps(self.log + ".new")
        self.assertEqual([(s["name"], s["kind"], s["code"]) for s in steps], [("boom", "step", 7), ("ok", "parallel", 0)])
        env.pop("STITCHWORT_TIER_LOG")
        self.assertEqual(subprocess.run([step, "x", "--", "true"], env=env).returncode, 0)

    def test_memguard_writes_its_peak(self):
        peak = os.path.join(self.dir, "peak")
        env = dict(os.environ, STITCHWORT_MEM_PEAK_FILE=peak)
        subprocess.run([os.path.join(here, "memguard"), "--cap-gb", "0", "--", "sleep", "1"], env=env, check=True)
        self.assertGreaterEqual(int(open(peak).read()), 0)


if __name__ == "__main__":
    unittest.main()
