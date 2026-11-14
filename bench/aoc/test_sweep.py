"""Tests for the sweep's answer reading and diffing: python3 -I test_sweep.py"""

import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("sweep", HERE / "sweep.py")
sweep = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sweep)

SOURCE = '''
const ANSWERS: &[(&str, &str, &str, &str)] = &[
    ("2020", "01", "1016619", "218767230"),
    (
        "2021",
        "13",
        "781",
        ".#\\n\\
         #.",
    ),
];
const SLOW: &[(&str, &str)] = &[("2020", "15")];
'''


def rec(n, status="ok"):
    return {"status": status, "instructions": n, "wall": 1.0}


class Answers(unittest.TestCase):
    def test_reads_answers_and_slow(self):
        answers, slow = sweep.read_answers(SOURCE)
        self.assertEqual(answers[("2020", "01")], "Part 1: 1016619\nPart 2: 218767230\n")
        self.assertEqual(answers[("2021", "13")], "Part 1: 781\nPart 2:\n.#\n#.\n")
        self.assertEqual(slow, {("2020", "15")})

    def test_the_real_file_parses(self):
        answers, slow = sweep.read_answers(sweep.ANSWERS_RS.read_text())
        self.assertGreater(len(answers), 50)
        self.assertTrue(slow <= set(answers))


class Select(unittest.TestCase):
    DAYS = [("2024", "01"), ("2024", "10"), ("2025", "01")]

    def test_year_and_regex(self):
        self.assertEqual(sweep.select(self.DAYS, "2025"), [("2025", "01")])
        self.assertEqual(sweep.select(self.DAYS, r"/01$"), [("2024", "01"), ("2025", "01")])
        self.assertEqual(sweep.select(self.DAYS, None), self.DAYS)


class Diff(unittest.TestCase):
    def test_percent_geomean_and_flags(self):
        old = {"a": rec(100), "b": rec(100), "c": rec(100), "gone": rec(5)}
        new = {"a": rec(200), "b": rec(50), "c": rec(102), "new": rec(7)}
        rows, mean = sweep.diff(new, old)
        self.assertEqual([r[0] for r in rows], ["a", "b", "c"])
        self.assertEqual([r[4] for r in rows], [True, True, False])
        self.assertAlmostEqual(rows[0][3], 100.0)
        # 2 * 0.5 * 1.02 over three days.
        self.assertAlmostEqual(mean, 1.02 ** (1 / 3))

    def test_failed_days_are_left_out(self):
        rows, mean = sweep.diff({"a": rec(None, "timeout"), "b": rec(10)}, {"a": rec(5), "b": rec(10, "wrong")})
        self.assertEqual(rows, [])
        self.assertIsNone(mean)


if __name__ == "__main__":
    unittest.main()
