#!/usr/bin/env python3
"""Tests for spellings.py: plain asserts, run with `python3 test_spellings.py`."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import spellings


def test_render_drops_one_group_of_a_unit():
    text = "foo [p := x] [q := y] bar"
    gs, us = spellings.parse(text, {"p", "q"})
    assert len(gs) == 2, gs
    assert len(us) == 1, us
    assert us[0][4] == [0, 1], us

    out, _ = spellings.render(text, gs, {1})
    assert out == "foo [q := y] bar", out
    out, _ = spellings.render(text, gs, {0})
    assert out == "foo [p := x] bar", out


def test_prune_falls_back_to_single_groups():
    # One unit, two groups: p can go, q must stay.
    us = [[0, 12, "head", ["p", "q"], [0, 1]]]
    written = []

    def write(keep):
        written.append(set(keep))

    def check():
        # Dropping q (group 1) breaks the namespace; dropping p is fine.
        return (1 if 1 not in written[-1] else 0, "")

    kept = spellings.prune({0, 1}, us, write, check)
    assert kept == {1}, kept
    # The whole unit was tried once, then p and q one at a time.
    assert written == [set(), {1}, set()], written


def test_prune_drops_whole_unit_first():
    us = [[0, 12, "head", ["p", "q"], [0, 1]]]
    checks = []

    def write(keep):
        checks.append(set(keep))

    def check():
        return 0, ""

    kept = spellings.prune({0, 1}, us, write, check)
    assert kept == set(), kept
    assert checks == [set()], checks


if __name__ == "__main__":
    test_render_drops_one_group_of_a_unit()
    test_prune_falls_back_to_single_groups()
    test_prune_drops_whole_unit_first()
    print("test_spellings.py: all tests passed")
