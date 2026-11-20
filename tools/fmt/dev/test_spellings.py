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


def test_spans_keep_brackets_in_string_literals():
    # A `]` inside a string used to end the group early, so dropping the
    # group left the rest of the literal behind and the check failed.
    text = (
        '      Parse.followsMap\n'
        '        [alike := ExprsAlike]\n'
        '        [p := () => inner.expect RBracket "`,` or `]`"]\n'
        '        [q := () => inner.expect RBracket "`,` or `]`"]\n'
        '        (close => ListOf open items trailing close)'
    )
    gs, us = spellings.parse(text, {"alike", "p", "q"})
    assert [text[s:e] for s, e, _ in gs] == [
        "[alike := ExprsAlike]",
        '[p := () => inner.expect RBracket "`,` or `]`"]',
        '[q := () => inner.expect RBracket "`,` or `]`"]',
    ], gs
    assert len(us) == 1, us
    assert us[0][4] == [0, 1, 2], us

    out, _ = spellings.render(text, gs, {0})
    assert out == (
        '      Parse.followsMap\n'
        '        [alike := ExprsAlike]\n'
        '        (close => ListOf open items trailing close)'
    ), out


def test_prune_earlier_unit_drop_leaves_later_unit_intact():
    # Two units.  The first can go; deleting it must not shift or damage the
    # second, whose string also contains a `]`.
    text = (
        '  first\n'
        '    [p := "a ] b"]\n'
        '  second\n'
        '    [p := "c ] d"]\n'
        '  done'
    )
    gs, us = spellings.parse(text, {"p"})
    assert [u[4] for u in us] == [[0], [1]], us

    written = []

    def write(keep):
        out, _ = spellings.render(text, gs, keep)
        written.append((set(keep), out))

    def check():
        keep, out = written[-1]
        # The second unit is needed; the namespace also rejects text with a
        # literal cut in half.
        return (0 if 1 in keep and out.count('"') % 2 == 0 else 1, "")

    kept = spellings.prune({0, 1}, us, write, check)
    assert kept == {1}, kept
    assert spellings.kept_units(kept, us) == 1
    assert spellings.kept_units(kept, us) <= len(us)
    out, _ = spellings.render(text, gs, kept)
    assert out == (
        '  first\n'
        '  second\n'
        '    [p := "c ] d"]\n'
        '  done'
    ), out


def test_prune_drops_some_members_of_a_group_with_brackets():
    # One unit, two groups: p can go, q must stay.  Both contain a `]` in a
    # string, so each group has to be read whole.
    text = (
        '  call\n'
        '    [p := "keep ] me"]\n'
        '    [q := "drop ] me"]\n'
        '  done'
    )
    gs, us = spellings.parse(text, {"p", "q"})
    assert len(us) == 1, us
    assert us[0][4] == [0, 1], us

    written = []

    def write(keep):
        out, _ = spellings.render(text, gs, keep)
        written.append((set(keep), out))

    def check():
        keep, out = written[-1]
        # q must stay; a half-deleted literal would also be rejected.
        return (0 if 1 in keep and out.count('"') % 2 == 0 else 1, "")

    kept = spellings.prune({0, 1}, us, write, check)
    assert kept == {1}, kept
    assert spellings.kept_units(kept, us) == 1
    out, _ = spellings.render(text, gs, kept)
    assert out == (
        '  call\n'
        '    [q := "drop ] me"]\n'
        '  done'
    ), out


def test_kept_count_is_units_not_groups():
    us = [
        [0, 20, "one", ["p", "q"], [0, 1]],
        [21, 30, "two", ["p"], [2]],
    ]
    assert spellings.kept_units({0, 1, 2}, us) == 2
    assert spellings.kept_units({0, 1}, us) == 1
    assert spellings.kept_units(set(), us) == 0
    assert spellings.kept_units({0, 1, 2}, us) <= len(us)


if __name__ == "__main__":
    test_render_drops_one_group_of_a_unit()
    test_prune_falls_back_to_single_groups()
    test_prune_drops_whole_unit_first()
    test_spans_keep_brackets_in_string_literals()
    test_prune_earlier_unit_drop_leaves_later_unit_intact()
    test_prune_drops_some_members_of_a_group_with_brackets()
    test_kept_count_is_units_not_groups()
    print("test_spellings.py: all tests passed")
