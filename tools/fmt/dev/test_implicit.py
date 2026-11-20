#!/usr/bin/env python3
"""Tests for implicit.py: plain asserts, run with `python3 test_implicit.py`."""
import os
import subprocess
import sys
import tempfile
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, "implicit.py")


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(textwrap.dedent(text).lstrip("\n"))


def read(path):
    with open(path, "r", encoding="utf-8") as handle:
        return handle.read()


def run_result(root, *args, dry=False):
    cmd = [sys.executable, TOOL, "--roots", root]
    if dry:
        cmd.append("--dry-run")
    cmd.extend(args)
    return subprocess.run(cmd, capture_output=True, text=True)


def run(root, *args, dry=False):
    result = run_result(root, *args, dry=dry)
    if result.returncode != 0:
        raise AssertionError(
            "%s failed:\nstdout:\n%s\nstderr:\n%s"
            % (" ".join(result.args), result.stdout, result.stderr))
    return result


def test_main_cases():
    with tempfile.TemporaryDirectory() as root:
        path = os.path.join(root, "Demo.sw")
        write(path, """
            theorem Demo.existing [inv: Inv] (x: A) (y: B) (z: C):
                P := byComputing

            theorem Use.existing: Q := Demo.existing [inv := i] x y z

            theorem Demo.group (a b: T) (c: U): P := byComputing

            theorem Use.group: Q := Demo.group aa bb cc

            theorem Demo.record (problem: P) [inv: Inv] (state: S): R := byComputing

            theorem Use.record: W := Demo.record { at = m, rest = xs } [inv := i] st

            theorem Demo.text (left: Text) (right: Text): T := byComputing

            theorem Use.text: U := Demo.text "a -- b" right

            theorem Demo.multi (first: A) (second: B): M := byComputing

            theorem Use.multi: N := Demo.multi a (
                some
                  expression)

            theorem Demo.named (x: A) (y: B): N := byComputing

            theorem Use.named: O := Demo.named (x := a) b
            """)

        # Dry run changes nothing and prints a diff.
        before = read(path)
        result = run(root, "Demo.existing", "y", "--force", dry=True)
        assert read(path) == before, "dry run wrote the file"
        assert "--- " in result.stdout and "+++ " in result.stdout, result.stdout

        run(root, "Demo.existing", "y", "--force")
        text = read(path)
        assert ("theorem Demo.existing [inv: Inv] (x: A) [y: B] (z: C):"
                in text), text
        assert "Demo.existing [inv := i] x z" in text, text

        run(root, "Demo.group", "b", "--force")
        text = read(path)
        assert "theorem Demo.group (a: T) [b: T] (c: U):" in text, text
        assert "Demo.group aa cc" in text, text

        run(root, "Demo.record", "problem", "--force")
        text = read(path)
        assert ("theorem Demo.record [problem: P] [inv: Inv] (state: S):"
                in text), text
        assert "Demo.record [inv := i] st" in text, text
        assert "{ at = m, rest = xs }" not in text.split("Use.record")[1], text

        run(root, "Demo.text", "left", "--force")
        text = read(path)
        assert "theorem Demo.text [left: Text] (right: Text):" in text, text
        assert 'Demo.text "a -- b" right' not in text, text
        assert "Demo.text right" in text, text

        run(root, "Demo.multi", "second", "--force")
        text = read(path)
        assert "theorem Demo.multi (first: A) [second: B]:" in text, text
        assert "Demo.multi a" in text, text
        assert "some" not in text.split("Use.multi")[1], text

        run(root, "Demo.named", "x", "--force")
        text = read(path)
        assert "theorem Demo.named [x: A] (y: B):" in text, text
        assert "Demo.named [x := a] b" in text, text


def test_placeholder_argument_dropped():
    with tempfile.TemporaryDirectory() as root:
        path = os.path.join(root, "Demo.sw")
        write(path, """
            theorem Demo.place (x: A) (y: B): P := byComputing
            theorem Use.place: Q := Demo.place _ bb
            """)

        run(root, "Demo.place", "x")
        text = read(path)
        assert "theorem Demo.place [x: A] (y: B):" in text, text
        assert "Demo.place bb" in text, text


def test_real_argument_refused():
    with tempfile.TemporaryDirectory() as root:
        path = os.path.join(root, "Demo.sw")
        write(path, """
            theorem Demo.real (x: A) (y: B): P := byComputing
            theorem Use.real: Q := Demo.real aa bb
            """)

        before = read(path)
        result = run_result(root, "Demo.real", "x")
        assert result.returncode != 0, result
        assert "REAL " in result.stderr, result.stderr
        assert ":2: Demo.real slot x: aa" in result.stderr, result.stderr
        assert read(path) == before, "refused run wrote the file"


def test_real_argument_forced():
    with tempfile.TemporaryDirectory() as root:
        path = os.path.join(root, "Demo.sw")
        write(path, """
            theorem Demo.force (x: A) (y: B): P := byComputing
            theorem Use.force: Q := Demo.force aa bb
            """)

        run(root, "Demo.force", "x", "--force")
        text = read(path)
        assert "theorem Demo.force [x: A] (y: B):" in text, text
        assert "Demo.force bb" in text, text


def test_real_argument_named():
    with tempfile.TemporaryDirectory() as root:
        path = os.path.join(root, "Demo.sw")
        write(path, """
            theorem Demo.name (x: A) (y: B): P := byComputing
            theorem Use.name: Q := Demo.name aa bb

            theorem Demo.multi (first: A) (second: B): M := byComputing
            theorem Use.multi: N := Demo.multi a (
                some
                  expression)
            """)

        run(root, "Demo.name", "x", "--name-real")
        text = read(path)
        assert "theorem Demo.name [x: A] (y: B):" in text, text
        assert "Demo.name [x := aa] bb" in text, text

        run(root, "Demo.multi", "second", "--name-real")
        text = read(path)
        assert "theorem Demo.multi (first: A) [second: B]:" in text, text
        assert ("Demo.multi a [second := (\n    some\n"
                "      expression)]") in text, text


def test_symlink_dedup():
    with tempfile.TemporaryDirectory() as base:
        real = os.path.join(base, "real")
        link = os.path.join(base, "link")
        path = os.path.join(real, "Demo.sw")
        write(path, """
            theorem Sym.f (a: A) (b: B) (c: C): S := byComputing

            theorem Use.sym: T := Sym.f aa bb cc
            """)
        os.symlink(real, link)

        # The same file is reachable as real/Demo.sw and link/Demo.sw.
        run(base, "Sym.f", "a", "--force")
        text = read(path)
        assert "theorem Sym.f [a: A] (b: B) (c: C):" in text, text
        assert "Sym.f bb cc" in text, text
        assert "Sym.f cc" not in text, "the file was edited twice"


def test_from_file():
    with tempfile.TemporaryDirectory() as root:
        path = os.path.join(root, "Demo.sw")
        write(path, """
            theorem From.one (a: A) (b: B): P := byComputing
            theorem From.two (c: C) (d: D): Q := byComputing

            theorem Use.one: R := From.one aa bb
            theorem Use.two: S := From.two cc dd
            """)
        spec = os.path.join(root, "specs.txt")
        with open(spec, "w", encoding="utf-8") as handle:
            handle.write("From.one: a\n\n-- comment\nFrom.two: d\n")
        run(root, "--from-file", spec, "--force")
        text = read(path)
        assert "theorem From.one [a: A] (b: B):" in text, text
        assert "theorem From.two (c: C) [d: D]:" in text, text
        assert "From.one bb" in text, text
        assert "From.two cc" in text, text


if __name__ == "__main__":
    test_main_cases()
    test_placeholder_argument_dropped()
    test_real_argument_refused()
    test_real_argument_forced()
    test_real_argument_named()
    test_symlink_dedup()
    test_from_file()
    print("test_implicit.py: all tests passed")
