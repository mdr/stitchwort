#!/usr/bin/env python3
"""Tests for dev/test-one-bin. Run: python3 dev/test-one-bin_test.py"""
import importlib.machinery
import importlib.util
import os
import unittest

here = os.path.dirname(os.path.abspath(__file__))
loader = importlib.machinery.SourceFileLoader("test_one_bin", os.path.join(here, "test-one-bin"))
one = importlib.util.module_from_spec(importlib.util.spec_from_loader("test_one_bin", loader))
loader.exec_module(one)


class T(unittest.TestCase):
    def check(self, args, want):
        self.assertEqual(one.pick(args), want)

    def test_a_filter_naming_one_package_and_binary_picks_it(self):
        self.check(
            ["-E", "package(stitchwort-driver) & binary(projects) & test(/parallel::/)"],
            "projects",
        )
        self.check(
            ["--", "-E", "binary(projects) & package(stitchwort-driver)"],
            "projects",
        )

    def test_a_library_unit_test_filter_picks_nothing(self):
        self.check(["-E", "package(stitchwort-elab) & test(/cache::tests/)"], None)

    def test_two_binaries_pick_nothing(self):
        self.check(
            [
                "-E",
                "(package(stitchwort-cli) & binary(server)) | "
                "(package(stitchwort-driver) & binary(projects))",
            ],
            None,
        )
        self.check(["-E", "package(p) & binary(a) & binary(b)"], None)

    def test_two_packages_or_no_package_pick_nothing(self):
        self.check(["-E", "package(p) & package(q) & binary(a)"], None)
        self.check(["-E", "binary(projects) & test(/x/)"], None)

    def test_the_binary_and_package_must_be_plain(self):
        for binary in ["=projects", "~projects", "#proj*", "/proj.*/", "proj*", "proj?", "(projects)"]:
            with self.subTest(binary=binary):
                self.check(["-E", f"package(stitchwort-driver) & binary({binary})"], None)
        self.check(["-E", "package(/stitchwort-.*/) & binary(projects)"], None)

    def test_a_regex_argument_does_not_count_as_a_predicate(self):
        self.check(["-E", "package(p) & binary(a) & test(/binary(b)/)"], "a")
        self.check(["-E", "package(p) & test(/package(q)/)"], None)

    def test_filterset_spellings(self):
        self.check(["--filterset=package(p) & binary(a)"], "a")
        self.check(["-Epackage(p) & binary(a)"], "a")

    def test_several_filtersets_pick_nothing(self):
        self.check(
            ["-E", "package(p) & binary(a)", "-E", "package(p) & binary(a)"],
            None,
        )

    def test_no_filter_picks_nothing(self):
        self.check(["named_calls"], None)
        self.check([], None)


if __name__ == "__main__":
    unittest.main()
