#!/usr/bin/env python3
"""Tests for dev/test-affected. Run: python3 dev/test-affected_test.py

The mapping tests run on a small made-up inventory with the real rules file;
`RealInventory` runs the table's cases on the built inventory too (skipped
when none is built)."""
import importlib.machinery
import importlib.util
import json
import os
import tempfile
import unittest

here = os.path.dirname(os.path.abspath(__file__))


def load(name):
    loader = importlib.machinery.SourceFileLoader(name, os.path.join(here, name))
    mod = importlib.util.module_from_spec(importlib.util.spec_from_loader(name, loader))
    loader.exec_module(mod)
    return mod


ta = load("test-affected")
ta.TEST_NAMES["enabled"] = False
inv_mod = ta.load_inventory_module()
CFG = ta.load_rules(os.path.join(here, "test-affected.toml"))
PROFILES = ta.profile_filters(os.path.join(here, "..", ".config", "nextest.toml"))


def test(binary, name, time=1.0, package=None, profiles=()):
    package = package or ("stitchwort-" + binary.split("::")[0].replace("stitchwort-", ""))
    bid = binary if binary.startswith("stitchwort-") else "stitchwort-" + binary
    return {"id": "%s %s" % (bid, name), "package": package, "binary": bid, "name": name,
            "profiles": list(profiles), "group": None, "time": time, "time_known": True}


INV = [
    test("core", "kernel_ok", 1),
    test("syntax", "parses", 1),
    test("cli::aoc_answers", "year2024_day04", 1),
    test("cli::aoc_answers", "year2024_day07", 1),
    test("cli::aoc_answers", "year2021_day01", 1),
    test("elab", "omega_search::tests::budget", 1),
    test("elab", "unify::tests::other", 1, profiles=["lane-elab"]),
    test("driver::search_at", "premises_are_filled_by_omega", 1),
    test("driver::hash_stability", "prelude", 30),
    test("driver::hash_stability", "examples", 30),
    test("driver::hash_stability", "projects", 30),
    test("driver::pinned_hashes", "pins", 3),
    test("driver::std_library", "the_standard_library_passes_its_own_tests", 20),
    test("driver::std_library", "a_cycle", 1, profiles=["lane-std"]),
    test("cli::examples", "accepted_examples_check", 40),
    test("cli::examples", "rejected_examples_fail_for_the_expected_reason", 25),
    test("cli::fmt", "the_repository_sources_are_formatted", 18),
    test("cli::build", "the_roguelike_plays_as_it_does_under_run", 5),
    test("cli::lsp", "hover", 2, profiles=["lane-lsp"]),
    test("cli::lsp", "heavy_one", 200),
    test("cli::extract", "int_is_bound_to_the_prelude", 20),
    test("web", "tests::escapes_json_strings", 0.1, profiles=["lane-web"]),
]


def pick(paths, budget=90.0, inv=INV, names=("abort.sw", "omega-basic.sw", "match-x.sw")):
    notes = []
    res = ta.select(list(paths), CFG, inv_mod, inv, budget, notes, use_crate_graph=False, names=list(names))
    return res, notes


def ids_of(res):
    return {i.split(" ", 1)[1] for i in res["ids"]}


class Globs(unittest.TestCase):
    def test_star_stays_in_a_folder_and_double_star_crosses(self):
        cases = [
            ("crates/elab/src/omega*.rs", "crates/elab/src/omega_search.rs", True),
            ("crates/elab/src/omega*.rs", "crates/elab/src/omega/x.rs", False),
            ("crates/elab/src/std/**", "crates/elab/src/std/List/List.sw", True),
            ("**/*.sw", "top.sw", True),
            ("**/*.sw", "a/b/c.sw", True),
            ("docs/**", "docs/a/b.md", True),
            ("docs/**", "board/a.md", False),
        ]
        for pattern, path, want in cases:
            with self.subTest(pattern=pattern, path=path):
                self.assertEqual(ta.globs_match([pattern], path), want)


class Render(unittest.TestCase):
    def test_selectors_render_as_nextest_filtersets(self):
        cases = [
            ({"package": "core"}, "package(stitchwort-core)"),
            ({"package": "elab", "lib": True}, "(package(stitchwort-elab) & kind(lib))"),
            ({"binary": "aoc_answers", "test": "^year2024_day04$"}, "(binary(aoc_answers) & test(=year2024_day04))"),
            ({"test": "omega"}, "test(/omega/)"),
            ({"package": "cli", "binary": "fmt", "not_test": "^x$"}, "(package(stitchwort-cli) & binary(fmt) & !test(=x))"),
        ]
        for sel, want in cases:
            with self.subTest(sel=sel):
                self.assertEqual(ta.render_selector(sel, PROFILES), want)

    def test_a_profile_is_pasted_in_whole(self):
        self.assertEqual(ta.render_selector({"profile": "lane-syntax"}, PROFILES), "(package(stitchwort-syntax))")


class Mapping(unittest.TestCase):
    """Changed paths to the tests they must pick (and some they must not)."""

    TABLE = [
        ("crates/elab/src/omega.rs", {"omega_search::tests::budget", "premises_are_filled_by_omega"}, {"hover"}),
        ("crates/elab/src/omega_search.rs", {"omega_search::tests::budget"}, {"the_standard_library_passes_its_own_tests"}),
        ("crates/elab/src/std/List/List.sw",
         {"a_cycle", "the_standard_library_passes_its_own_tests", "prelude", "examples", "pins",
          "the_repository_sources_are_formatted"}, {"hover", "year2021_day01"}),
        ("crates/elab/src/std/core/Nat.sw", {"int_is_bound_to_the_prelude", "prelude"}, set()),
        ("aoc/src/Aoc/Year2024/Day07/Part1.sw", {"year2024_day07", "year2024_day04"}, {"year2021_day01"}),
        ("games/rogue/src/Rogue/Map.sw", {"the_roguelike_plays_as_it_does_under_run"}, {"hover"}),
        ("crates/lsp/src/lib.rs", {"hover"}, {"heavy_one"}),
        ("crates/syntax/src/lexer.rs", {"parses", "hover"}, {"year2021_day01"}),
        ("crates/cli/tests/snapshots/examples__reject__abort.snap", {"rejected_examples_fail_for_the_expected_reason"}, {"hover"}),
        ("examples/accept/abort.sw", {"accepted_examples_check", "examples", "the_repository_sources_are_formatted"}, {"hover"}),
    ]

    def test_table(self):
        for path, want, unwanted in self.TABLE:
            with self.subTest(path=path):
                res, _ = pick([path])
                got = ids_of(res)
                self.assertTrue(want <= got, "missing %s" % (want - got))
                self.assertFalse(unwanted & got, "unexpected %s" % (unwanted & got))

    def test_docs_only_selects_nothing_to_run(self):
        self.assertTrue(all(ta.globs_match(CFG["ignore"], f) for f in ["docs/testing.md", "board/tickets.json", "README.md"]))

    def test_the_fixed_core_is_always_in(self):
        res, _ = pick(["crates/js/src/x.rs"])
        self.assertTrue({"kernel_ok", "parses", "year2024_day04"} <= ids_of(res))

    def test_a_narrow_rule_takes_its_file_out_of_the_broad_one(self):
        res, _ = pick(["crates/elab/src/omega.rs"])
        self.assertNotIn("elab-general", [r.id for r in res["rules"]])
        res, _ = pick(["crates/elab/src/unify.rs"])
        self.assertIn("elab-general", [r.id for r in res["rules"]])

    def test_a_test_binary_is_its_own_rule(self):
        res, _ = pick(["crates/driver/tests/pinned_hashes.rs"])
        self.assertIn("pins", ids_of(res))


class Examples(unittest.TestCase):
    def test_a_changed_example_narrows_the_sweeps(self):
        res, _ = pick(["examples/accept/abort.sw"])
        self.assertEqual(res["examples"], "abort")

    def test_a_part_that_names_no_example_is_dropped(self):
        res, notes = pick(["crates/elab/src/omega.rs"], names=["abort.sw"])
        self.assertIsNone(res["examples"])
        self.assertTrue(any("matches no example" in n for n in notes))

    def test_a_rule_that_needs_the_sample_keeps_examples_unset(self):
        res, notes = pick(["examples/accept/abort.sw", "crates/elab/src/std/List/List.sw"])
        self.assertIsNone(res["examples"])
        self.assertTrue(any("left unset" in n for n in notes))


class Budget(unittest.TestCase):
    def test_over_budget_cuts_the_least_relevant_rules_first_and_says_so(self):
        res, _ = pick(["crates/elab/src/std/List/List.sw"], budget=35)
        cut = [r.id for r, _ in res["cut"]]
        self.assertTrue(cut)
        self.assertNotIn("std", cut, "the direct tests are cut last")
        self.assertLessEqual(res["estimate"]["estimate"], 40)

    def test_under_budget_cuts_nothing(self):
        res, _ = pick(["crates/elab/src/std/List/List.sw"], budget=1000)
        self.assertEqual(res["cut"], [])

    def test_the_fixed_core_is_never_cut(self):
        res, _ = pick(["crates/elab/src/std/List/List.sw"], budget=1)
        self.assertIn("fixed-core", [r.id for r in res["rules"]])

    def test_the_estimate_counts_sweeps_one_at_a_time(self):
        inv = [dict(t, group="corpus-sweeps") if t["name"] in ("examples", "prelude") else t for t in INV]
        res, _ = pick(["crates/elab/src/std/List/List.sw"], inv=inv, budget=1000)
        self.assertGreaterEqual(res["estimate"]["estimate"], 60)


class ChangedTestFile(unittest.TestCase):
    """A diff of crates/lsp/tests/features.rs (SW-1760)."""
    LSP = [test("lsp::features", "quick_one", 2, package="stitchwort-lsp"),
           test("lsp::features", "slow_one", 60, package="stitchwort-lsp"),
           test("lsp::memory", "other", 9, package="stitchwort-lsp")]

    def run_with(self, names):
        old = ta.changed_test_names, dict(ta.TEST_NAMES)
        ta.changed_test_names = lambda path, range_: names
        ta.TEST_NAMES.update(enabled=True, range=None)
        try:
            return pick(["crates/lsp/tests/features.rs"], inv=INV + self.LSP, budget=1000)
        finally:
            ta.changed_test_names = old[0]
            ta.TEST_NAMES.update(old[1])

    def test_changed_tests_come_first_and_the_rest_is_only_its_quick_tests(self):
        res, _ = self.run_with(["quick_one"])
        rules = {r.id: r for r in res["rules"]}
        self.assertEqual(rules["test-file-changed"].rank, 1)
        self.assertEqual(rules["test-file"].rank, 2)

    def test_a_changed_helper_selects_the_whole_binary_at_the_top_rank(self):
        """`cached_memory` is not a test: the diff must not leave a rule that
        selects nothing, and every test of the file may be affected."""
        res, notes = self.run_with(["cached_memory"])
        rules = {r.id: r for r in res["rules"]}
        self.assertNotIn("test-file-changed", rules)
        self.assertEqual(rules["test-file"].rank, 1)
        self.assertFalse(rules["test-file"].cheap_only)
        self.assertIn("slow_one", ids_of(res))
        self.assertEqual(res["empty"], [])
        self.assertFalse([n for n in notes if "selects no test" in n])

    def test_an_empty_rule_is_reported_for_the_refresh(self):
        res, _ = pick(["crates/lsp/tests/features.rs"], inv=INV, budget=1000)
        self.assertIn("test-file", res["empty"])


class SelectorLogFiles(unittest.TestCase):
    def test_the_log_and_gitattributes_select_nothing(self):
        for f in ("dev/selector-log.tsv", ".gitattributes"):
            self.assertTrue(ta.globs_match(CFG.get("ignore", []), f), f)

    def test_run_selected_logs_only_in_the_main_checkout(self):
        import subprocess
        text = open(os.path.join(here, "run-selected")).read()
        self.assertIn("--git-common-dir", text)
        self.assertIn('[ "$main_checkout" = 1 ]', text)
        # The test the script applies: a linked worktree's git dir is not the common one.
        r = subprocess.run(["git", "rev-parse", "--path-format=absolute", "--git-dir", "--git-common-dir"],
                           cwd=here, capture_output=True, text=True)
        gitdir, common = r.stdout.split()
        linked = "/worktrees/" in gitdir
        self.assertEqual(gitdir != common, linked)


class Quoting(unittest.TestCase):
    def test_a_filter_with_spaces_and_regexes_survives_the_task_pipeline(self):
        """The filter goes to `task test:selected` as one argv element, never
        through a shell string."""
        flt = "package(stitchwort-core) | (binary(x) & test(/^(a|b c)$/))"
        import subprocess
        out = subprocess.run(["python3", "-c", "import sys; print(sys.argv[1])", flt], capture_output=True, text=True).stdout.strip()
        self.assertEqual(out, flt)


def real_inventory_path():
    try:
        return ta.find_inventory(os.environ.get("TEST_INVENTORY"))
    except SystemExit:
        return None


@unittest.skipUnless(real_inventory_path(), "no built inventory")
class RealInventory(unittest.TestCase):
    def test_every_rule_with_a_table_entry_selects_something(self):
        inv = json.load(open(real_inventory_path()))["tests"]
        for rule in CFG["rule"]:
            if not rule.get("select"):
                continue
            r = ta.Rule(rule, [])
            with self.subTest(rule=rule["id"]):
                self.assertTrue(ta.tests_of(r, inv), "%s selects no test" % rule["id"])


# Test binaries that no rule and no lane area reaches, with why. Everything
# else must be reached by some rule of dev/test-affected.toml or a lane area
# (`EveryBinaryIsReached`), so a new binary gets a place in the table when it
# is added, not never.
NOT_REACHED = {
    "stitchwort-bench::baseline": "check counts against the committed baseline, 145 s; run by `task bench`",
    "stitchwort-bench::repeat": "repeatability of the counts, 12 s; run by `task bench`",
    "stitchwort-cli::float_paths": "needs the playground's web/pkg bundle and skips (passes) without it; daily sets STITCHWORT_REQUIRE_WASM",
    "stitchwort-driver::fuzz_elab": "mutated-example fuzzing, 100 s; daily tier",
    "stitchwort-driver::soundness_fuzz": "soundness fuzzing, 95 s; daily tier",
    "stitchwort-driver::search_at_aoc": "`search --at` over AoC goals, 250 s; daily tier",
}


@unittest.skipUnless(real_inventory_path(), "no built inventory")
class EveryBinaryIsReached(unittest.TestCase):
    """The lane areas and the rules together run something of every test
    binary: nothing is left that only a whole tier would ever run, unless
    `NOT_REACHED` says why."""

    def reached(self, inv):
        by_binary = {}
        for t in inv:
            by_binary.setdefault(t["binary"], False)
            if any(p.startswith("lane-") for p in t["profiles"]):
                by_binary[t["binary"]] = True
        for rule in CFG["rule"]:
            # A change to the build inputs runs the merge tier, which is not a place for any one binary.
            if not rule.get("select") or rule["id"] == "build-config":
                continue
            for i in ta.tests_of(ta.Rule(rule, []), inv):
                by_binary[i.split(" ", 1)[0]] = True
        return by_binary

    def test_no_test_binary_is_left_out(self):
        inv = json.load(open(real_inventory_path()))["tests"]
        by_binary = self.reached(inv)
        missing = sorted(b for b, ok in by_binary.items() if not ok and b not in NOT_REACHED)
        self.assertEqual(missing, [], "no rule or lane area reaches these test binaries: add them to a rule in "
                         "dev/test-affected.toml (or a lane in .config/nextest.toml), or to NOT_REACHED with a reason")

    def test_the_list_of_exceptions_is_current(self):
        inv = json.load(open(real_inventory_path()))["tests"]
        by_binary = self.reached(inv)
        stale = sorted(b for b in NOT_REACHED if by_binary.get(b, False) or b not in by_binary)
        self.assertEqual(stale, [], "NOT_REACHED lists binaries that are now reached or gone")

    def test_the_inventory_has_every_binary_cargo_knows(self):
        import subprocess
        r = subprocess.run(["cargo", "metadata", "--no-deps", "--format-version", "1", "--offline"],
                           capture_output=True, text=True, cwd=os.path.join(here, ".."))
        if r.returncode != 0:
            self.skipTest("cargo metadata is not available")
        known = {t["binary"] for t in json.load(open(real_inventory_path()))["tests"]}
        targets = {p["name"] + "::" + t["name"] for p in json.loads(r.stdout)["packages"] for t in p["targets"]
                   if t["kind"] == ["test"]}
        if targets - known:
            self.skipTest("the inventory is out of date (task test:inventory): %s" % sorted(targets - known))


if __name__ == "__main__":
    unittest.main()
