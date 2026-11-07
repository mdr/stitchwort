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
    test("cli::running", "aoc_answers::year2024_day04", 1),
    test("cli::running", "aoc_answers::year2024_day07", 1),
    test("cli::running", "aoc_answers::year2021_day01", 1),
    test("elab", "omega_search::tests::budget", 1),
    test("elab", "unify::tests::other", 1, profiles=["lane-elab"]),
    test("driver::library", "search_at::premises_are_filled_by_omega", 1),
    test("driver::library", "hash_stability::prelude", 30),
    test("driver::library", "hash_stability::examples", 30),
    test("driver::library", "hash_stability::projects", 30),
    test("driver::library", "pinned_hashes::pins", 3),
    test("driver::library", "std_library::the_standard_library_passes_its_own_tests", 20),
    test("driver::library", "std_library::a_cycle", 1, profiles=["lane-std"]),
    test("cli::running", "examples::accepted_examples_check", 40),
    test("cli::running", "examples::rejected_examples_fail_for_the_expected_reason", 25),
    test("cli::tools", "fmt::the_repository_sources_are_formatted", 18),
    test("cli::running", "build::the_roguelike_plays_as_it_does_under_run", 5),
    test("cli::server", "lsp::hover", 2, profiles=["lane-lsp"]),
    test("cli::server", "lsp::heavy_one", 200),
    test("cli::extraction", "extract::int_is_bound_to_the_prelude", 20),
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
            ({"package": "cli", "binary": "running", "test": "^aoc_answers::year2024_day04$"}, "(package(stitchwort-cli) & binary(running) & test(/^aoc_answers::year2024_day04$/))"),
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
        ("crates/elab/src/omega.rs", {"omega_search::tests::budget", "search_at::premises_are_filled_by_omega"}, {"lsp::hover"}),
        ("crates/elab/src/omega_search.rs", {"omega_search::tests::budget"}, {"std_library::the_standard_library_passes_its_own_tests"}),
        ("crates/elab/src/std/List/List.sw",
         {"std_library::a_cycle", "std_library::the_standard_library_passes_its_own_tests", "hash_stability::prelude", "hash_stability::examples", "pinned_hashes::pins",
          "fmt::the_repository_sources_are_formatted"}, {"lsp::hover", "aoc_answers::year2021_day01"}),
        ("crates/elab/src/std/core/Nat.sw", {"extract::int_is_bound_to_the_prelude", "hash_stability::prelude"}, set()),
        ("aoc/src/Aoc/Year2024/Day07/Part1.sw", {"aoc_answers::year2024_day07", "aoc_answers::year2024_day04"}, {"aoc_answers::year2021_day01"}),
        ("games/rogue/src/Rogue/Map.sw", {"build::the_roguelike_plays_as_it_does_under_run"}, {"lsp::hover"}),
        ("crates/lsp/src/lib.rs", {"lsp::hover"}, {"lsp::heavy_one"}),
        ("crates/syntax/src/lexer.rs", {"parses", "lsp::hover"}, {"aoc_answers::year2021_day01"}),
        ("crates/cli/tests/running/snapshots/running__examples__reject__abort.snap", {"examples::rejected_examples_fail_for_the_expected_reason"}, {"lsp::hover"}),
        ("examples/accept/abort.sw", {"examples::accepted_examples_check", "hash_stability::examples", "fmt::the_repository_sources_are_formatted"}, {"lsp::hover"}),
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
        self.assertTrue({"kernel_ok", "parses", "aoc_answers::year2024_day04"} <= ids_of(res))

    def test_a_narrow_rule_takes_its_file_out_of_the_broad_one(self):
        res, _ = pick(["crates/elab/src/omega.rs"])
        self.assertNotIn("elab-general", [r.id for r in res["rules"]])
        res, _ = pick(["crates/elab/src/unify.rs"])
        self.assertIn("elab-general", [r.id for r in res["rules"]])

    def test_a_test_binary_is_its_own_rule(self):
        res, _ = pick(["crates/driver/tests/library/pinned_hashes.rs"])
        self.assertIn("pinned_hashes::pins", ids_of(res))


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

    def test_a_cut_never_keeps_a_rule_of_a_higher_rank_than_one_it_drops(self):
        paths = [["crates/core/src/kernel.rs"], ["crates/elab/src/std/List/List.sw"],
                 ["crates/elab/src/omega.rs", "crates/cli/src/main.rs"]]
        checked = 0
        for p in paths:
            for budget in (1, 5, 10, 20, 35, 60):
                res, _ = pick(p, budget=budget)
                for c, _ in res["cut"]:
                    for k in res["rules"]:
                        checked += 1
                        self.assertLessEqual(k.rank, c.rank, "%s cut but %s kept at %s/%s" % (c.id, k.id, p, budget))
        self.assertGreater(checked, 0)

    def test_a_cut_of_a_rank_that_does_not_move_the_estimate_still_comes_before_a_lower_rank(self):
        # guide-quotes (rank 3) is hidden behind a longer test, so dropping it
        # alone does not lower the estimate; it still goes before rank 2.
        inv = INV + [test("cli::tools", "guide::the_guide_quotes_its_examples_and_the_compiler", 2, package="stitchwort-cli"),
                     test("cli::server", "lsp::heavy_one", 200)]
        res, _ = pick(["crates/core/src/kernel.rs"], inv=inv, budget=60)
        kept = {r.id: r.rank for r in res["rules"]}
        cut = {r.id: r.rank for r, _ in res["cut"]}
        if "guide-quotes" in kept:
            self.assertFalse([i for i, rk in cut.items() if rk == 2], "rank 2 cut while guide-quotes is kept: %s" % cut)

    def test_the_changed_codes_own_tests_outlast_unrelated_ones(self):
        # The omega rule's tests cost more than the whole budget's slack, but
        # the downstream quick tests (rank 2) go first and the omega tests stay.
        inv = [dict(t) for t in INV] + [
            test("elab", "omega_big_%d" % i, 10, profiles=["lane-omega"]) for i in range(3)]
        res, _ = pick(["crates/elab/src/omega.rs"], inv=inv, budget=45)
        kept = {r.id for r in res["rules"]}
        self.assertIn("elab-omega", kept)
        self.assertFalse([r.id for r, _ in res["cut"] if r.rank == 1 and r.id not in res["trimmed"]])
        self.assertEqual(res["trimmed"], [])

    def test_when_the_changed_codes_own_tests_are_over_budget_the_cheapest_are_kept_and_the_rest_named(self):
        inv = [t for t in INV if t["name"] != "lsp::heavy_one"] + [
            test("driver::library", "search_at::omega_big", 100),
            test("elab", "ring_small", 3, profiles=["lane-rewrite"])]
        files = ["crates/elab/src/omega.rs", "crates/elab/src/ring.rs"]
        res, _ = pick(files, inv=inv, budget=30)
        kept = {r.id for r in res["rules"]}
        self.assertIn("fixed-core", kept)
        self.assertNotIn("elab-omega", kept)
        self.assertIn("elab-omega", res["trimmed"])
        self.assertEqual(res["unprotected_files"], ["crates/elab/src/omega.rs"])
        text, _ = ta.report(res, files, PROFILES, 30, False, inv)
        self.assertIn("own tests alone are over the budget", text)
        self.assertIn("crates/elab/src/omega.rs", text)

    def test_the_single_cheapest_own_rule_is_kept_even_when_it_is_over_budget(self):
        inv = INV + [test("driver::library", "search_at::omega_big", 100)]
        res, _ = pick(["crates/elab/src/omega.rs"], inv=inv, budget=5)
        self.assertIn("elab-omega", {r.id for r in res["rules"]})

    def test_under_budget_cuts_nothing(self):
        res, _ = pick(["crates/elab/src/std/List/List.sw"], budget=1000)
        self.assertEqual(res["cut"], [])

    def test_the_fixed_core_is_never_cut(self):
        res, _ = pick(["crates/elab/src/std/List/List.sw"], budget=1)
        self.assertIn("fixed-core", [r.id for r in res["rules"]])

    def test_the_estimate_counts_sweeps_one_at_a_time(self):
        inv = [dict(t, group="corpus-sweeps") if t["name"] in ("hash_stability::examples", "hash_stability::prelude") else t for t in INV]
        res, _ = pick(["crates/elab/src/std/List/List.sw"], inv=inv, budget=1000)
        self.assertGreaterEqual(res["estimate"]["estimate"], 60)


class MergeProfile(unittest.TestCase):
    def test_the_merge_filter_is_generated_from_the_lane_filters(self):
        import subprocess
        r = subprocess.run([os.path.join(here, "nextest-merge"), "--check"], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_a_stale_merge_filter_is_noticed_and_rewritten(self):
        nm = load("nextest-merge")
        text = open(nm.NEXTEST).read()
        stale = text.replace("package(stitchwort-syntax)", "package(stitchwort-syntaz)", 1)
        self.assertNotEqual(stale, text)
        self.assertEqual(nm.rewrite(stale), text)


class ChangedTestFile(unittest.TestCase):
    """A diff of crates/lsp/tests/it/features.rs (SW-1760)."""
    LSP = [test("lsp::it", "features::quick_one", 2, package="stitchwort-lsp"),
           test("lsp::it", "features::slow_one", 60, package="stitchwort-lsp"),
           test("lsp::it", "memory::other", 9, package="stitchwort-lsp")]

    def run_with(self, names):
        old = ta.changed_test_names, dict(ta.TEST_NAMES)
        ta.changed_test_names = lambda path, range_: names
        ta.TEST_NAMES.update(enabled=True, range=None)
        try:
            return pick(["crates/lsp/tests/it/features.rs"], inv=INV + self.LSP, budget=1000)
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
        self.assertIn("features::slow_one", ids_of(res))
        self.assertEqual(res["empty"], [])
        self.assertFalse([n for n in notes if "selects no test" in n])

    def test_an_empty_rule_is_reported_for_the_refresh(self):
        res, _ = pick(["crates/lsp/tests/it/features.rs"], inv=INV, budget=1000)
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
        linked = gitdir != common
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
