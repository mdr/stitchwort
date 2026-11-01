# Review 1 of documentation.md, draft 1

Independent review by a Claude Opus subagent with no part in the draft, 1 November 2026, of
commit `65117c21`. It was given the proposal and the repo, not the author's conclusions, and asked
to check claims against the code and assess the design. Recorded as received, lightly
reformatted; scratch-file paths left out.

**Verdict: approve with changes.** The core design is sound: attach docs by position, read them
from source when shown, attach examples by name, and rank theorems from the existing search. But
two rules would give wrong results on today's code: std file docs and the theorem scope for
project names. One evidence case quotes a comment as it stood after the incident it describes.
And several things an implementer needs are unspecified.

Checked against the worktree at `65117c21`. All three scripts re-run, reproducing the proposal's
numbers; the release CLI run for std-only queries plus one `check --index` on a two-line scratch
file.

**Confirmed:**
- **Scripts:** every count in §1.2 (1,945 / 3,635, 823 / 1,108, the aoc and roguelike rows, 47
  marked blocks) and §5.4 (181 / 594 with 123 + 58, 133 targets, 96 / 115 as 42 + 54, 129 /
  1,108). The summary figures (915, median 64, p90 139, longest 355, 44 over 160) and the 141-line
  grep also match.
- **Search runs:** `List.filterMap` is 9th of 9 and 2nd with `--definitions`. It has 22 theorems,
  which split 7 / 8 / 7 exactly as claimed. The by-hand order of the 8 in §5.3 matches search's
  (premises, size) order.
- **File:line citations:** all correct (lexer.rs, parser.rs, fmt, lsp.rs, nav.rs, search.rs,
  main.rs:503, hash.rs, check-cache.md:177-178, formatter.md, guide 06, web/index.html). So are
  the NOTES-2024 quotes, the SW-1006/D2131 account, and the commit dates for f7264e47 and
  155a64e1.
- **Absences:** no `--|` in any `.sw` file, and no Markdown crate in Cargo.lock.

1. **Must fix: std file docs go to the wrong namespaces.** §4 gives a std file's doc to every
   namespace whose declarations appear in that file. 45 of std's 90 files declare names in more
   than one namespace (regex count). `doc List` would print the file docs of 20 files, including
   core/Show.sw, core/DecEq.sw, core/Ord.sw and Text/Basics.sw; `doc Nat` would print 26.
   Change: give a std file's doc to the namespace of its folder (`List/…` to `Std.List`), with an
   explicit rule for `core/`, perhaps "no namespace doc"; or use the namespace with the most
   declarations in the file.
2. **Must fix: D2146 assumption 2 is false, so theorems would be missed silently.**
   docs/projects.md:253-254: "`N` depends on `M` if a file of `N` imports from `M` … or writes a
   qualified name that resolves into `M`". Guide 06:160 says "importing from it or writing a full
   name". A namespace that uses X only by its full name has no import line. Change: use the
   driver's own pre-check dependency graph and restate the assumption. For a widely used
   namespace such as `Aoc.Common`, "X's namespace plus everything that imports it" is most of
   aoc, so the scope saves little there.
3. **Must fix: the research note link is broken.** `docs/research/documentation.md` is not in git;
   it exists only untracked in the main checkout. Commit it or drop the link. The anchor
   `#review-1-and-how-it-was-addressed` has no target yet.
4. **Should fix: the Set.union evidence quotes a comment written after the incident (§1.3).** The
   quote "when one set, of n keys, is much smaller" is from e947353f (28 Oct 05:17); the note is
   155a64e1 (28 Oct 04:51). On 24 Oct (96b79502) the comment read "O(n log m) when `a` is much
   smaller", so the substance survives. e947353f then made both argument orders fast. Change:
   quote the 24-Oct text and add that the cost was fixed 26 minutes after the note.
5. **Should fix: the evidence the ticket names is missing.** SW-1013 says "Evidence: query log
   from SW-993"; SW-993 records "The search query log was never switched on (no log file
   anywhere)". Say so in §1.3, and rename the §1.3 heading: there is no "misused" case.
6. **Should fix: one-word exact test matches in AoC are mostly wrong (§5.4, D2144).** `test
   "example"` (4 times) and `test "square"` attach to input values (`def square: List Tile`,
   Day09/Tests/Examples.sw:32); those tests test `solvePart1`/`answers`. `test "at"`
   (Common/Tests/Grid.sw:27) tests `Grid.at` but the name resolves to `at`. Only `choices` is
   right: 1 of 7. Change: attach only to a definition with parameters, or only qualified names
   in projects; say so in D2144.
7. **Should fix: tests live in `.Tests` namespaces in projects.** Search the same namespace set as
   theorems.
8. **Should fix: 19 std `…Example` theorems would be invisible**, e.g. `List.memFilterMapExample`
   (List/Lemmas.sw:2015), a concrete example of `filterMap`; search hides them and §5.5 drops
   them, so `doc List.filterMap` prints "Examples: none". Change: list them in the coverage report
   to be renamed, or attach them by the head of their statement.
9. **Should fix: `doc` output is unspecified for most kinds and for clashing names**: types (with
   constructors and fields), interfaces, abilities, theorems, constructors, instances; a name that
   is both a type and a namespace (`List`, `Option`, `Map`); the JSON for a namespace listing and
   for several matches.
10. **Should fix: cold-cache cost, and whether `doc` needs a check.** "About 1 s" is warm; with a
    fresh `--cache-dir` the same search took 17.7 s real (7.6 s user). Doc, summary, header and
    examples need only parsing. Suggested new D: print parse-only parts at once, check only for
    theorems. Also unstated: whether `doc` picks up the enclosing project by default.
11. **Should fix: the "all N" command shows only 10** (`--limit 10` default). Print `--limit 22`.
12. **Should fix: members sharing a line (§4 rule 1)** break for one-line records,
    `type Parse.Mark = { rest: …, offset: …, left: … }` (Parse/Parse.sw:31, also 43 and 70).
    Change: such a member has no doc of its own. Also state that a comment between an attribute
    line and `def` isn't a doc (none exist today).
13. **Should fix: the summary rule doesn't match its own data.** "Followed by a space or the end"
    never fires at a line end when `Doc.text` joins with `\n`; summ.py joins with spaces. Say
    "whitespace", and don't cut inside backticks. `Text.padLeft`'s first sentence is 162
    characters, so its summary is cut mid-parenthesis.
14. **Should fix: the "timing" marker would demote user docs.** All 6 std hits are cost or
    behaviour text (Parse.sw:668, Toolkit.sw:479, Finite.sw:35 and :67, Bits.sw:350, Vec.sw:361,
    Lemmas.sw:493 "1s" meaning ones). Drop it; "47 blocks" overstates by up to 6.
15. **Should fix: links to names the file doesn't import.** Resolving as the file does means a
    link to ``[`List.filterMapAppend`]`` needs `import Std (List)`. Accept full names, and std
    names without `Std.`, regardless of imports. Consider a D question.
16. **Minor: link targets must be name-shaped.** aoc Day15/Spec/Spec.sw:40 has "its `[` is; its
    `]`".
17. **Minor: D2149 assumption 1 cites test code**, not a comment; cite Vec.sw:53 or Show.sw:81.
18. **Minor: removing `docMarker` changes a field**, needing a version bump by search.md §4.1's
    rule; keep it, reading `--|` after the pass. Say whether the index carries it.
19. **Minor: the index has a precedent for an unversioned field**: `signature`, ec84e6d2 (24 Oct).
    `signature` is also an alternative or supplement to the hand-sliced header.
20. **Minor: index cost** is larger than "what the program uses" suggests: a two-line file
    importing `List` and `Text` gave 40 std files, 1,231 symbols, 4.9 MB.
21. **Minor: theorem ranking and display.** "Contains the last component" is loose: for
    `List.map`, 66 of 121 theorems are "named after" (incl. `filterMapSome`, `toTextMap`); a
    simulation still gives a sensible top 8, but `lengthMap` misses group 1. Test on `List.map`
    and `Nat.add` (268 theorems). JSON `group` has two values for three groups. Is a congruence
    lemma exempt from the cap? Read "left side headed by X" off each statement rather than a second
    `--rewrite` search. Drop only binders used later, not named premises.
22. **Minor: docs must come from the std the check used** (`--std-dir`, `STITCHWORT_STD_DIR`).
23. **Minor: "a shown example has passed at the last merge" overstates**: the merge tier samples
    the corpus sweeps (testing.md:26).
24. **Minor: file docs during the fallback**: say whether D2142 covers file headers, and what
    happens with two header blocks (List/Toolkit.sw:1-4 and 6-22).

On honesty: apart from points 4 and 5, the evidence section is careful; it flags thin evidence
itself, and "the problem is real but modest" is a fair summary.
