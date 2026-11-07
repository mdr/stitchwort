# A mutation check: break the program, and some proof or test must notice (SW-1064)

Status: proposal, 7 Nov 2026 (Opus, by reading only: nothing was built or
run). Questions D2920-D2924 for Matt. Ticket SW-1064 (D2169, undecided).
Run times come from the tickets, `dev/measurements/` and the notes named;
where a number is my own estimate it says so.

## In short

**What it gives you.** Today a lane can finish an AoC day with every proof
checked and still have proved almost nothing about the program: a theorem
that restates the definition, or one whose hypotheses can't all hold. The
audit's vacuity warning catches some of the second kind; nothing catches the
first. Lanes check by hand, by breaking the code and seeing if a proof fails.
A mutation check does it for them. It makes small breaks in the day's code
(`<` for `≤`, `+ 1` for `+ 2`, a swapped `if`), re-checks the day's proofs and
runs its tests for each, and lists every break that nothing noticed, with the
line, the edit and, where it can find one, an input on which the broken
program gives a different answer.

**Recommendation.** Mutate the *source* of the definitions the theorems'
statements reach, and re-check each mutant in one long-lived session that
rewinds to just before the edited namespace, as the language server does
(`LiveProject`, `crates/driver/src/live.rs:1-16`). A typical AoC day re-checks
in well under a second this way, so a quick run over one day takes about
20-40 s, and a run over all of AoC about an hour on one core of this machine,
or a few hours on the old laptop: an overnight job. Stage 1, one Sonnet lane
of about 90 minutes, is `stitchwort audit --mutants` on one namespace with
token-level operators. It reports survivors and never fails anything.

## 1. The problem

**A user would hit it like this.** 2020 day 5 computes a seat ID as
`Nat.fromBits (pass.row ++ pass.column)`
(`aoc/src/Aoc/Year2020/Day05/Day05.sw:37`). Suppose a lane proves
`part1Correct` by showing that `solvePart1 passes` equals
`passes.maximumOf .seatId`. That checks. It restates the definition: change
`seatId` to read `pass.column ++ pass.row` and the theorem still checks,
because both sides use the same `seatId`. The theorem never said what a seat
ID is. (The real day's theorems go through `Spec`, which defines seats by
halving regions, `Spec/Spec.sw:11-52`, so they *do* pin it down; this is the
failure the check exists to find.)

The other common shape is a theorem with hypotheses no input satisfies. The
audit warns when the counterexample search finds no input that makes them
true (`crates/driver/src/audit.rs:229-238`), but that is evidence, not proof,
and SW-1261, SW-1304, SW-1317 and SW-1621 are all cases of the warning
firing falsely or not at all. A vacuous theorem has a second symptom: *no*
break of the program makes it fail, because its proof never looks at the
program. A mutation check sees that directly.

**What exists.**

- `stitchwort audit` (stage 1, SW-912) reports axioms, unfinished proofs and
  the vacuity warning per theorem (`crates/driver/src/audit.rs:1-15`). Stage
  2 (SW-1029, next) adds `--base` (statements unchanged against a branch)
  and `--minimal` (drop each hypothesis, re-check).
- Soundness fuzzing (SW-687, `crates/driver/tests/soundness_fuzz.rs:1-37`)
  already mutates AoC, std and examples, but it mutates *theorems*
  (statement or proof) to look for a false theorem the checker accepts. This
  note is its dual: mutate the *program*, keep the theorems, and look for a
  mutant they all still accept. MutDafny draws the same contrast
  (docs/research/infrastructure.md, C9). Its tokenizer, its site finder and
  its operator list (`soundness_fuzz.rs:100-150`, `:439-680`) are reusable.
- A proof that fails already triggers a short counterexample search
  (`ON_FAILURE`, `crates/elab/src/counterexample/mod.rs:53-57`, `:272-275`;
  D1154). So when a mutant breaks a proof, `check` already says whether the
  theorem's *statement* became false.

## 2. Designs compared

Two independent choices: what gets mutated, and how a mutant is re-checked.

### 2.1 What gets mutated

**(A) Source text, at sites chosen from the syntax tree.** Each mutant is a
text edit inside one definition's span, checked exactly as if a person had
typed it. This is how cargo-mutants (edits on `syn` spans) and mutmut (edits
on a `parso` tree) work.

- *For:* the mutant means what it says. Its proofs are re-elaborated, so a
  tactic proof (`omega`, `byDecision`, `rewrite`) adapts to the mutant as it
  would for a real edit. The report is a source diff. It reuses the whole
  pipeline, with no new trusted code.
- *Against:* some mutants don't type-check or fail the termination or
  exhaustiveness checks ("unviable"). Each costs a re-elaboration of the
  definition's namespace, tens of milliseconds (below).

**(B) Elaborated core terms.** Replace a definition's checked term with a
mutated one (`Nat.lessThan` for `Nat.lessEq`, a constant plus one, one match
arm's body for another's) and re-check, in the kernel only, the stored proof
terms of the theorems that depend on it.

- *For:* type-directed operators give no unviable mutants. Skipping
  elaboration would be roughly 3× faster: before the check cache trusted its
  hits, the kernel was 9.9 s of a 35.6 s cold AoC check
  (`docs/proposals/check-cache.md:934-943`) **[inferred from those two
  numbers]**.
- *Against, decisively:* a stored proof term was built for the original
  definition. A rewrite chain or an `omega` certificate that no longer fits
  the mutant fails in the kernel, while the same proof *text* would have
  re-elaborated fine. Every such false kill hides a survivor, and survivors
  are the point. It also needs a way to admit a changed definition and
  re-admit everything above it, near the kernel's trust boundary, and a way
  to map term positions back to source for the report.

**Recommendation: (A).** (B) is faster where speed isn't the bottleneck (§6)
and wrong in the direction that matters. mCoq, the one mature tool of this
kind for a proof assistant, also mutates the source of definitions and
re-checks the proofs (§8).

### 2.2 How a mutant is re-checked

**(i) A process per mutant**, cargo-mutants style: write the mutated file to
a scratch copy, run `stitchwort check` and `stitchwort test` on the day.
Needs no new driver code, but each run pays process start and cache replay,
a median 0.47 s for a warm `check NS` on AoC
(`dev/measurements/parallel-checking.md:148`) before any real work, which
roughly doubles a typical mutant's cost.

**(ii) A fresh in-process `Session` per mutant**, as soundness fuzzing does
(`soundness_fuzz.rs:769-866`): about a second per AoC mutant, "since their
namespace is checked again" (docs/testing.md:144). Part of that is replaying
imports from the cache.

**(iii) One session, rewound per mutant.** `LiveProject` keeps a project
checked in memory, marks the session before each namespace, and when a
file's text changes rewinds to the mark before the first changed namespace
and re-checks from there, the edited namespace's dependents included
(`live.rs:1-16`, `:503-511`, `:578-600`). Rewinding is tested equal to a
fresh check (`crates/driver/tests/projects/rewind.rs:1-17`). The library is
loaded once, before the first mark, so re-checks never pay for it:
`Aoc.Year2025.Day01` re-checks in 30 ms (`live.rs:466-469`). A mutant is
`set_text(path, mutated)`, `step` until done, read the diagnostics, run the
affected tests, then `set_text(path, original)`.

**Recommendation: (iii).** It's the language server's engine, already
differential-tested, and it is the "incremental re-checking" the per-mutant
cost needs. Two cautions for the implementation, both decided here:

- The project given to `LiveProject` should be the day's files plus what
  they import (`Aoc.Common`), not all of AoC. Otherwise everything after the
  edited namespace in canonical order is in the plan. `set_focus` and
  `set_also` order the day first (`live.rs:514-538`), but the rest would still
  be checked unless the run stops stepping.
- Mutant results must not reach the shared caches. A test result written to
  the test cache "deletes that test's other results"
  (`crates/driver/src/driver.rs:1050-1053`), so mutants would evict the real
  results. Use the in-memory test cache (`Cache { memory, .. }`, `:1054-1057`)
  and a check cache that the run reads but doesn't write.

## 3. Mutation operators

At the source level, chosen so that most mutants still type-check (the
language is total and dependently typed, so a careless operator is mostly
unviable). Stage 1 needs only tokens; stage 2 needs the syntax tree.

| Operator | Example | Stage |
|---|---|---|
| Flip a comparison | `==` ↔ `≠`, `<` ↔ `≥` | 1 |
| Shift a boundary | `<` ↔ `≤`, `>` ↔ `≥` | 1 |
| Swap arithmetic | `+` ↔ `-`, `*` ↔ `+`, `/` ↔ `%` | 1 |
| Swap a connective | `&&` ↔ `\|\|`, `∧` ↔ `∨` | 1 |
| Numeral by one | `7` → `8`, `0` → `1` (`1` → `0`) | 1 |
| Boolean constant | `True` ↔ `False` | 1 |
| Swap an `if`'s branches | `if c then a else b` → `if c then b else a` | 2 |
| Replace an arm's body | one arm returns what another arm returns, or a neighbour's value of the same type | 2 |
| Replace a body by a default | `[]`, `0`, `None`, `False`, `""` of the result type, as cargo-mutants does | 2 |
| Swap two arguments of one type | `f a b` → `f b a` | 2 |
| Drop a list element or an `..rest` | `[a, ..rest]` → `rest` | 2 |

Not used: deleting a match arm (almost always non-exhaustive, so unviable;
replacing its body tests the same thing), mutating text literals (error
messages are rarely specified, so mostly noise), and anything inside a
`decreasing` clause (unviable by design). Operators come from cargo-mutants'
and PIT's defaults, adapted to expressions; MutDafny mined some of its 40
from Dafny bug fixes (infrastructure.md, C9), which is a good source for a
later stage once there are AoC friction notes to mine.

The grep counts on AoC's code namespaces (71 files, 5,326 lines without
comments, 1,126 `def`s, `Spec`/`Proofs`/`Tests`/`Common` excluded): 272
comparisons, 346 arithmetic operators, 99 connectives, 873 numerals, 145
`if`s and 838 match arms **[checked: grep over `aoc/src/Aoc`, rough: a
numeral in a type or a string counts too]**.

## 4. Choosing sites

**Plainly:** only break code the theorems talk about. Breaking `main`'s
printing, or a helper that only a proof uses, tells you nothing about the
theorems.

**The rule.** The sites are the definitions reachable from some theorem's
*statement* (its type, not its proof), following definition bodies,
restricted to the project's own code namespaces: not std, not `Spec`,
`Proofs` or `Tests` namespaces, not definitions declared inside a proof
namespace (`letter` and `written` in `Day05/Proofs/Seat.sw:11,31` are proof
helpers). `AxiomWalk` already walks every definition a theorem reaches, with
cycles handled (`crates/driver/src/axioms.rs:1-20`); the site walk is the
same walk started from the type only and keeping definition references
rather than `Quot` nodes. SW-1029 needs the same set for its "which
definitions are the program" question, so it should be written once.

**A free by-product.** The project's code definitions that *no* theorem
statement reaches are listed as "not covered by any theorem" without making
a single mutant, as PIT reports `NO_COVERAGE`. For 2020 day 5 that would be
`main` and nothing else, if the parser's theorems reach `pass`
(`Proofs/Parse.sw:28`) **[inferred]**.

**Shared code.** A mutant of `Aoc.Common` re-checks the 57 namespaces that
import it (`parallel-checking.md:89-91`). Mutants of a shared namespace are
checked against its own `Proofs` and `Tests` first; only a survivor there
goes on to the days that use it. Common is in the batch run only (§6).

**Spec mutation, later.** Mutating the `Spec` instead of the program is
equally telling: if the spec's `part2Answers` can change and every theorem
still checks, the theorems don't connect the program to that part of the
spec. It's the same machinery with a different site set, so it's a later
stage once program mutation has been tried on AoC (D2923).

## 5. Outcomes

**What counts as killed.** Each mutant gets exactly one of these, checked in
this order:

| Outcome | Meaning | Counted |
|---|---|---|
| **unviable** | its own namespace doesn't check (a type, termination or exhaustiveness error) | no |
| **same** | the mutated definition's content hash equals the original's or an earlier mutant's (the content hash ignores names and spans, `docs/proposals/check-cache.md:44-57`) | no: it is the same program |
| **refuted** | a theorem's statement is false of the mutant: the search on its failed proof found an input (`ON_FAILURE`, D1154) | killed, by a theorem, strongly |
| **broken** | a proof stopped checking, and no counterexample was found | killed, by a theorem, weakly: the proof may only have been brittle |
| **failed a test** | every proof checks but a test fails | killed, by a test |
| **out of steps** | a check or a test ran past the mutant's step cap | neither: reported, and the run's summary says how many |
| **survived** | every proof checks and every test passes | the finding |

A survivor is a strong statement, not evidence: the theorems *have been
proved* about the mutant. The only way it is harmless is if the mutant
behaves exactly like the original (§7).

"Broken" is the weak kill. A proof by `rfl` on the real input, or one that
unfolds the definition step by step, can break on a mutant its statement
still holds for. Reporting it separately from "refuted" keeps the score
honest: a day whose kills are all "broken" has brittle proofs, not strong
statements. In a batch run, the stronger search (`ON_AUDIT`'s input count,
`counterexample/mod.rs:65-71`) runs on each broken theorem to move what it
can into "refuted".

**Determinism and limits.** The search is untimed in a mutation run
(`untimed_counterexamples`, `crates/elab/src/state/options.rs:71`), so a
run's results don't depend on load. Each mutant's step cap is a multiple of
the steps the original took (stage 4 records them). A mutant that passes it
is "out of steps", an explicit outcome: never quietly a kill or a survivor
(D2543). Stitchwort's definitions are total, so true non-termination is
rare; blowups (a mutant that makes a search exponential) are the case the
cap is for.

**Quick and full.** A quick run (a lane's, one day) stops a mutant at its
first kill, cheapest check first: affected tests, then proofs. A full run
(the batch) checks everything for every mutant, so it can say *which*
theorems kill which mutants. Within one namespace elaborating continues
past an error, so the extra cost is only in the tests and the searches.

**Per theorem.** In a full run, a theorem whose statement reaches some sites
but which kills none of their mutants gets a warning: "kills none of the 14
mutants of the definitions it mentions: it may be vacuous or restate them".
That is the restating and vacuous theorems of §1, found from the program
side, and a cross-check on the vacuity warning.

## 6. Cost on AoC

**Per mutant.** Unviable mutants cost one re-check of their own namespace:
tens of milliseconds (30 ms for 2025 day 1, `live.rs:466-469`). A viable one
costs the day's code namespace, its `Spec` if that imports the code (some
do, `parallel-checking.md:91-93`), its `Proofs` and `Tests`, and the tests
whose content hash changed (a test's hash covers what it uses,
`driver.rs:1039-1041`, so the mutant reruns only affected tests, as PIT's
coverage-based selection does, for free). From the cold AoC check (67.4 s
CPU, of which 7.3 s is the library and 39.9 s six `Proofs` namespaces,
`parallel-checking.md:94-106`), the other days' namespaces together take
about 20 s, roughly 0.4 s per day **[inferred]**. The six heavy days take
6-8 s each. Test run times per day aren't recorded anywhere I found; I
assume about 0.5 s **[guess]**.

**How many mutants.** From §3's counts, stage 1's operators give about 1,900
(two per comparison, one per other operator and numeral), and about 1,300
after site selection removes `main`, I/O and unreached code (a 70% guess).
Stage 2's operators add about 1,700. So about 20 mutants per day in stage 1
and 40 with stage 2, and a third unviable **[guess, by analogy with
cargo-mutants runs; to be measured in stage 1]**.

| Run | Mutants | Estimate |
|---|---|---|
| Quick, a typical day, stage 1 | ~20 | ~20 s |
| Quick, a typical day, stage 2 | ~40 | ~40 s |
| Quick, a heavy day (2021 day 16), stage 2 | ~40 | 1-5 min (most die on a test before the 8 s `Proofs`) |
| Full, all of AoC but Common, stage 2 | ~3,000 | ~1 h on one core here: 240 heavy-day mutants × 9 s + 1,760 × 1 s + 1,000 unviable × 0.1 s |
| Full, `Aoc.Common` (144 defs) | ~400 | 1-3 h: most stop at Common's own proofs and tests |

**On the old laptop.** Assume 2-3× slower per core **[guess]**. A session
holding one day and the library is about 150 MB (the warm worker's median,
`parallel-checking.md:159`), so four days at a time fit easily in 16 GB.
The full run is then about 1-2 hours wall, 3-5 with Common: overnight, with
a wide margin for my estimates being wrong by 3×. The run must be resumable:
it appends one JSON line per mutant and skips mutants already recorded with
the same source hash, so a laptop that sleeps loses nothing.

## 7. Equivalent mutants

**Plainly:** some breaks don't break anything. A loop's fuel of 1000 made
1001, `x * 1` made `x + 0`, or `≤` for `<` where the two values can never be
equal. Nothing *should* notice those, and a tool that keeps listing them
gets ignored.

Three layers, cheapest first:

1. **Same hash.** A mutant whose elaborated definition hashes the same as
   the original is the same program, and isn't checked further. This is
   Trivial Compiler Equivalence (compare compiled output), which in the
   mutation-testing literature removes a sizeable share of equivalent and
   duplicate mutants at no cost.
2. **A distinguishing input.** For each survivor, a full run searches for an
   input on which the original and the mutant give different results: the
   counterexample search on `original x = mutant x`, with the original kept
   under a fresh name in the mutated file. Found: the survivor is real, and
   the input goes in the report. Not found: it's listed separately as
   "probably equivalent", after the real ones.
3. **Accepted survivors.** A file in the project lists survivors judged
   equivalent, each keyed by the definition, the operator and position, and
   the definition's source hash, with a reason. A changed definition drops
   its entries, so a judgement never outlives the code it was about. I
   chose a file over an attribute in the source (mutmut's `# pragma: no
   mutate`, cargo-mutants' `#[mutants::skip]`) so that stage 3 needs no
   syntax; an attribute can come later if lanes want it next to the code.

## 8. Reporting a survivor

What makes a survivor useful is that a lane can act on it in one step:
strengthen a theorem, or add a test. So each survivor says where, what, who
didn't notice, and why it matters:

```
survived  Aoc.Year2020.Day05.Pass.seatId   Day05/Day05.sw:37
  - Nat.fromBits (pass.row ++ pass.column)
  + Nat.fromBits (pass.column ++ pass.row)
  still checked: part1Correct, part2Sound, part2Complete (they mention seatId)
  still passed:  3 tests that use it
  differs on:    pass = { row = [F,F,F,F,F,F,T], column = [F,F,F] }: 8 before, 64 after
```

(Made up, to show the shape: the real day kills this mutant with its real
input test.) Survivors come grouped by definition, real ones first, then
"probably equivalent", with a summary line per namespace: mutants made,
unviable, same, killed (refuted / broken / by a test), out of steps,
survived. `--json` gives the same per mutant, as `audit` does today. The
mutated text of each survivor is saved under `target/mutants/` (as
soundness fuzzing saves findings, `soundness_fuzz.rs:915`), so a lane can
check it by hand.

The headline number is the share of viable mutants a *theorem* kills
(refuted or broken); test kills are a second column (D2921).

## 9. Prior art

- **cargo-mutants** (Rust): source edits on function bodies (replace a body
  with a default value of its return type, swap binary operators, delete
  `!`, delete match arms), each built and tested in a scratch copy of the
  tree. Outcomes: caught, missed, unviable (doesn't build), timeout. The
  timeout is a multiple of the baseline test time. `--in-diff` mutates only
  changed lines, `--shard k/n` splits a run across machines, and results go
  in `mutants.out/` with a diff per missed mutant. docs/testing.md:157 and
  :187 already use it on the Rust crates. Borrowed here: the outcome set,
  the default-value operator, the diff-only mode (stage 4), sharding.
- **PIT** (JVM): mutates bytecode and loads each mutant into a running JVM,
  with no recompilation; runs only the tests whose coverage reaches the
  mutated line, fastest first; keeps a history file so an unchanged class
  isn't mutated again. Outcomes include KILLED, SURVIVED, NO_COVERAGE,
  TIMED_OUT. Its default operators are picked to give few equivalent
  mutants. Borrowed: coverage-based test selection (here, the content hash
  gives it), "not covered", and history (the resumable results file).
- **mutmut** (Python): source edits on a parso tree (numbers, strings,
  operators, keywords). Version 3 compiles every mutant into one copy of the
  code behind a switch chosen at run time ("mutation schemata"), so nothing
  is rebuilt per mutant. That can't work for proofs: a proof is about one
  fixed definition, not a switch. It would work for tests alone, but tests
  aren't the expensive part here.
- **Proof assistants.** *mCoq* (Celik, Palmskog, Parovic, Gallego Arias,
  Gligoric, ASE 2019) is the direct precedent: it mutates Coq definitions
  with operators taken from functional-language mutation testing, re-checks
  every proof the change could affect, and calls a mutant "live" if every
  proof still checks. Live mutants pointed to incomplete and missing
  specifications in popular Coq libraries, and it needed parallel proof
  checking to be practical on 12 projects ([ASE 2019](https://2019.ase-conferences.org/details/ase-2019-papers/90/Mutation-Analysis-for-Coq),
  [ICSE 2020 demo](https://users.ece.utexas.edu/~gligoric/papers/abstracts/JainETAL20mCoqTool.txt)).
  *MutDafny* (ICSE 2026, infrastructure.md C9) does the same for Dafny, with
  verification as the oracle, and found weak specifications at a rate of
  about one per 241 lines. Isabelle's *Mutabelle* mutates theorem
  statements to measure its counterexample finders, which is the
  soundness-fuzzing direction, not this one **[from memory]**. I know of no
  Lean or Agda tool for it. What none of them have is Stitchwort's split of
  a kill into "refuted" and "broken" from a search on the failed statement,
  and a distinguishing input for a survivor: both come from the existing
  counterexample search.

## 10. What it costs and what it rules out

- **Cost.** About five lanes in all (below). No kernel or elaborator change:
  everything is in the driver and the CLI, on top of `LiveProject`, the
  audit, the content hash and the counterexample search.
- **Rules out** the term-level design as the main path. It stays possible as
  a later fast path for a pre-filter, if the batch ever becomes too slow;
  by §6 it won't soon.
- **Doesn't do:** mutate std (its lemmas are about its own definitions; a
  later stage, same machinery), mutate tactics or the checker (that's
  `cargo mutants`), or judge whether a survivor *matters*. A survivor in
  input validation the puzzle never exercises may be fine, which is what
  the accepted list is for.

## Questions for Matt

- **D2920: Adopt the mutation check as designed here: source mutants of the
  definitions theorems mention, re-checked by rewinding one session, with
  stage 1 as below?** [rec: yes, because survivors are proved facts about
  weak theorems, which neither the vacuity warning nor review catches, and
  stage 1 is one lane with no kernel risk]
- **D2921: Is a mutant killed only by a test a pass?** The goal of D2169 is
  theorems that say something. [rec: report both, and make the headline
  the share killed by a theorem; a test-only kill is shown as "only a test
  noticed", not as a survivor, because it is still a real check, just not
  the one the day's proofs claim]
- **D2922: Advisory, or a gate?** Stage 1-3 survivors would print but never
  fail anything. Later, should a new AoC day be "done" only with no
  unexplained survivors (each killed, or accepted with a reason)?
  [rec: advisory now; decide the gate after the first full AoC run shows
  how many survivors and equivalent mutants there are, because a gate on an
  unmeasured false-positive rate would slow every day lane]
- **D2923: Should the spec be mutated too, eventually** (theorems must
  connect the program to every part of the spec), and std's definitions
  against std's lemmas? [rec: yes for `Spec` after the first full AoC run,
  std later, because it's the same machinery and catches theorems that
  ignore part of the spec]
- **D2924: Run the full AoC mutation run on the old 16 GB laptop, weekly or
  nightly, with its report filed as tickets by the orchestrator?** [rec:
  yes, weekly once stage 4 lands, because it needs hours unattended and
  nothing in the merge flow waits on it]

The command's name (`stitchwort audit --mutants`, as an audit check beside
the vacuity warning), the operator list, the outcome order, the accepted
list as a file, and the stage order are implementation decisions; I've made
them here and they can change in review.

## Tickets to file

In order. Each runs only the targeted tests named.

1. **Mutation check stage 1: `audit --mutants` on a namespace, token
   operators** (Sonnet, 90 min). Move soundness fuzzing's tokenizer into
   `crates/driver` (shared, the test keeps using it). Site walk from theorem
   statements (beside `AxiomWalk`). Operators: the stage-1 rows of §3.
   Re-check through `LiveProject` on the day's files plus imports, in-memory
   test cache, check cache read-only, untimed search. Outcomes: unviable,
   refuted, broken, failed a test, out of steps (a fixed cap for now),
   survived; quick mode (stop at first kill). Text and `--json` reports
   with the diff; "not covered by any theorem". Tests: a small project in
   `crates/cli/tests/tools/audit.rs` with one restating theorem (a survivor
   expected), one real spec theorem (all killed) and one unviable mutant;
   `task test:one -- audit`. Update `docs/syntax.md` (audit section) and the
   guide's audit page. Report the mutant counts and time on two AoC days.
2. **Stage 2: structural operators and same-hash skipping** (Sonnet, 75
   min). Syntax-tree sites: `if` branch swap, arm body replaced, body to a
   default of the result type, same-type argument swap, list element drop.
   Skip mutants whose content hash matches the original or an earlier one.
   Tests: the stage-1 project extended; `task test:one -- audit`.
3. **Stage 3: survivors explained** (Opus, 90 min: building the
   original-versus-mutant statement and searching it is the tricky part).
   Distinguishing input per survivor; "probably equivalent"; the accepted
   list keyed by source hash; full mode with per-theorem kill attribution
   and the "kills none of the mutants it mentions" warning; broken theorems
   re-searched at `ON_AUDIT`. Tests: the audit tests, plus one equivalent
   mutant (fuel + 1) that must land in "probably equivalent".
4. **Stage 4: the batch run** (Sonnet, 60 min). Whole project, workers by
   day group, step cap from each day's recorded baseline steps (as SW-1957's
   stage 2 proposes, kernel-merge-gate.md §3 (b)), resumable JSON-lines
   results, `--shard k/n`, `--changed-since REF` for a lane's own edits,
   Common's mutants checked against Common first, and a `task
   mutants:aoc` for the laptop with a summary in markdown. Tests: the audit
   tests on a two-namespace project; resuming skips recorded mutants.
5. **First full AoC run and triage** (Opus, 60 min of reading, after D2924):
   run it on the laptop, then file survivors per day as tickets and propose
   the gate (D2922).

Related, not absorbed: SW-1029 (`--minimal` drops each hypothesis and
re-checks: a statement mutation on the same per-variant engine; whichever
lands second should reuse the other's site walk and re-check loop).

Findings worth filing:

- **Soundness fuzzing's AoC mutants could rewind instead of starting a
  fresh session** (Sonnet, 45 min). `check_site` builds a new `Session` per
  mutant (`soundness_fuzz.rs:775-800`), about a second per AoC mutant;
  `LiveProject`'s rewind should make most of that go away, which would let
  the full tier take more AoC mutants for the same time **[inferred, to be
  measured]**.
- **Test results are evicted by any other result of the same test**
  (`driver.rs:1050-1053`): anything that checks variants of a program (this,
  `--minimal`, two branches alternating in one checkout) should use the
  in-memory cache, or it thrashes the real one. Worth one sentence in the
  `Cache` docs and in docs/testing.md.
