# SW-2072: is the `Effect.widenIn` prototype on `main` meant, and safe?

Read-only review, 7 Nov 2026, of `main` at `1c9aa4b86`. Nothing was built or
run; every claim below comes from reading code, history and the board.

## Summary

The prototype reached `main` deliberately. The orchestrator merged branch
`sw-424-delayed-translate` 24 Oct (`8046d40cc`), three minutes after the
PROTOTYPE commit, and its merge message records that the orchestrator itself
decided the note's three questions: "Decided by the orchestrator as internal
encoding (D1150 a, D1151 yes, D1152 note the limit)". The code on `main` is the
recommended option B, line for line as prototyped (it has since only had
mechanical refactors). It is sound by construction: `widenIn` is an ordinary
std definition by cases on the row, with no native and no kernel rule. The
kernel checks the definition and every call the elaborator builds, and the
backends compile it like any other definition. Since then other work has come
to depend on it: the empty-row specialisation of SW-407 is documented and
snapshot-tested with `widenIn` among the row eliminators, the short
`Fail.toResultMap` proof that `Parse/Reads.sw` and `Parse/Runs.sw` rewrite with,
and the `twiceThen` example. What is wrong is the paperwork, plus four items
the note said were needed "before merging it as the real change" that were
never done. **Recommendation: keep it.** Fix the note (in SW-2071), have Matt
ratify the three decisions, and add the missing tests in one small lane.

Top five:

1. Keep `widenIn`; have Matt ratify D1150 (a), D1151 (a) and D1152 (a), which
   the orchestrator decided for him (D2960).
2. Fix `delayed-translate.md`'s status line and §5, and the stale limit
   bullet in `proof-reification.md` that D1152 (a) promised to update. Fold
   both into SW-2071.
3. Add the prototype's missing tests: `lift`'s new case and its neighbours, a
   non-empty-row case where a law still applies, and an `E-STD-INTERNAL`
   reject for `widenIn` (Sonnet lane, below).
4. Check whether `pure_at_empty` (`equations.rs:5191`) should compute
   `widenIn Empty` away, as it does `doneIn`/`bindIn`/`liftIn` (same lane).
5. Make a commit marked PROTOTYPE or "not for merging" something the merge
   review has to answer for (D2961).

Findings: 0 high, 2 medium, 3 low.

## How it reached `main` (question 1)

| When (24 Oct) | Commit | What |
|---|---|---|
| (before) | `f87729a29` | Board: SW-424 filed ("design note first") |
| 15:03:57 | `626d63d56` | PROTOTYPE (SW-424) … "not for merging as is" |
| 15:06:14 | `931eb5216` | Design note `delayed-translate.md`, saying "stopped for review" |
| 15:06:47 | `8046d40cc` | Merge of `sw-424-delayed-translate` into `main`, first parent `f87729a29`; "Decided by the orchestrator as internal encoding (D1150 a, D1151 yes, D1152 note the limit)" |
| 15:13 | `b916dbb7f` | Snapshots: hashes move; generated JS calls `widenIn` |
| 15:13 | `cdaaa3224` | Board: SW-424 done, commits `626d63d5` |

So the branch was merged as a whole, the PROTOTYPE commit included, 33 seconds
after the note that calls itself "stopped for review" was committed. SW-424's
archived ticket (`board/board show 424`) has an empty body: no record of the
decisions, a review, or Matt. Nothing else on the board or in `git log --all
--grep` mentions D1150-D1152 or a later review. Every lane branch since then
contains the commit because they all start from `main`.

The workflow of the time (`docs/workflow.md` at `8046d40cc`, line 23) asked
for Matt's decision only on "a design that changes the language". The
orchestrator judged this an internal encoding: no syntax, no kernel change, no
new name a program can use. That judgement is arguable. The change does
alter which proofs check (that was its purpose), which makes it user-visible
in proofs, and the note was written with "Decisions for the owner". So D2960
asks Matt to ratify the decisions after the fact.

## Reviewed or finished afterwards? (question 2)

Not reviewed: there is no review doc, ticket or commit about it after 24 Oct.
The note's own pre-merge list (§5, last paragraph) said what "the real change"
would need. Here is each item's status on `main`:

| Item | Status |
|---|---|
| A unit test of `lift`'s new case (closed into open with the same abilities; different order; more abilities; partial) | **Not done.** `effects.rs` has no test module, and no test names the case. The examples cover the common path indirectly. |
| An example where `e` turns out non-empty and a law still applies (`Each`-style) | **Not done** as a proof. The run-time side is covered: `Each.sw`'s "abort outside each" test and the effect differential fuzzer's `Widen` atom (`crates/cli/tests/extraction/effect_differential.rs:145`), which runs nested `Fail.toResult`s on the reference evaluator, `rt` and JS. |
| A test that `widenIn` is `E-STD-INTERNAL` from a program | **Not done** for `widenIn`. It is in the internal list (`scope.rs:1026`), next to `rowOp`, which `examples/reject/row-internal-inspect.sw` tests. The mechanism is tested, this entry isn't. |
| The R1 note's limit bullet updated | **Not done.** `proof-reification.md:589-594` still says the `MapIn` proof "still splits a second time". |

The prototype lane's own test table (§5) covers elab lib, the CLI examples,
`std_library`, `ability_errors` and `empty_row_kernel`. The full gate was not
run before the merge. The tiers have run many times in the two weeks since,
but I haven't checked their logs.

## Does `main` match the decided design? (question 3)

Yes, for all three decisions as the merge message records them:

- **D1150 (a), option B.** `Effect.widenIn` (`Effect.sw:210-214`) is exactly
  the note's §4 B definition. `lift_plain` (`effects.rs:1311-1330`) uses it
  under the note's condition: not unmoved, neither row partial, `from` closed,
  `to` open, the same abilities in the same order. `widen`
  (`effects.rs:1401-1424`) builds `pre`/`preRes` as lambdas over the tail.
  The diff against `626d63d56` is only `quote` becoming `quote_folded`
  (SW-1748) and the `&Ev` and Globals refactors (SW-1190).
- **D1151 (a).** `Fail.toResultMap` (`Fail/Fail.sw:201-208`; `toResultMapIn`
  was renamed by SW-408 the same day) has the short proof.
- **D1152 (a).** Half done. No `rewrite` normalisation was built, but the
  limit was never written into `proof-reification.md` (above).

One thing the note didn't foresee: divergence indices came later (D1215,
D1254/D1255). A closed row moved into an open row that carries an index goes
through `lift`'s `(None, Some(dt))` arm, which calls `lift_plain` on the plain
rows and so still widens, then `liftD`. Two rows that both have an index go
through `translateD` and never widen. That matches §6's "what stays open";
nothing new is broken.

## What depends on it now (question 4)

- **Elaborated terms everywhere.** Every closed call written inside an
  open-row thunk now elaborates to `widenIn`: `Fail.toResult (() => …)`,
  `Abort.toOption (() => …)` and `Each.collectIn` bodies across std, examples
  and AoC. The prelude hash snapshot pins `Std.Effect.widenIn`
  (`library__hash_stability__prelude.snap:417`), and the hashes of every
  declaration with such a move include it.
- **Proofs.** `Fail.toResultMap`'s short proof (D1151) and
  `examples/accept/reify-thunk-in-proof.sw`'s `twiceThen` need it, and
  `Parse/Reads.sw:985` and `Parse/Runs.sw:843` rewrite with
  `Fail.toResultMap`. About 50 `toResultThen`/`toOptionThen` uses in std,
  36 AoC proof files and three examples use the same laws inside thunks. I
  can't tell without running which of those match only because `widenIn`
  computes away (medium confidence that some do; that is the pattern of
  §2's repro).
- **Backends.** No native: `js/src/effect.rs:97-101` and `rt/src/effect.rs:135-139`
  bind only `bind`, `foldComp`, `translate` and `runPure`. `widenIn`
  compiles as ordinary code whose `Ops` arm calls the native `translate`.
  The empty-row specialisation (`rt/src/specialise.rs:1-35`, design E, SW-407)
  inlines it at `Empty` by shape, not by name, and `effect-polymorphism.md`
  (stage 2 "As built", lines 2073 and 2153) records it as one of the row
  eliminators. Two JS extraction snapshots show it
  (`extraction__extract__effect-runtime.js.snap`, `…effect-handlers.js.snap`).
- **Native pins.** None involve `widenIn`. Editing `Effect.sw` near it could
  still shift the `translate`/`bind` pins, as for any std core edit.

## Soundness and determinism (question 5)

Nothing unchecked reaches the kernel:

- `widenIn` is a plain std definition (`Builtin::WidenIn` is a registry
  `Def`, `registry.rs:447`, used only for lookup by identity; the registry
  invariants at `registry.rs:23-26` say binding grants no native). Its first
  clause type-checks only because `rowOp Empty` computes to `NoOp`, which the
  kernel checks.
- The elaborator builds `widenIn [t] pre preRes tail m term` as an ordinary
  term. The kernel re-checks every declaration (`elab/src/lib.rs:5-7`). A
  wrong `pre`, `preRes` or `m` is a kernel type error, never an accepted
  falsehood.
- `widen`'s de Bruijn handling reads correctly: `pre`'s body is quoted at
  `level + 1` with the bound `t` as `Value::var(level)`, `preRes`'s at
  `level + 2` with `t` and `r` as `level` and `level + 1`.
- Determinism: `widens` and `widen` use only the rows' label order and
  `mapping`. No hash-ordered tables, no addresses.
- Inference risk (the note's §4 B, and `effect-rows-external-review.md`
  line 269 on non-injective stuck definitions): `widenIn ?e …` is compared
  structurally, like any stuck definition. `row_rule` special-cases only
  `CompIn`. At worst this accepts or rejects a different set of programs,
  and the kernel catches a wrong solution. No finding.

## Findings

| # | Where | What | Severity | Confidence | Fix (size) |
|---|---|---|---|---|---|
| F1 | `docs/proposals/delayed-translate.md:3-8`, §5, §7 | The status line says it is "stopped for review" and that the prototype is on a side branch. It has been on `main` since 24 Oct, with D1150-D1152 decided by the orchestrator. §5 names the branch and `toResultMapIn` (now `toResultMap`). | medium | high | Status line: "Built: merged 24 Oct (`8046d40cc`); D1150 (a), D1151 (a), D1152 (a) decided by the orchestrator, ratification D2960". Note the rename. (S, in SW-2071) |
| F2 | `effects.rs:1311-1330`, no tests | None of the prototype's required tests were added (table above). The `widens` condition (six conjuncts) is guarded only by examples that happen to pass through it. A change to `align` or `same_shape` that stopped it firing would show up only as a proof failing somewhere, or not at all if the row is never empty. | medium | high | Tests per the Sonnet lane below. (M) |
| F3 | `docs/proposals/proof-reification.md:589-594` | It still says the `MapIn` step "still splits a second time". D1152 (a) said this bullet would record §6's remaining limits (rigid tails, more abilities, another order, two divergence-indexed rows). | low | high | Replace with §6's limits and a link. (S, in SW-2071) |
| F4 | `elab/src/equations.rs:5195-5203` | `pure_at_empty`'s plumbing list (computed away in the generated per-arm equations of effect-polymorphic definitions, SW-1035) has `CompIn`, `DoneIn`, `BindIn` and `LiftIn`, but not `WidenIn`. An equation whose right side moves a closed call into the definition's own row may show `widenIn Empty m c` rather than `c`. It is equal by computation, so `rfl` is unaffected, but it is visible in goals that print the equation unreduced. Unverified: I didn't find such an equation. | low | low | Add a probe; if it shows, add `Builtin::WidenIn` to the list. (S) |
| F5 | `docs/proposals/effect-runtime.md:228` | It cites `Effect.sw:165-200` for the row helpers, which are now at `Effect.sw:184-214`. | low | high | Cite by name, not line. (S, in SW-2071) |

## Checked and sound

- The merge history and its first parent. The branch held exactly the
  prototype and the note, nothing else.
- Every arm of `lift` that reaches `widens`: plain, `(None, Some)` with
  `liftD`, `(Some, None)` and `(Some, Some)`, which never widen.
- The `widens` predicate against the note's stated condition.
- `widen`, `ops_ending` and `res_ending`: levels and argument order match
  `widenIn`'s signature (`pre`, `preRes`, row, `m`, computation).
- `widenIn` is internal (`scope.rs:1026`) and not proof-only, so programs can't name it.
- Backends: no native. Specialisation handles it by shape. The reference
  evaluator just computes the definition.
- No dependence on hash order or addresses.

## The 1 Nov review's findings in this scope

`docs/research/rust-codebase-review.md` has no finding about `lift` or
`widenIn`. Its item 12 (mechanical file splits) lists `effects.rs` at 5.0k
lines. It is now 5,231 and still open. `widen` and its helpers add about 60
lines, which would move with `lift` in any split.

## Recommendation (question 6)

**Keep it as it is, fix the note, and finish the four promised tests.**

| Option | What it takes | Cost | Risk |
|---|---|---|---|
| Keep, fix docs (recommended) | SW-2071 fold-in, plus the test lane below | ~30 min DeepSeek + ~45 min Sonnet | None new. Two weeks on `main` under the tiers, with backends and specialisation built on it. |
| Finish further (option D's normalisation, §6 cases) | A design note first | L | Nothing needs it yet (D1152). Not recommended now. |
| Take it out | Revert `lift_plain`'s `widens` arm, `widen` and its helpers, `Effect.widenIn`, `Builtin::WidenIn` and the internal entry. Restore `Fail.toResultMap`'s second split, delete `twiceThen`, re-record snapshots. Then find and repair every std/AoC proof that relied on it, an unknown number found only by a full AoC check (Matt's OK needed). Update design E's docs and the extraction snapshots. | M-L, mostly unknown proof repair | Brings back §2's `E-REWRITE-NOTHING` for every law used inside an open-row thunk. At the empty row, generated code does a `translate` tree walk that does nothing. |

## Tickets to file

- **Fold into SW-2071** (DeepSeek, adds ~15 min): F1, F3, F5. Also mark
  `docs/proposals/README.md`'s row for `delayed-translate.md` "built" rather
  than "built (stale)", and resolve its stale claim 16.
- **New lane, Sonnet, 45 min: tests for `widenIn`'s case in `lift`** (F2, F4),
  epic as for effects:
  1. `examples/reject/row-internal-widen.sw`, `E-STD-INTERNAL` for naming
     `Effect.widenIn`.
  2. Accept examples with a `goals`/`rfl` check, one per arm of the
     condition: `{Fail}` into `{Fail | e}` with `e` empty (no `widenIn` or
     `translate` left in the shown goal), `{A, B}` into `{B, A | e}`
     (`translate`), `{Fail}` into `{IO, Fail | e}` (`translate`), and an
     `Each`/`Abort` case where `e` turns out non-empty and `toOptionThen` or
     `toResultThen` still rewrites, or a comment saying it doesn't and why
     (§6).
  3. The F4 probe, and the one-line fix if it shows `widenIn Empty`.
  4. Snapshots: `task snap:hashes` for the new examples and the
     `hash_stability` test. Targeted tests only.

## Questions for Matt

**D2960. Ratify SW-424's decisions, which the orchestrator took for you on
24 Oct?** D1150 (a): move a closed computation into an open row with
`Effect.widenIn`, which is the computation itself at the empty row. D1151
(a): `Fail.toResultMap` keeps the short proof. D1152 (a): nothing now for
rigid rows or rows with more abilities; note the limit. **[rec: yes]** It is
small, sound by construction, and other work is built on it. Taking it out
would re-break the proofs it fixed.

**D2961. Should a commit marked PROTOTYPE or "not for merging" block a merge
until the merge message says how each caveat was met?** This would be one
line in `docs/workflow.md`, "Checks after a merge" or the review step.
**[rec: yes]** Here a note saying "stopped for review" and a commit saying
"not for merging" went in within three minutes, with no trace on the
ticket. The audit found it two weeks later.
