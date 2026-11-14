# Proposal: one postponement queue in the elaborator

**Status:** draft 3, 30 October 2026; **stages 1, 2, 3 and 6 are built** ([As built (stage
1)](#as-built-stage-1), [As built (stage 2)](#as-built-stage-2), [As built (stage
3)](#as-built-stage-3), [As built (stage 6)](#as-built-stage-6)); stage 4's second attempt is
stopped for decisions ([Stage 4, second attempt: stopped](#stage-4-second-attempt-stopped)), and the third
attempt's design is written ([Stage 4: design for the third attempt](#stage-4-design-for-the-third-attempt);
decisions D2087, D2090, D2091) and built in steps 4.0 to 4.3 ([As built (step
4.3)](#as-built-step-43): number literals wait); stage 5 removes the retry paths nothing
uses any more and keeps two that are still used ([As built (stage 5)](#as-built-stage-5)). Stage 7's
design (proof searches last; inferred literals wait, D2118) is written ([Stage 7:
design](#stage-7-design-expected-type-first-proof-searches-last); SW-988; decisions D2126 to D2130)
and built in SW-1010 ([As built (stage 7)](#as-built-stage-7)): proof searches and `rfl` as
arguments are checked last, a failed `omega` or `ring` waits as `rewrite` and `cases` do, and
inferred number literals wait; D2128's "any unsolved unknown" is left out (D2140: it hides the
failure the after-expected path needs; SW-1014 reworks that path first). Tickets SW-817 (anchor), SW-847 and SW-885; context
SW-509, SW-805, SW-896. Follows D1990 (one queue, agreed in principle), D1991 (SW-805's
field-name rule stays, as name resolution), D2012 (Matt: design for the best end state; the
cost of churn is not a criterion) and D2015 (Matt: revise after the external review). Repros,
measurements and the prototype's outputs are in [postponement/](postponement/). Three decisions
for Matt are in [§10](#10-decisions-for-matt). The reviewer's brief is
[postponement/review-brief.md](postponement/review-brief.md); the review, as received, is
[postponement/review-1.md](postponement/review-1.md).

**What changed from draft 2.** The external review approved the design with revisions. Every
point is worked in; [Review 1 and how it was addressed](#review-1-and-how-it-was-addressed) has
one row per point. In short:
- the design now starts from **eight queue invariants** ([§5.1](#51-queue-invariants)), with
  item states (waiting, running, done, failed);
- **a `.field` keeps its receiver as syntax** and elaborates it again when resumed, unless the
  unknown it waits on was made inside the receiver; this is what Stitchwort's dot calls already
  do ([§5.5](#55-the-receiver-of-a-queued-field-r1)). Measured: same outcomes and same hashes as
  keeping the term;
- **termination** is argued from the attempt sites themselves: each of the 42 snapshot sites and
  48 `transaction`/`attempt` calls has a fixed, finite list of alternatives, and the measure is
  lexicographic ([§5.7](#57-termination));
- **scoped W1 is an isolation rule**, not a heuristic ([§5.6](#56-resume-points-isolation-and-order));
- **placeholders are opaque to elaboration choices**, with the list of the 15 consumers that
  choose from a type's shape and what each does ([§5.10](#510-placeholders-filling-and-opacity-r7)).
  They stay solvable by unification until unification can wait: freezing them now breaks one
  example and four AoC proofs (new decision D2016);
- **errors**: a resumed item reports against the type now known; stuck items are reported by
  independent root, at most 3 ([§5.9](#59-stuck-items-and-errors));
- **stage 6** is now an expected follow-up, tri-state unification, with a trigger
  ([§8](#8-stage-plan)).

Labels, as in the other notes:

- **[checked: file:line]**: read in the Stitchwort source at `3d0036f8` (main, 30 October).
  Nothing under `crates/` changed since draft 2's `fcb12746` (`git log fcb12746..3d0036f8 --
  crates/` is empty), so draft 2's line numbers still hold;
- **[run]**: run on 30 October with `target/release/stitchwort` built from `fcb12746` plus the
  prototype, with the switch off (today's behaviour) unless the line says it was on;
- **[measured]**: the prototype's measurement harness of [§6](#6-what-the-single-queue-changes-today),
  draft 1's counters ([§4](#4-p1-how-often-postponement-is-needed)), or draft 3's counters
  ([§6.7](#67-draft-3-runs));
- **[cited: S]**: read in source S under [Sources](#sources), at the commit given there;
- **[inferred]**: my reasoning from checked, run or cited facts, not tested;
- **[unverified]**: believed, not confirmed.

## The short answer

- **The end state.** One queue of suspended checks per declaration. A construct that needs the
  shape of a type that is still an unknown (a record literal, `.field`, a method section, a
  number literal) doesn't fail: it leaves a placeholder unknown in the term and a queued check
  that waits on the unknown it needs (its *blocker*), as in Agda and OmniML. Queued checks are
  resumed at fixed points (the end of each application, before lifting, in the obligations
  loop, at the end of the declaration) through one ladder: resume what is unblocked, then
  obligations and rows, then defaults by priority (SW-805's field-name rule, then number
  literals), as in Lean. What is still stuck at the end is reported with the error its site
  raises today, one report per independent root ([§5](#5-the-design)).
- **Eight invariants** say what makes it correct ([§5.1](#51-queue-invariants)). The two the
  review pressed hardest:
  - a queued `.field` doesn't freeze its receiver: the receiver is undone and kept as syntax,
    unless the blocker was made inside it, and in that case the receiver was inferred with no
    expected type, as it is today;
  - a placeholder is never more than an unknown to the code around it: no choice that could
    give a different well-typed meaning is made from it before it is filled.
- **The prototype** queues record literals and `.field` on an unknown type in the main pass,
  which also turns off the catch-and-retry for them. It accepts all three ticket repros, with
  the right values at run time **[run]**. Over std, the 321 + 53 accepted and extract examples,
  the 687 reject examples, aoc and rogue it changes **[measured]**:
  - **acceptance of 1 file** with resume points scoped as recommended (2 unscoped): one
    accepted example is now rejected, because the field-name default runs after a number
    literal has already been made `Nat`. Unscoped, one reject example is also accepted; it is a
    correct program that today's order rejects;
  - **the hashes of 26 declarations** of 23,213, from 7 direct changes, none to a statement.
    Five are harmless: an `Ann` (two tests), a folded motive, a lambda's term as checked in
    place (twice). Two are **needed fixes**: a placeholder filled by reading a value back
    writes out an unfolded call, and `==` loses its specialised `Nat.decEq`. Std, rogue and the
    extract examples are unchanged;
  - **no error message** of any example that stays rejected;
  - **no AoC answer or rogue behaviour**: all 914 AoC tests and 100 rogue tests pass;
  - **CPU time**: aoc 5% faster (38.0 s to 36.0 s), the rest within noise.
- **Draft 3's runs** of the same prototype with counters added **[measured]**:
  - of 159 queued `.field`s, 131 have a variable receiver whose blocker was made before it, and
    28 a blocker made inside the receiver (19 chained `.field`s, 5 applications, 4 record
    literals). No receiver's inference defaulted a number or chose a generic dictionary;
  - queueing those 131 as syntax and elaborating them again on resume changes **no outcome and
    no hash** against keeping the term;
  - in 14 of 135 fills, unification had already solved the placeholder. Freezing placeholders
    (Lean's synthetic-opaque metavariables) breaks one example and four AoC proofs.
- **Three design facts from the prototype**, which draft 1 didn't have:
  - the queue must be drained at the end of each application, not only at the end of the
    declaration, or std fails at `Map/Spec.sw:1862`. The reason is that Stitchwort's unifier
    can't wait on a placeholder. Scoped to the application's own items, as Lean's
    `withSynthesize` is, it changes no reject example (D2014);
  - it must also be drained before lifting, or a queued literal holding a `match` breaks aoc;
  - the unifier already relies on solving placeholders early: that is why they stay solvable
    by unification until stage 6 (D2016).
- **SW-805's rule becomes a default** in the ladder. It still looks only at the field names and
  the names in scope (D1991's R1 holds). That subsumes its `held`/`last_resort` machinery
  (its 5 reruns fall to 0), and it means number literals must be defaulted in the same ladder
  at a lower priority, as Lean's `OfNat Nat` default instance is (D2013).
- **The catch-and-retry paths shrink at once**: the lambda try-then-postpone fires 9 times
  instead of 100. The 6 left in accepted code are method sections, the next kind to queue.
- **Stage plan** ([§8](#8-stage-plan)): the queue with its invariants, item states, placeholder
  table and root-grouped stuck report; record literals and `.field`; sections; numbers and the
  defaults ladder; removing the retry paths; then, as an expected follow-up, tri-state
  unification. Each stage is gated on every test, example, AoC answer and rogue test staying
  right. Hashes may change.

## 1. The problem

`E-CANNOT-INFER` stops the declaration whenever a construct needs a type that a *later* part
of the declaration would fix. Postponement exists today only for lambda and method-section
arguments within one application ([§2](#2-stitchwort-today)). Each repro below is in
[postponement/](postponement/). The output is from `stitchwort check` with the switch off
**[run]**.

**SW-817**, [sw817.sw](postponement/sw817.sw): a record literal as an argument whose type only
a later argument fixes.

```
type Tally = { enabled: Bool, total: Nat }
type Score = { enabled: Bool, total: Nat }
def step (tally: Tally) (n: Nat): Tally := …
def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total
```
```
[E-CANNOT-INFER] Error: can't tell which record type this literal is
    ╭─[ docs/proposals/postponement/sw817.sw:22:47 ]
 22 │ def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total
    │                                               ──────────────┬──────────────
    │                                                             ╰──────────────── nothing here says what type it should have
    │ Note 1: add a type annotation, as in `({ x = 0, y = 0 }: Point)`
    │ Note 2: more than one record type has exactly these fields: `Tally`, `Score`
```

AoC 2024 day 3's literal has a single record type with those fields, so SW-805's field-name
rule (merged) accepts it. `Score` is there to show what the rule leaves over.

**SW-847**, [sw847.sw](postponement/sw847.sw): a let-bound unannotated lambda over a pair,
using `.field` on a component.

```
def total (pairs: List (Nat, Item)): Nat :=
  let counted := ((index, item)) => if index < 3 then item.value else 0
  List.sumBy pairs counted
```
```
[E-CANNOT-INFER] Error: can't tell what `item` is, so can't look up `.value`
    ╭─[ docs/proposals/postponement/sw847.sw:15:55 ]
 15 │   let counted := ((index, item)) => if index < 3 then item.value else 0
    │                                                       ─────┬────
    │                                                            ╰────── its type isn't known yet here
```

The same lambda passed straight to `List.sumBy` is accepted (`inline` in the file), because
an argument is postponed.

**SW-885**, [sw885.sw](postponement/sw885.sw): a record literal with an effectful field, as an
argument (`inArgument`), a tuple part (`inTuple`), a nested field (`nested`) or an argument
whose parameter type a later argument fixes (`generic`). All four give
`[E-CANNOT-INFER] Error: can't tell which record type this literal is`, labelled "nothing here
says what type it should have", at the literal (lines 27, 29, 31, 36), with the note that
`Position` and `Size` both have these fields. The same literal as the whole body, or annotated,
is accepted.

**With the prototype on** (`STITCHWORT_QUEUE=1 STITCHWORT_QUEUE_APP=1 STITCHWORT_QUEUE_LIFT=1`,
with or without `STITCHWORT_QUEUE_SCOPED=1`) all three files print `checked …`, and copies with
tests added ([prototype/](postponement/prototype/)) compute the right values:
`total [1, 2, 3] == 6` for SW-817, `total [(0, {value = 5}), (7, {value = 9})] == 5` for SW-847,
and all four SW-885 functions run under `Parse.run` to the number they parse **[run]**. They
still do with draft 3's receiver rule ([§6.7](#67-draft-3-runs)) **[run]**.

## 2. Stitchwort today

**Argument postponement** (`check.rs:1970-2250`) **[checked]**:
- A lambda argument whose domain is unknown, with a later explicit argument, is tried in place
  under a `Snapshot`. If that fails, it is restored and checked after the later arguments.
- A method section is postponed without a try, unless a later parameter's type depends on it.
- A lambda that fails where the application's expected type is known (`late_able`), and a
  non-lambda argument that fails while its type has unknowns, are checked again after the
  application's type is compared with the expected type (`after_expected`).
- Under `retrying` (`check.rs:1874`), a failed application is elaborated a second time with
  `late_literals` on, which checks a constructor or list holding number literals last.
- Postponed items are resumed at the end of the same `apply_args_postponing`. If one fails,
  the in-place try's error is kept when both are `E-CANNOT-INFER` (`first_error`). The checked
  term replaces the placeholder in the application (`fill_placeholder`), "so that zonking
  doesn't write out an unfolded value".

**The catch-and-retry paths** a single queue is meant to remove **[checked]**:

| path | where | catches | how often, std + examples + aoc + rogue **[measured]** |
|---|---|---|---|
| lambda tried in place, postponed on failure | `check.rs`, `apply_args_postponing` | any non-fatal error | 100 (98 `E-CANNOT-INFER`) |
| lambda or argument checked after the expected type | same, `late_able` and the `snapshot` of non-lambda arguments | any non-fatal error | 67 lambdas, 166 arguments (2 `E-CANNOT-INFER`) |
| section postponed without a try | same | (no try) | 46 |
| `retrying` with `late_literals` | `check.rs:1874` | any non-fatal error | 19 |
| SW-805's `held` / `last_resort` | `records.rs:714-745`, used by `==` and comparisons (`numbers.rs:754`, `:1125`), `++` (`check.rs:3599`), `calc` (`calc.rs:95`, `:113`) | `E-CANNOT-INFER` after a held literal | 5 reruns |
| infer one side, on `E-CANNOT-INFER` infer the other | `append_tried` (`check.rs:3603-3611`), `calc` (`calc.rs:117-121`), `numbers.rs:1135` | `E-CANNOT-INFER` | (inside the above) |

The counts are firings of each path with the switch off, from counters the prototype adds
([§11](#11-the-prototype)). Only the first and last two rows are about `E-CANNOT-INFER`; the
after-expected rows are mostly `E-OMEGA`, `E-REWRITE-NOTHING` and `E-TYPE-MISMATCH`, proofs
found from a goal that only the expected type fixes.

**Where `E-CANNOT-INFER` is raised for the constructs in the tickets** **[checked]**:
- a record literal inferred, or checked against an unknown after SW-805's rule finds no single
  type (`records.rs`, `infer_literal` and `check_record`);
- `.field` on a receiver whose type is unknown (`dot.rs:457`, `find_in_view`, `Step::Unknown`);
- a method section whose argument type is unknown (`dot.rs:454`, `section_unknown_name`).

**How a dot call is elaborated today** **[checked]**, which draft 2 didn't describe and the
receiver rule of [§5.5](#55-the-receiver-of-a-queued-field-r1) rests on:
- `infer_call` (`dot.rs:1613-1640`) first tries the **prefix form**. `prefix_form`
  (`dot.rs:1143-1238`) infers the receiver once, only to find the namespace, and **undoes that
  inference** (`dot.rs:1166-1174`). The call is then elaborated as the prefix call
  `T.f recv args`, where the receiver is *checked* against `T.f`'s receiver parameter (SW-129).
  The namespace found is cached by call (`dot_heads`).
- Only where the prefix form doesn't apply, or fails non-fatally (then restored,
  `dot.rs:1628-1636`), does `infer_dot` (`dot.rs:267-302`) elaborate the receiver for keeps: it
  is *inferred*, with no expected type (`infer_receiver`, `dot.rs:316-322`), its leading
  implicit arguments are inserted (`insert`, `dot.rs:279`, `check.rs:2843`), its written type
  is read (`written_type`, `dot.rs:182`), the namespace is found (`find_in_view`,
  `dot.rs:443`), and the receiver is put in its parameter's place (`call`, `dot.rs:1240`).
- A prefix form that failed is not tried again in the same metavariable state:
  `mark_failed`/`has_failed` key it by the call and the lengths of the metavariable table and
  trail (`dot.rs:1656-1670`).

**Let.** `pure_let` (`effects.rs`) infers an unannotated value first, then checks the body with
the name as a transparent `let`. A let-bound lambda's parameter types are unknowns that the
body's uses can solve (SW-509, `settle_let_lambda`; reported from `parameter_metas` at zonk).
SW-847 fails before that point: `.value` is looked up while the value is inferred.

**Effects (SW-885).** In a computation, a call's effectful arguments run first, each bound to a
fresh variable (`comp_app`). `run_argument` passes the parameter's type on only for a decided
proposition; everything else goes to `run_first`, which calls `comp_infer`. `comp_compound`
runs a tuple's, record's or list's parts the same way. So a literal with an effectful field
reaches `infer_literal` as a pure literal over bound variables. The prototype's trace shows
exactly one queued literal per SW-885 case, each resumed **[run]**.

**The unifier's put-aside pairs (SW-896).** `unify::run` (`unify.rs:30-80`) puts aside a pair
that fails while one side is blocked on an unknown. It compares the pair again after the rest
of the same call, only if the rest solved something. Nothing outlives the call: the result is
`true` or `false`, and callers branch on it.

**Opaque unknowns already exist** **[checked]**. `Globals::frozen_metas` (`globals.rs:427-432`)
are unknowns "unification never solves, so each is equal only to itself" (`unify.rs:278`,
`:413`, `:590`, `:737`). Two things use them: a lifted `match` or local definition before its
helper exists (`lift.rs:6-9`), and a goal hole `?` (`goals.rs:3-6`). For the first,
`Globals::lifted_calls` (`globals.rs:433-438`) records the call that solves it, and zonking puts
that term in "instead of reading the solution value back, which would write out what the
arguments of the call unfold to" (`lift.rs:661-666`, `unify.rs:1719-1727`). That is exactly
what a placeholder needs at its fill ([§5.10](#510-placeholders-filling-and-opacity-r7)).

**Other declaration-level waiting** **[checked]**:
- obligations (instances) wait and are retried in rounds (`solve_obligations_until_stuck`,
  `auto.rs:100`);
- row comparisons that can't be decided are kept with their context and retried in that loop
  (`rows.rs`, `retry_rows`);
- `finish` (`lib.rs:1088`) compares awaited helpers, runs that loop, settles rows and zonks;
- `Snapshot` (`undo.rs`) records the length of each per-declaration table, and `restore`
  truncates them;
- `with_local_retries` (`lib.rs:2270`) re-runs a failing declaration body after admitting
  local definitions.

## 3. How other systems do it

Every row comes from source files fetched with `gh api` on 30 October 2026, or from the
OmniML paper's full text. Commits and URLs are under [Sources](#sources).

| | What is postponed | Where it lives | When resumed, in what order, how it stops | Still stuck at the end | Errors |
|---|---|---|---|---|---|
| **Lean 4** | Any term elaborator that calls `tryPostpone…`: structure instances, `.field` on an unknown type, anonymous constructors, `elab_as_elim` minor premises. Not `fun`. | A synthetic metavariable of kind `.postponed (SavedContext)`, listed in `pendingMVars`, created `syntheticOpaque`. The local context is the metavariable's own. | `synthesizeSyntheticMVars`: steps in creation order while one makes progress. Then, in order, retry with postponing off (errors postponed), default instances (by priority, numerals' `OfNat Nat` at low priority), retry with postponing off (errors reported), tactics. Runs at the end of each definition and at nested `withSynthesize` points, which handle only what was created inside them. | Can't stay stuck. The last retry runs with postponing off, so the elaborator commits or fails. For `.postponed`, `reportStuckSyntheticMVar` is `unreachable!`. | Logged at the postponed syntax (`withRef stx`), against the metavariable's type as now known. The term becomes `sorry` and elaboration goes on. |
| **Agda** | A `TypeCheckingProblem`: `CheckExpr`, `CheckArgs` (the remaining arguments), `CheckProjAppToKnownPrincipalArg`, `CheckLambda`, `DisambiguateConstructor`, `DoQuoteTerm`. Sites include a record expression with several candidate types, a record update, a check blocked on a pattern, and some lambdas. | A metavariable instantiated as `PostponedTypeCheckingProblem (Closure …)`, plus an `UnBlock` constraint with a `Blocker`, in the type checker's constraint lists. Unification constraints sit in the same lists. | Woken when a blocking metavariable is solved (`wakeupConstraints`), then solved one at a time from the awake list. At a declaration's end: wake all, solve sizes, wake again, freeze the metavariables. | Left as constraints. At the end of the module they become the warning `UnsolvedConstraints`, an error in batch mode. There is no defaulting. | Each constraint is printed with its range. Postponed type-checking problems are filtered out as "not interesting", except constructor disambiguation. |
| **Idris 2** | Elaborators wrapped in `delayOnFailure` (try first, postpone on a matching error) or `delayElab`, with reasons `CaseBlock`, `Ambiguity`, `LazyDelay`, `RecordUpdate`, `Rewrite`. | `delayedElab` in the unifier state: a closed elaborator per hole, with the local hints. It is saved and restored around each `elabTermSub`. | At the end of `elabTermSub`, sorted by reason. Retries keeping recoverable errors repeat while some succeed, with constraint solving in between. Then a pass that reports all errors. Then default and last-chance constraint solving. | Errors. | The delayed elaborator's own error, at its own location. In the last pass it tries the later ones too, and prefers a non-generic error. |
| **Rocq** | No syntax, except within one application: the arguments after a user-written bidirectionality hint `&`, when an expected type is given, plus `Program`'s constructor parameters. Unification problems are postponed. | `conv_pbs` in the evar map. | `solve_unif_constraints_with_heuristics` retries stuck problems while one makes progress. It is called from `solve_remaining_evars_from` after type classes and hooks. | `error_cannot_unify` or `error_unsolvable_implicit`. | At the problem's or evar's recorded location. |
| **OmniML** | Any construct that needs a type's shape, as a suspended `match` constraint: record labels, polytypes. | A wait list on each unification variable, flushed into a global scheduler when that variable is unified. | Any order: the meaning doesn't depend on it. | "A match constraint that is never discharged is considered unsatisfiable". Defaults aren't formalised; the prototype can attach one. | The prototype has basic reporting only, "attaching source locations to constraints". |

**Lean 4** [cited: L1-L7].
- **Postponement is an exception.** When `mayPostpone` is set, an elaborator throws
  `Exception.postpone` (`tryPostpone`, `TermElabM.lean:1374-1415`). `elabUsingElabFnsAux`
  catches it, **restores the state saved before the elaborator ran**, and registers the syntax
  (`:1678-1701`, `postponeElabTermCore` at `:1456-1460`). The comment explains the restore:
  in `((f.x a1).x a2).x a3` each `.x` postpones in turn, and without it "dead" metavariables
  would stay on the pending list.
- **The placeholder is synthetic opaque.** `postponeElabTermCore` makes it with
  `mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque` (`TermElabM.lean:1458`), so
  ordinary unification doesn't assign it [cited for the line; the `isDefEq` behaviour is from
  Lean's documentation of metavariable kinds, unverified in source here].
- **Resuming.** `resumePostponed` (`SyntheticMVars.lean:32-77`) takes `saveState` again,
  re-elaborates under `withRef stx` against `instantiateMVars mvarDecl.type`, and on
  postpone or error (when `postponeOnError`) restores and reports no progress.
- **The ladder** is `synthesizeSyntheticMVars` (`:638-672`): `filterRevM` keeps creation order.
  The definition-level call is `synthesizeSyntheticMVarsNoPostponing` (`MutualDef.lean:1403`).
- **Scoped resume points.** `withSynthesize` and `withSynthesizeLight` save `pendingMVars`, set
  it to `[]`, run their argument, synthesize, and put the saved ones back
  (`SyntheticMVars.lean:689-720`). So an inner resume point handles only what was postponed
  inside it.
- **Defaults** (`synthesizeUsingDefault`, `:237-243`) go through the priorities in descending
  order and stop at the first default that applies; the ladder then starts again. The numeral
  default `instOfNatNat` is `@[default_instance 100] /- low prio -/` (`Prelude.lean:1411-1413`),
  so a number literal's type is decided late, at low priority, not at the literal.
- **Postponing sites**: structure instances (`StructInst.lean:1357-1365`); dot notation
  (`resolveLValLoop`, `App.lean:1678-1694`); `elab_as_elim` minor premises (`App.lean:1314`).
  `fun` elaborates its body at once (`Binders.lean:678`).
- **Body-first `let`.** `let_delayed` (`Binders.lean:951-952`) elaborates the value after the
  body, with the value an unknown meanwhile (`:779-782`, `:848-856`).
- **Pitfalls named in the code:** the order-dependence of turning postponing off ("we are
  essentially giving up the opportunity of learning `x`s type", `SyntheticMVars.lean:646-659`);
  long unfolding against synthetic-opaque metavariables left in a `let`'s type, issue #4051
  (`Binders.lean:754-773`).

**Agda** [cited: A1-A8].
- **Postponing.** `postponeTypeCheckingProblem` (`MetaVars.hs:629-661`) creates a metavariable
  whose instantiation is the closure of the problem, an alias metavariable that it returns, and
  an `UnBlock m` constraint under the blocker.
- **Waking.** `wakeupConstraints x` wakes the constraints blocked on the solved metavariable `x`
  and solves the awake ones (`Constraints.hs:246-251`). `solveConstraint_ (UnBlock m)` enters
  the closure, runs `checkTypeCheckingProblem`, and assigns the result (`:300-326`, `:344-352`).
- **At a declaration's end**: `Decl.hs:226-240`.
- **Record literals.** `checkRecordExpression` at a blocked type calls `guessRecordType`
  (`Term.hs:1118-1123`). It finds every record type in scope with *at least* the given fields
  (`findPossibleRecords`, `Records.hs:219-235`): none, error; one, commit; more, postpone
  (`Term.hs:1177-1215`). So Agda's name rule runs *before* the queue.
- **Projections.** `CheckProjAppToKnownPrincipalArg` keeps the principal argument's value and
  type, so that argument isn't checked again (`Application.hs:1440-1476`).
- **Stuck at the end.** These become `UnsolvedConstraints` (`Pretty/Warning.hs:988-1004`), but
  `interestingConstraint` drops postponed type-checking problems other than constructor
  disambiguation (`Pretty/Constraint.hs:42-51`).
- **Pitfall.** A comment calls committing to a function type for an untyped lambda "hazardous"
  (implicit lambdas, modalities; `Term.hs:591-606`).

**Idris 2** [cited: I1-I4].
- **The queue.** `delayOnFailure` and `delayElab` (`TTImp/Elab/Delayed.idr`) push a closed
  elaborator, built by `mkClosedElab` over the environment, onto `delayedElab`
  (`Core/UnifyState.idr:102-107`).
- **The order** of the reasons was "chosen to give the most likely useful error messages
  first" (`UnifyState.idr:65-77`).
- **Resuming.** `retryDelayed` repeats while there is progress, then reruns with `AllErrors`.
  It is called from `elabTermSub`, sorted by reason (`TTImp/Elab.idr:110-148`).
- **No restore.** `delayOnFailure` runs the elaborator first and postpones on a matching error;
  there is no restore in `Delayed.idr` **[inferred]**.
- **Record updates** are delayed this way (`TTImp/Elab/Record.idr:244-259`).

**Rocq** [cited: R1-R4].
- **Bidirectionality hints** (`pretyping.ml:1057-1120`, `:1181-1201`): when an expected type is
  given, the arguments after the hint are evars; the application is coerced to the expected
  type, then those arguments are pretyped against their refined types. This is Stitchwort's
  `after_expected` with the cut point written by the user.
- **Unification problems.** `solve_unif_constraints_with_heuristics` (`evarconv.ml:2087-2121`)
  and `check_problems_are_solved` (`:2044-2047`) handle the postponed problems.
- **Record syntax** `{| f := … |}` is resolved by its first field's name during
  internalisation (`constrintern.ml:1576-1581`), so a record literal never waits on a type.

**OmniML** [cited: O1].
- **Suspension** (§2.4, formalised in §4.1, implemented with wait lists and a scheduler in §6).
- **Records.** §3.2's closed-world rule: the labels "exactly match" one record type's; it
  "depend[s] only on the global label environment". That is SW-805's rule.
- **Defaults** are left out ("No defaults, by default", §2.5).
- **Errors** (§7): suspended constraints "do not fundamentally complicate error reporting".

**What the single-pass design takes from each** [inferred]:
1. **From Agda and OmniML: items wait on an unknown.** An item names its blocker and is woken
   when that is solved, instead of every item being retried (Lean, Idris, Rocq). This gives the
   order and keeps the cost per resume point to the items that can move.
2. **From Lean: the ladder, the defaults, and scoped resume points.** One loop resumes,
   solves obligations, applies one default by priority, and goes round again. Number literals
   are defaulted in it at low priority, not at the literal. An inner resume point handles only
   what was created inside it.
3. **Not from Lean or Agda: resume inside the unifier.** Lean's `isDefEq` and Agda's
   constraint solver can leave a comparison stuck on a metavariable and come back to it.
   Stitchwort's unifier answers `true` or `false` at once (SW-896's put-aside pairs live only
   inside one call). So placeholders must be filled before the comparisons that need them,
   which is why the end of every application is a resume point
   ([§5.6](#56-resume-points-isolation-and-order)). The prototype shows this is enough for the
   corpus; the review is right that it isn't a general substitute ([§5.13](#513-the-unifier-and-placeholders-r4)).
4. **From Lean, not Agda: re-elaborate the receiver.** A queued `.field` undoes its receiver
   and keeps the syntax, as Lean's restore does and as Stitchwort's prefix form already does
   ([§5.5](#55-the-receiver-of-a-queued-field-r1)). Agda's kept principal argument is used only
   where the receiver itself made the unknown it waits on.
5. **From OmniML, the ideal; from Lean, the reality.** OmniML's order doesn't matter; ours
   does, through defaults and through `true`/`false` unification. Creation order plus priorities
   makes it deterministic, as in Lean.

## 4. P1: how often postponement is needed

Draft 1's counters (dropped; [postponement/p1-counters.patch](postponement/p1-counters.patch),
output in [postponement/p1-counts.txt](postponement/p1-counts.txt)) **[measured]**:
- postponement already fires in about 1 in 1,000 arguments in std (86 of 57,889) and 3 in 1,000
  in aoc (273 of 89,559); about 2% of lambda arguments are postponed;
- the sites a queue replaces raise and recover `E-CANNOT-INFER` **1,073 times** in accepted
  code (std, accepted examples, aoc, rogue), mostly `.field` on an unknown type (1,022). Every
  one is caught by a try. These are the routes a single pass changes, and the reason draft 1
  chose a second pass;
- 7 of 686 reject examples fail with `E-CANNOT-INFER`.

The prototype counts what the queue actually holds, which is much less than the raises: 178
items queued in the whole corpus, 26 of them in std **[measured]**. Most of the 1,073 raises
were the same site failing again inside nested tries and the reruns of `retrying` and
`infer_call`'s prefix form; with the queue, the first try succeeds.

## 5. The design

### 5.1 Queue invariants

These say what makes the queue correct; the resume points W1-W4 are how they are met. Each has
its tests in [§9](#9-tests). They are the review's eight ([review-1.md](postponement/review-1.md),
"Suggested change to the design's invariants"), with invariants 2 and 8 made precise for a
unifier that can't wait (D2016).

1. **One placeholder, one occurrence.** A placeholder stands for exactly one queued occurrence
   of source syntax in one elaboration attempt. An attempt undone takes its items and their
   placeholders with it; elaborating the same syntax again makes a new item and a new
   placeholder.
2. **Only its item fills a placeholder.** Filling means putting the item's checked term in
   place: zonking writes that term, never a value read back. Until stage 6, unification may
   *solve* a placeholder as it solves any unknown, because comparisons can't wait; the item's
   term is then compared with that solution when it fills, and a disagreement is the item's
   error at its own span (D2016).
3. **Isolation.** In the review's words: "postponement may delay a choice, but must not expose
   a postponed item to information outside the lexical elaboration scope that would have been
   available to that item in a non-postponing elaboration". Operationally, an item is resumed
   only inside the scope in which it was created: at the end of the application it was created
   in or of one that encloses it (W1, scoped), or at the declaration-level points W2-W4
   ([§5.6](#56-resume-points-isolation-and-order)).
4. **No re-entry.** An item has a state: *waiting* (on its blocker), *running*, *done* or
   *failed*. Only a waiting item whose blocker is solved is resumed; it is running until its
   check returns. A running item is never selected by a nested resume point
   ([§5.7](#57-termination), step T3).
5. **Restore restores the queue.** Restoring a snapshot restores the items, their states and
   the resumption log to what they were when it was taken: an item queued since is gone, and an
   item resumed since is waiting again ([§5.3](#53-where-the-queue-lives-and-how-items-wait)).
6. **Kept subterms are stable.** An item keeps an elaborated subterm only if that subterm's
   final term can't change with what is learnt later (a choice that §5.10 decides at `finish`
   is allowed, as for invariant 8); otherwise it keeps the syntax and its
   context and elaborates it again when resumed. For a queued `.field`, the receiver is kept as
   syntax unless the blocker was made inside it ([§5.5](#55-the-receiver-of-a-queued-field-r1)).
7. **Defaults at quiescence only.** A default is applied only when resuming, obligations and row
   comparisons have all stopped making progress (ladder step 3, at W4). Effect rows are among
   the row comparisons. *Restated by D2087 (31 October 2026; built in step 4.2): at one of three
   points, W4, W2, and a `rewrite` rule's own checks before its search; see
   [Invariant 7, restated](#invariant-7-restated-d2087).*
8. **Placeholders are opaque to elaboration choices.** No choice that could give a different
   well-typed meaning is made from an unfilled placeholder's apparent shape: such a choice
   waits (an item, or the ladder's defaults), or is made at `finish` where only the term, not
   the meaning, depends on it. A choice whose wrong guess can only be a type error is allowed,
   as it is for any unknown today ([§5.10](#510-placeholders-filling-and-opacity-r7) lists every
   consumer).

### 5.2 What is queued

A **queued check** (an *item*) has:
- what to elaborate, one of the kinds below, as syntax, with a kept elaborated subterm only
  where invariant 6 allows one;
- its **blocker**: the unknown at the head of the type it needs;
- its **state**: waiting, running, done or failed (invariant 4);
- the saved context: the whole `Ctx` except the elaborator, cloned (the prototype's
  `Ctx::save`, `check.rs`);
- a **placeholder** unknown standing for its result in the term built so far, and the unknown
  for its result type;
- the error its site raises today, for when it stays stuck;
- its span.

| kind | created where today raises or retries | blocker | resumed as | prototype |
|---|---|---|---|---|
| K1 record literal | `check_record` at an unknown, and `infer_literal` (with a fresh type unknown) | the expected type's head | `check_record` at the type now known | yes |
| K2 `.field` or dot call | `find_in_view` meets `Step::Unknown` (`dot.rs:457`) | the unknown that step met (a later step may block again) | `infer_call` from the start, from the syntax ([§5.5](#55-the-receiver-of-a-queued-field-r1)); with a kept receiver only when the blocker was made inside it | yes, both ways |
| K3 method section | `section_unknown_name`; and today's section postponed without a try | the section's parameter type | a lambda over `x : ?D` whose body is K2 on `?D` | no |
| K4 number literal | a literal checked against an unknown, today defaulted to `Nat` at once (`numbers.rs:290-312`), and a number group with no type (`numbers.rs:944-946`) | the expected type | the literal at the type now known; default `Nat` | no |

**States.** A waiting item becomes running when a resume point selects it; running becomes done
when its check returns and its placeholder is filled, or waiting again, on a new blocker, when a
K2 meets an unknown at a later step of its view; running becomes failed when the check raises
an error. Failed is never kept: the error propagates, so either the enclosing attempt is undone
(and with it the transition, back to waiting, by invariant 5) or the declaration fails with that
error. The states live in the resumption log, which snapshots record (§5.3). The prototype has
the running/done distinction already: it marks an item done *before* resuming it
(`drain_queue_from` in the patch's `queue.rs`), so a nested drain skips it.

Not queued:
- **a lambda as a whole.** A lambda is always checked in place; what inside it needs its
  parameter's type is queued (K1-K4). This is what removes the lambda try-then-postpone
  ([§5.11](#511-removing-the-catch-and-retry-paths)). Lean does the same (`fun` is never
  postponed); Agda postpones some lambdas, and calls committing early "hazardous" for implicit
  lambdas, which Stitchwort doesn't have.
- **an effectful part (SW-885).** None is needed: the effect pass already binds the part and
  infers a pure literal, which is a K1 ([§2](#2-stitchwort-today)). Draft 1's stage 0 and Q4 are
  dropped.
- **a unification pair** ([§5.13](#513-the-unifier-and-placeholders-r4)).
- other `E-CANNOT-INFER` sites (`rfl`, `J`, quotients). They don't need a type's shape from
  later; they need an annotation.

### 5.3 Where the queue lives, and how items wait

**Per declaration**, as a table on the `Elaborator` beside `obligations` and
`row_constraints`, **indexed by blocker**:
- `clear_metas` clears it, `rewind` clears it;
- `Snapshot` records two lengths, of the items and of the **resumption log** (which items have
  been resumed or re-queued, in order, with their new states), and `restore` truncates both. So
  an attempt undone takes back both the items it queued and the resumptions it made: an item
  resumed inside an attempt that fails is waiting again afterwards. The prototype needed this
  (an item resumed and then undone was otherwise lost) **[run]**;
- a map from blocker to items lets a resume point look only at items whose blocker was solved
  since the last point (`Globals::meta_trail` lists solved unknowns in order, as
  `Snapshot::solved_since` already reads it). The prototype scans the whole queue instead;
- the **placeholder table**: for each placeholder, its item and, once filled, the checked term
  ([§5.10](#510-placeholders-filling-and-opacity-r7)). Snapshots record its length too.

**Why per declaration and not per unknown alone.** Metavariables, obligations, rows and
snapshots are all per declaration in Stitchwort, and a declaration's unknowns never outlive it
(`finish` zonks them). Agda's and OmniML's wait lists hang off each unknown in a store that
outlives declarations; here that store is the declaration. So items live in the declaration's
table and wait on an unknown, which is OmniML's wait list with Stitchwort's lifetime.

**Why not wake inside the unifier**, as Agda's `wakeupConstraints` does after an assignment:
`unify` is a function of `Globals` with no `Ctx` (`unify.rs:30`), called inside many of the 42
`Snapshot::take` sites and 48 `transaction`/`attempt`/`undo::unify` calls that branch on its
answer, and resuming an item elaborates syntax. Waking from inside it would run elaboration in
the middle of a comparison. Waking at the resume points below gives the same order at fixed,
safe places.

### 5.4 Item kinds in detail: K1, K3, K4

- **K1** waits before checking any field, so it keeps nothing elaborated: invariant 6 holds
  trivially. Resumed, it is `check_record` against the type now known.
- **K3** is K2 inside a lambda: `.f a` becomes `x => x.f a` with `x : ?D` at once, and the body
  is an ordinary K2 on `?D` whose receiver is the variable `x`, made before the receiver, so
  kept as syntax (§5.5). The review agrees this is the right normalisation: "it reduces method
  scheduling semantics". *As built, the section is queued whole and checked at its type once
  `?D` is known, so that it keeps D506's partial application; the scheduling is K2's ("As built
  (stage 3)", deviation 1).*
- **K4** keeps the literal (syntax). Its default, `Nat`, is applied in the ladder after the
  field-name default (§5.8). The number *group* of `numbers.rs` (a comparison or arithmetic
  tree typed at once) defaults to `Nat` at its step 6 (`numbers.rs:944-946`) when no leaf
  decides; under K4 that default also moves into the ladder, at K4's priority, because it is
  the same choice (invariant 8, §5.10).

### 5.5 The receiver of a queued `.field` (R1)

The review asked that "kept receivers" be a design invariant (invariant 6), since a receiver
elaborated before its type is known could freeze a choice that would differ once it is known:
"the kernel will catch an incompatible choice. It will not catch an alternative compatible but
semantically different one."

**What a receiver's elaboration does today** **[checked]** (§2, "How a dot call is
elaborated"):
- The receiver is never elaborated against an expected type before the namespace is known. The
  prefix form infers it only to find the namespace and undoes that (`dot.rs:1166-1174`); the
  dot form infers it with no expected type (`dot.rs:316-322`).
- After the namespace is known, the prefix form elaborates the receiver *again, from syntax*,
  checked against `T.f`'s receiver parameter. So Stitchwort already does what the review
  prefers: the receiver is kept as syntax and elaborated again once its type is known.
- What the receiver's inference can decide from an unknown's shape is listed in §5.10: number
  literals (`Nat` at once, `numbers.rs:290-312`), operator dictionaries (decided at `finish`:
  the projection is made when the declaration finishes, so an operator whose dictionary is
  found later still gets the term a known type gives, `interfaces.rs:1490-1521`, `:1705-1738`), the `if` condition's reading
  (`logic.rs:98-118`), the container of `in` (`membership.rs:98`), and implicit arguments,
  inserted only where the type is already a function with leading implicit parameters
  (`insert`, `check.rs:2843-2882`). Effects decide from declared types and syntax:
  `receiver_passed` (`effects.rs:2000-2009`) reads `target_place`, which reads the receiver's
  type without elaborating it (`receiver_type`, `dot.rs:1451-1495`), and an unknown counts as
  not a computation (`is_comp_type`, `effects.rs:1795-1809`).

**What K2 meets in the corpus** (draft-3 counters, [§6.7](#67-draft-3-runs)) **[measured]**:
159 `.field`s queued, counting those in attempts later undone.

| receiver | blocker made before the receiver | blocker made inside the receiver |
|---|---|---|
| a variable (a lambda parameter, a `let`, a pattern variable) | 131 | 0 |
| a `.field` (chained: itself a K2's placeholder) | 0 | 19 |
| an application | 0 | 5 |
| a record literal (a K1's placeholder) | 0 | 4 |

In none of the 159 did the receiver's inference default a number literal or choose a generic
dictionary, and in none, at resume, did the receiver's type have a leading implicit parameter
that `insert` would now fill (all three counters 0) **[measured]**.

**The rule** (invariant 6 for K2):
- **Blocker made before the receiver: keep the syntax.** At queue time, restore the snapshot
  taken before the receiver was inferred (the one `prefix_form` already takes), queue
  `recv.field args` with the saved context, and wait on the blocker, which survives the restore
  because it predates the receiver. Resume by calling `infer_call` from the start: prefix form
  or dot form, exactly as an elaboration without postponement would choose now. Items queued
  inside the receiver are undone with it and made again on resume (invariant 1). This covers
  131 of 159, all variables, where elaborating again costs nothing.
- **Blocker made inside the receiver: keep the term.** Then the receiver's own unknowns are the
  only link through which its blocker can be solved; undoing them would leave an item nothing
  can wake (this is why Agda keeps the principal argument, `Application.hs:1440-1476`). The
  kept term is stable, which is the review's second clause ("elaboration of that syntactic
  category is independent of expected-type information"):
  - it was inferred with no expected type, as `infer_dot` infers it today (`dot.rs:316-322`),
    so no expected-type information was missing that the resumed item would have;
  - for a chained `.field` or a record literal (23 of 28), the receiver *is* a placeholder: a
    choice not yet made, which its own item makes later under these same rules;
  - for an application (5 of 28), the choices its inference could make from an unknown's shape
    are §5.10's, and invariant 8 makes each of them wait or not depend on time; a debug
    assertion checks that no number literal was defaulted inside a receiver kept as a term (the
    counters above are 0 today). Operators are not checked: they are decided at `finish`
    (§5.10), so a kept receiver's `x * x` is projected at the end to the same term as with the
    type known at once;
  - at resume, everything after inference that reads the type is redone at the type now known:
    `insert`, `written_type`, `find_in_view` and `call`. (The prototype redid all but `insert`;
    the counter shows `insert` would have added nothing.)

**Measured** **[measured]**: the prototype was run both ways over the whole corpus (scoped W1,
W2). Queueing the 131 as syntax and resuming them through `infer_call` gives **the same outcome
for every file and the same hash for every declaration** as keeping all 159 receivers, and the
three repros still pass their run-time tests ([§6.7](#67-draft-3-runs)).

**Why not always keep the syntax** (Lean's restore) [inferred]: for the 28 the item would have
no blocker left to wait on. **Why not always keep the term** (Agda, and draft 2): for a variable
it saves nothing, and keeping is a claim about stability that elaborating again doesn't need to
make. The rule takes the simpler claim wherever it can.

### 5.6 Resume points, isolation and order

**Resume points.** The ladder below runs, scoped as in Lean's `withSynthesize`, at:
- **W1, the end of each application**, after its arguments and before its type is compared with
  the expected type, for the items created while the application was elaborated;
- **W2, before lifting** (`lift` and `lift_signature`): a queued literal may hold a `match`,
  which must be drafted before helpers are lifted;
- **W3, every round of the obligations loop** (`solve_obligations_until_stuck`), so any
  `solve_obligations` call (there are several mid-declaration) resumes too;
- **W4, `finish`**, for the items made since the last `finish`, with defaults and the stuck
  report.

The prototype found W1 and W2 necessary **[run]**:
- with only W3 and W4, std doesn't load. `Map/Spec.sw:1862` has
  `Eq.cong (xs => List.last (List.filter xs (e => Map.Spec.isLess e.fst key))) h`. The
  queued `e.fst` is still a placeholder when `Eq.trans` compares the `Eq.cong` with its
  expected type, the comparison fails, and nothing can wait. With W1, `e.fst` is resumed when
  `h` has fixed `e`'s type, at the end of the `Eq.cong` application;
- with W1 and without W2, aoc fails with `E-MATCH-MOTIVE` at
  `Day08/Proofs/Part2.sw:148`: a record literal `{ forward = …, backward = … }` holding a
  `match` is resumed after its declaration's helpers were lifted.

**Isolation (invariant 3).** At W1, only items created during the application are resumed
(Lean's `withSynthesize`). An item created outside is resumed at the outer application's W1 or
at W4. The review makes this non-negotiable, and the evidence supports it: unscoped, the
prototype accepts `postponed-lambda-second-error.sw`, because `c.size` is resumed three times
inside attempts that are later undone, under three different transient states, and the one that
survives is not the one an elaboration without postponement would reach; scoped, it stays
rejected with today's error ([§6.2](#62-acceptance-changes), [§6.5](#65-variants)). So the scope
is an isolation boundary, not an optimisation: an item sees what its own scope learnt, as it
would without postponement, plus what its own later arguments fixed, which is the point.

W2-W4 are declaration-level: `lift` (`lift.rs:547`), `solve_obligations_until_stuck` and its
callers (`lib.rs:1090`, `auto.rs:85`, `local.rs:448`, `lift.rs:551`, `:566`, `rows.rs:333`,
`interfaces.rs:644`) and every `finish` call are methods of the `Elaborator` run between
elaborations, never from inside `check` **[checked: the callers]**. So no declaration-level
point runs inside an item's resumption, and the items they see are, by construction, those of
the declaration part being finished.

**The ladder** (one function; W1-W3 run steps 1-2, W4 runs all):
1. Resume, in creation order, every waiting item in scope whose blocker is solved (its type's
   head is no longer an unknown). It is running until its check returns; then fill its
   placeholder ([§5.10](#510-placeholders-filling-and-opacity-r7)). Resuming may queue new
   items; they go at the end. If anything was resumed, repeat step 1.
2. Run a round of obligations and row constraints. If anything was solved, go to 1.
3. (W4 only) Apply **one default**, the first by priority, then by creation order: priority 1,
   SW-805's field-name rule for a waiting record literal; priority 2, `Nat` for a waiting number
   literal or number group ([§5.8](#58-defaults-and-sw-805s-rule)). If one applied, go to 1.
4. (W4 only) If items are still waiting, report ([§5.9](#59-stuck-items-and-errors)).

### 5.7 Termination

Draft 2's argument counted items "per surviving attempt". The review is right that this is not
a global bound: "rollback can recreate states", and a restored state may elaborate the same
syntax and queue the same logical item again. The argument below bounds the attempts first,
then the work inside one branch. It rests on the existing try-and-undo sites, which I read one
by one (T1, T2); the rest is [inferred] from them and from the ladder.

**T1. Every attempt site has a fixed, finite list of alternatives** **[checked]**. There are 42
`Snapshot::take` sites outside `undo.rs` and 48 calls of `transaction`, `attempt`,
`numbers::attempt` and `undo::unify`. Each is one of:
- **two or three ways in straight-line code**: try one way, undo, then another or fail. For
  example `pure_first` (`check.rs:1043`), the lambda in place (`check.rs:1970`), `late_able`
  (`check.rs:1954`), the argument after the expected type (`check.rs:2078`), `retrying`
  (`check.rs:1874-1899`: a second run with `late_literals` on, and a nested `retrying` inside
  it runs once, `check.rs:1875-1877`), expected-type propagation (`check.rs:4152`, `:4253`),
  the prefix form's speculative inference and then the dot form (`dot.rs:1166`, `:1628`),
  `section_partial` (`dot.rs:667`), `last_resort` (`records.rs:726-745`), a number group's
  leaf (`numbers.rs:1122`), the `if` condition (`logic.rs:98-118`), `in`'s container
  (`membership.rs:73`), and the sites in `effects.rs`, `named.rs`, `cases.rs`, `matching.rs`,
  `no_effect.rs`, `rows.rs`, `defaults.rs`, `lift.rs` and `bind.rs`;
- **a loop over a finite list, each element tried once**: each hypothesis in context
  (`rewrite.rs:576`), each atom seen so far (`omega.rs:2055`), each obligation of an instance
  tree, with a `tried` set (`interfaces.rs:1405-1440`), occurrences in a goal (`rewrite.rs`,
  bounded by its `remaining` budget), case splits (`omega.rs`, bounded by `splits`), proof
  search (`auto.rs`, bounded by its depth, `auto.rs:637`);
- **a loop that repeats only on progress**: the obligations loop (`auto.rs:100-140`, a
  `progress` flag set only when an obligation is solved or a row settles), row retries
  (`check.rs:1051`, `rows.rs:330`, each round settling a comparison or stopping), the local
  retries (`lib.rs:2270-2295`, again only while `preadmitted` grows, bounded by the local
  definitions), the total-row retype (`lib.rs:2445-2460`, once).

**T2. Which sites run the same alternative again in the same state** **[checked]**. The review
asks that no attempt "retries the same alternative with the same metavariable state". Three
sites can, each a fixed number of times, never in a loop:
- the lambda tried in place and then checked after the later arguments (`check.rs:1970`, resumed
  at the end of `apply_args_postponing`), when the later arguments solved nothing;
- the argument after the expected type (`check.rs:2078`, `:2164`), when the comparison with the
  expected type solved nothing;
- the `if` condition's `Bool` reading (`logic.rs:114-117`): after a failed proposition reading,
  when the `Bool` reading had drafted a `match`, the `Bool` reading is run again from the same
  state, because "undoing the reading drops them, so if it made any, it's done again"
  (`logic.rs:94-97`), and fails again the same way.

`retrying`'s second run is a different alternative (`late_literals` on), though it repeats the
work when nothing defers. One site already guards against repetition: the prefix form, not
tried again in a state it failed in (`dot.rs:1656-1670`). None of the three breaks termination:
each is a fixed second (or third) try. The first two are catch-and-retry paths stage 5 removes;
the third is outside the queue's reach and is noted as wasted work.

**T3. A running item is never resumed by a nested resume point** [inferred from §5.6]. Inside a
running item's check, the only resume points reachable are W1s of applications inside it, and a
scoped W1 sees only items created during its application, that is after the running item
started. W2-W4 are never reached from inside `check` (§5.6). The state *running* makes this a
checked fact rather than a consequence: a debug assertion fails if the ladder selects a running
item.

**T4. The measure.** Consider one *branch*: a sequence of elaboration steps with no restore
across them. In it, lexicographically:
1. the occurrences of the declaration's syntax not yet finished in this branch, an item's
   occurrence counting as unfinished while it waits;
2. the remaining steps of each waiting K2's type-head view (finite: `find_in_view` stops at a
   head seen before, `dot.rs:496-498`);
3. the obligations not yet solved and the row comparisons not yet settled.

Elaborating syntax finishes occurrences (1 falls) and may make new unknowns and obligations
(2 and 3 may rise, which is why unknowns are not in the measure, unlike the review's version).
Resuming an item finishes its occurrence (1 falls), or re-queues a K2 at a strictly later step
of its view, since within a branch types only get more solved (2 falls). A return from ladder
step 2 to step 1 needs a solved obligation or a settled comparison (3 falls), and obligations
made by instance search are bounded by its depth. A default solves a waiting item's blocker and
the next step 1 finishes that item (1 falls). Queueing a K2 as syntax undoes its receiver
(§5.5), which leaves 1 where it was before the `.field` and moves on to other syntax.

Across branches: a restore happens only inside an attempt site, which then runs its next
alternative or fails upward (T1). So the attempts form a tree. It is finitely branching (T1),
and it has finite depth, because along one branch the nested sites are entered while
elaborating occurrences that measure 1 counts down, or inside T1's bounded loops. A finitely
branching tree of finite depth is finite. The review's first component, "unexplored finite
alternatives in the current attempt tree", is this tree's unvisited part: rollback may raise
1-3, but only by returning to a node whose next alternative is a different, not yet visited
node. "The same logical item again" after a restore is an item of that different node.

**The step budget stays** (`budget.step`), as the review recommends. Under T1-T4 it is a
resource limit, not a patch over a gap, **on condition that every new attempt site keeps T1**:
a finite, fixed list of alternatives, and loops only on progress. That becomes a review rule
for `undo.rs`'s callers, written into its module comment in stage 1. The elaborator fuzzer
already checks that every mutated example finishes within a step limit and a 60 s watchdog
(`crates/driver/tests/fuzz_elab.rs`, docs/testing.md), which tests the condition from outside.

**Correction to draft 2.** Draft 2 said "the ladder takes no snapshot". Its step 2 runs instance
search, whose attempts take and restore snapshots (`interfaces.rs:1431`, `auto.rs:232` and
others). Each is a T1 site, finite, and none spans a resumption.

### 5.8 Defaults, and SW-805's rule

SW-805's rule stays as D1991 has it, a name-resolution rule that looks only at the literal's
field names and the names in scope (assumption R1), but it runs **as a default**, at step 3,
not at the literal. Two prototype variants show why **[run]**:
- **as a default** (the prototype): `examples/accept/record-literal-inferred.sw`'s tests "the
  other side says" (`hidden 1 == Some ({ value = one })`) and "appended"
  (`[{ value = 2 }] ++ [({ value = 3 }: Hidden.Cell)] == …`) pass, because the other side fixes
  the type before any default runs. Its test "in a list",
  `[{ row = 1, column = 2 }, …].map (p => p.row) == [1, 4]`, fails: `[1, 4]` is made
  `List Nat` at once (numbers default at the literal today), and when the field-name default
  later makes `p` a `Position`, `p.row` is an `Int`;
- **at the literal when it finds one type** (Agda's order; `STITCHWORT_QUEUE_NAMES_FIRST=1`):
  "in a list" passes, and the other two fail with
  "expected `Option Cell`, but this has type `Option Hidden.Cell`" and
  "expected `Cell`, but this has type `Hidden.Cell`", which is what `held`/`last_resort`
  exists to prevent.

So the rule is right as a default, and number literals have to wait too: K4, defaulted to `Nat`
after the field-name rule, as Lean defaults numerals by its lowest-priority default instance
(`Prelude.lean:1411`). With both in the ladder, "in a list" is: literals waiting, `p.row`
waiting, `[1, 4]` waiting; default 1 makes the list's elements `Position`; `p.row` resumes as
`Int`; `1` and `4` resume as `Int` **[inferred]**. That is D2013.

**The review agrees with the order**, for the reason that matters: SW-805's rule "looks only at
field *names*. It doesn't perform candidate-directed type checking of fields. So defaulting `1`
to Nat does not give the SW-805 rule any additional evidence anyway." The review's caveat is
recorded as a condition on D2013: **if record inference ever checks fields against candidate
types** (enumerate the record types with these names, check the fields against each, keep the
viable ones), a number's type would become evidence for the record, and the order must be
revisited.

**`held` and `last_resort` are subsumed.** They exist so that a literal in one part of `==`,
`++`, `calc` or a comparison group waits for another part to say its type. With K1, every
literal waits, so the other part always gets the chance, and the field-name rule applies only
where nothing else said. With the prototype on, `last_resort` reran 0 times, against 5 with it
off **[measured]**. The `FieldNames` counters, `held`, `last_resort`, and the three "infer one
side, on `E-CANNOT-INFER` infer the other" catches can go once K1 is in (stage 5). D1991's R1
still holds: the default looks at names only. What changes is *when* it runs, which D1991
doesn't fix.

### 5.9 Stuck items and errors

**Resumed and failing.** A resumed item that fails reports **its new error, against the type
now known, at its original span**: `Ctx::save` keeps the span, and `cx.mismatch` prints today's
solutions. This is Lean's `withRef stx` plus `instantiateMVars` (`SyntheticMVars.lean:33-39`).
The review: "if `q.x` was postponed because `q : ?a`, and eventually `?a = String`, then
`String has no field or function x` is the real error. Reporting `can't tell what q is` would
now be false." In the prototype this arose once, in `postponed-lambda-second-error.sw`
([§6.2](#62-acceptance-changes)), unscoped only.

**Stuck at the end: by independent root.** Each item carries the error its site raises today
(code, message, span, notes). At W4, the waiting items are grouped:
- an item **depends on** another if its blocker is that other item's placeholder or result-type
  unknown, or is solved only through it (a chained `.field`'s blocker is the inner `.field`'s
  result type; a `.field` on a waiting record literal waits on the literal's type);
- the **root** of an item follows that relation to an item that depends on no waiting item;
- items with the same root, or the same blocker, form one group.

The report is **the first item, in creation order, of each group, for at most 3 groups**; the
others are suppressed as consequences. The first is the declaration's error, as today's first
`E-CANNOT-INFER` is; the next two go out as further errors through the channel `branch_errors`
already provides ("a definition that fails reports them after its own error",
`lib.rs:380-385`). So `A on ?1; B on A's placeholder; C on B's` reports A once, and
`A on ?1; D on ?7` reports both, as the review proposes.

With the prototype on (first stuck item only), **no reject example's error changed** (687
files), and the 4 items left stuck were in those files **[measured]**. With grouping, a
declaration with independent stuck items gains a second or third error; none of the 4 is such a
case [inferred: 4 items in 4 different files].

### 5.10 Placeholders: filling and opacity (R7)

**Filling.** A placeholder must be filled with the **checked term**, as `fill_placeholder` does
today, not by unifying it with the term's value. The prototype unified, and in
`Day06.offRouteFree` that wrote `Map.Spec.sameKey.%match1 (Position.%compare blocker other)`
where the source and today's term have `Map.Spec.sameKey blocker other` **[run]**: reading a
value back unfolds calls. Stitchwort already has the mechanism, for lifted helpers: the
placeholder table records the item's term, as `lifted_calls` records a helper's call
(`lift.rs:661-666`), and zonking puts the term in place of the placeholder applied to its
variables, as it does for a lifted call (`unify.rs:1719-1727`). The types that mention the
placeholder see its value, as today.

**Solvable by unification, until stage 6 (D2016).** Lean makes a postponed placeholder
synthetic opaque (`TermElabM.lean:1458`), and the review suggests the same. Stitchwort's
version would be a frozen metavariable (§2, "Opaque unknowns already exist"). Draft 3's runs
measured it **[measured]**:
- with placeholders as ordinary unknowns, 14 of 135 fills found the placeholder **already
  solved** by unification: a comparison had met the placeholder and solved it as a pattern
  (for example `?18 diskMap file free := (FreeSpace.moveFile free file).snd`, from an expected
  type in a day 9 proof), and the item's term later agreed;
- with placeholders frozen until filled, those comparisons fail instead: one accepted example
  (`lambda-postponed-dependent.sw`) and four AoC proofs (2024 days 9 and 24) become
  `E-TYPE-MISMATCH`, for example "expected `File.idAndLength (?18 diskMap file free) =
  File.idAndLength file`, but this has type `File.idAndLength (FreeSpace.moveFile free
  file).snd = File.idAndLength file`".

Lean can freeze because its unifier can postpone a comparison; Stitchwort's answers at once. So
until comparisons can wait (stage 6), a placeholder stays solvable by unification, and
invariant 2 is kept by the fill: the item's term is compared with any solution, a disagreement
is the item's error at its span, and zonking writes the item's term, not the solution. A
solution found by unification is not a guess: a pattern solution is forced by the comparison
that found it, and other comparisons are put aside or fail (`unify.rs:30-80`). Once stage 6
lands, placeholders become frozen and those 14 comparisons wait instead (D2016).

**Opaque to elaboration choices (invariant 8).** "A synthetic placeholder representing postponed
syntax is not ordinary unknown evidence and consumers must not make irreversible elaboration
choices from its apparent shape." Every place that chooses from a type's shape treats an unknown
in one of three ways, and a placeholder's type is an unknown like any other **[checked]**:

| consumer | where | with an unknown today | with a placeholder, end state |
|---|---|---|---|
| dot namespace lookup | `find_in_view`, `dot.rs:443-461` | `E-CANNOT-INFER` | **waits**: K2 |
| record literal's type | `check_record`, `infer_literal`, `records.rs:783-890` | SW-805's rule, else `E-CANNOT-INFER` | **waits**: K1, field-name default in the ladder |
| method section | `section_unknown_name`, `dot.rs:454`, `:696` | `E-CANNOT-INFER` | **waits**: K3 |
| number literal | `check_literal`, `numbers.rs:290-312` | made `Nat` at once, noted in `defaulted` | **waits**: K4, `Nat` in the ladder |
| number group's type | `group_in`, `numbers.rs:799-1000` | a leaf of unknown type decides nothing (`Class::Unknown`); with no deciding leaf, `Nat` (`:944-946`) or, for `==` with nothing numeric, the first leaf's type | an unknown leaf decides nothing, as today; the `Nat` default **moves into the ladder** with K4 |
| instance search | `interfaces::attempt`, `auto.rs:100-140` | waits (`Attempt::Wait`) | waits, as today |
| a proposition where a `Bool` is expected: its decision (added in stage 3, D2035) | `decide_to_bool`, `check.rs:4113`, via `bind::decide` | decided at once; with a placeholder in it, `E-AUTO-NONE` naming the placeholder | **waits** for the placeholder: a `Decide` item (stage 3) |
| `==` and `!=` as `Bool`: the decision | `decide_eq_of`, `interfaces.rs:1490-1521`, via `bind::decide`, `bind.rs:255-313` | found at once if it can be, and then its field is projected (`Nat.decEq x y`); otherwise the generic `DecEq.decide [d] x y` | **decided at `finish`**: the projection is made at zonk, so the term doesn't depend on when the dictionary was found (the `Day05.noRuleBroken` fix) |
| `+`, `*`, `<`, `<=` through a dictionary | `method_call`, `interfaces.rs:1705-1738`, from `operator`, `numbers.rs:1347-1402` | the same: projected only if found at once | **decided at `finish`**, as above |
| prefix form or dot form | `infer_call`, `prefix_form`, `dot.rs:1143-1238`, `:1613-1640` | an unknown receiver type: dot form | the choice is made at resume, from the syntax (§5.5) |
| implicit arguments of an inferred term | `insert`, `check.rs:2843-2882` | none inserted | none inserted at the placeholder; the item's own term has its implicit arguments inserted before it fills (§5.5) |
| `if c`: `Bool` or proposition | `condition`, `logic.rs:98-118` | the `Bool` reading, tried first, succeeds | the same: allowed, a wrong guess is a type error (below) |
| `-k`, or a number group with a `-` | `check_literal`, `group_in` (step 4), `numbers.rs:326-332` | made `Int` at once, not noted in `defaulted` | the same: allowed, a wrong guess is a type error (`-k` is never a `Nat`, and a `Float` would mismatch) |
| `x in c`: list or keys | `container_kind`, `membership.rs:72-98` | a list (`:98`) | the same: allowed, a wrong guess is a type error |
| an unknown type of types | `check_type`, `check.rs:4864-4866` | `Type` | the same: allowed |
| applying something of unknown type | `function_parts`, `check.rs:2701` | an explicit function type of two new unknowns | the same: a unification, not a choice among readings |
| passing or running an effectful part | `receiver_passed`, `effects.rs:2000-2009`; `is_comp_type`, `:1795-1809` | an unknown is not a computation: run | the same: decided from declared types and syntax, not from a placeholder (§5.5) |

So the consumers fall into three classes:
- **wait** (dot lookup, records, sections, numbers, instance search, a `Bool` decision): the queue and the ladder;
- **decided at `finish`**, where the choice changes the term but not the meaning (the
  operators' known-instance projection, the dot call's route). The projection at `finish` is a
  change to today's code too: wherever an operator's dictionary is found after the operator
  today, its term becomes the specialised call. The corpus has 486 generic fallbacks today
  (switch off; 487 on, the extra one `Day05.noRuleBroken`), counting attempts undone and
  dictionaries that are local variables, which stay generic **[measured]**; how many become
  specialised is measured in stage 1, as a hash list;
  what the class relies on is that an operator's result type does not depend on its dictionary
  (`a → a → a`, `Prop`, `Bool`, all homogeneous), so the receiver of a dot call on an
  operator's result has the same type whichever dictionary is found. That is why invariant 6's
  assertion does not check operators (SW-3045). A future operator interface whose result type
  depends on the dictionary (a heterogeneous or output-typed operator) would have to wait
  instead, and the assertion would have to cover it;
- **allowed** (the `if` reading, `in`'s container, `Type`, a function's shape, `-k` and a group
  with `-` made `Int`): these are
  irreversible choices from an unknown's shape, so this is a deliberate weakening of the
  review's invariant 8. They are allowed because their alternatives have different types: a
  wrong guess fixes the placeholder's type to something its item's result must match at the
  fill, so it ends as a type error at the item, never as a different well-typed meaning. And
  each program that reaches one fails today with `E-CANNOT-INFER`, so none can change an
  accepted program. Queueing them too (an item for the whole `if`) is possible later if a case
  wants it [inferred].

### 5.11 Removing the catch-and-retry paths

Each path of the table in [§2](#2-stitchwort-today), and what replaces it:

| path | end state | evidence |
|---|---|---|
| lambda tried in place, postponed on failure | removed: a lambda is checked in place; K1-K4 inside it wait | with K1 and K2 on, it fires 9 times instead of 100 (8 with W1 scoped): 6 method sections (`.fst`, `.couldBeTrue` in aoc; K3), and 3 (2) in reject examples **[measured]** |
| section postponed without a try | removed: K3 | 46 firings, all K3 sites |
| `retrying` with `late_literals`, `defers_literal`, `else_first`, `check_items`' reordering | removed: K4 makes the order of number literals irrelevant | 19 firings with the switch off, 17 with it on: numbers aren't queued in the prototype |
| `held` / `last_resort` | removed: K1 plus the field-name default | 5 reruns off, 0 on |
| "infer one side, else the other" in `++`, `calc`, comparisons | removed: the first side's literal or `.field` waits, so the first side always infers | covered by the line above |
| lambda or argument checked after the expected type | **kept**, as Rocq's bidirectionality hint: it is about proofs found from the goal (`E-OMEGA`, `E-REWRITE-NOTHING`), not about unknown types; only 2 of its 233 firings were `E-CANNOT-INFER`, and those go with K1-K2 | 233 firings off, 228 on |

The after-expected path is not a postponement of an unknown type but a choice of which
information a proof search sees. The review agrees strongly: it is "changing the goal supplied
to a search procedure, rather than delaying syntax because its input type shape is unavailable.
Trying to force both through one abstraction would make the queue less principled, not more."
It stays separate.

### 5.12 The existing postponements as instances

- **Record literals (SW-817, SW-885).** K1 at the literal, field-name default at W4.
- **`.field` on an unknown type (SW-847).** K2, its receiver as syntax (a variable).
- **Method sections.** K3: the section becomes `x => x.f …` at once, with `x : ?D`, and its body
  waits on `?D`. Today's special case "postponed without a try unless a later parameter
  depends on it" goes, and so does `section_unknown_name`'s separate error path (the K2 inside
  carries the section's message).
- **Lambda arguments.** No longer postponed as a whole. Their stuck pieces are K1-K4, resumed at
  the application's W1, which is where today's postponed lambdas are checked.
- **`late_literals`.** K4.
- **`after_expected`.** Kept as is ([§5.11](#511-removing-the-catch-and-retry-paths)).

### 5.13 The unifier and placeholders (R4)

Two levels, kept apart, as in draft 1:
- **The unifier's pairs (SW-896)** live inside one `unify` call. One still stuck when the call
  ends makes the call return `false`.
- **The queue** holds *checks* (syntax plus context) across the declaration. A resumed item runs
  ordinary `check`, whose own `unify` calls put pairs aside as usual.

**W1 is a pragmatic substitute for waiting comparisons, not a complete one.** The review: "No
number of 'end of application' checkpoints makes that general", for a placeholder that a
comparison consumes before information that solves its blocker arises later in the same
non-application construct. The corpus has no such case with W1 scoped, but the 14 placeholders
that unification solved early (§5.10) show comparisons do meet placeholders, and D2016's
freeze shows what happens when they can't solve them.

The end state is **tri-state unification**: `unify` answers `Yes`, `No`, or `Blocked(unknowns)`,
the unknowns being the ones a put-aside pair is stuck on. A caller that gets `Blocked` keeps the
comparison as a declaration-level constraint, woken when one of its unknowns is solved, as
`rows::postpone` does for rows and as Agda's `ValueCmp` constraints do. Then placeholders can be
frozen (D2016's end state), and W1 can become less frequent. It is stage 6, an **expected
follow-up**, not a condition for the queue: the review says "I would not block this queue work
on it, though. The queue is useful independently." Draft 1 measured that 91-94% of put-aside
pairs fail with nothing solved since, so most `Blocked` answers would not wake.

**The trigger** for stage 6 is measurable from stage 1: a counter of comparisons that met an
**unfilled** placeholder and answered `false`, and of fills that found the placeholder already
solved (14 today). Stage 6 starts when the corpus or the elaborator fuzzer
(`crates/driver/tests/fuzz_elab.rs`, whose mutations drop annotations) produces a program whose
placeholder crosses W1 unresolved and makes a comparison fail that would have succeeded once the
item was resumed.

### 5.14 `let`, and SW-847 (D2011 kept)

`pure_let` still infers the value first. When `item.value` is reached with `item : ?B`
unknown, it is a K2 item and the lambda's body type is the placeholder's type. The receiver
`item` is a variable whose type unknown `?B` was made with the lambda's parameter, so it is
queued as syntax (§5.5). The body `List.sumBy pairs counted` unifies the parameter with
`(Nat, Item)`, and the next resume point resumes `item.value` with `?B = Item`. The prototype
accepts sw847.sw this way, both with the receiver kept and as syntax, and the test
`total [(0, {value = 5}), (7, {value = 9})] == 5` passes **[run]**. So D2011 still fits the
single queue and is kept: no body-first `let` (Lean's `let_delayed`), and the `let` stays
transparent for the body.

A let-bound method section (`let g := .drop 1; g xs`) works the same way once K3 exists, which
moves `examples/reject/section-unknown-receiver.sw` to accept [inferred; the prototype doesn't
queue sections, and that example is unchanged with it on].

### 5.15 The language server

The language server elaborates a file's declarations with the same elaborator
(`crates/cli/src/lsp.rs`), so the queue's behaviour there is the batch behaviour. What differs:
- **Broken code.** A stuck item reports the error its site reports today, so diagnostics while
  typing `p.` are unchanged. A resumed item that fails reports at its own span, which is where
  the user is typing.
- **Several errors.** Up to 3 independent roots are reported (§5.9), so the editor shows an
  unrelated second stuck item without the cascade behind the first.
- **Hover and goals** see more: a `?` goal or a hovered variable inside a queued check is noted
  when the check resumes, with its type known, where today the whole declaration stopped at the
  first `E-CANNOT-INFER` [inferred].
- **Cost.** The queue is per declaration and is cleared with it, so incremental re-checking is
  unaffected. A resume point with nothing in scope costs a length comparison. CPU time over the
  corpus didn't rise ([§6.4](#64-cpu-time)).

### 5.16 Snapshots (P3 revisited)

D1990's P3 says queued items need no snapshot because they try nothing before waiting. That
still holds for K1, K3 and K4, and for resuming: an item is resumed only when its blocker is
solved, so the head test that queued it now passes. For K2 it changes in one place: a `.field`
whose blocker predates its receiver restores the snapshot taken before the receiver (§5.5),
which `prefix_form` already takes, so no new snapshot site is added. And the *queue itself*
(items, resumption log, placeholder table) is part of the state that every snapshot records
([§5.3](#53-where-the-queue-lives-and-how-items-wait)).

## 6. What the single queue changes today

### 6.1 Method

The prototype ([§11](#11-the-prototype)) queues K1 and K2 in the main pass, with the
catch-and-retry for them off (they never raise, so nothing catches), resume points W1-W4
(W1 unscoped), and the field-name rule as the only default. A scratch test
(`crates/driver/tests/queue_scratch.rs`) loads std eagerly, then each of
`examples/{accept,reject,extract}` (rewinding between them), aoc and rogue, and writes every
declaration's hash, every file's errors (code, message, span), the queue's counters and the
retry paths' counters. It ran twice with the switch off and twice on; the two runs of each
agree **[measured]**. The off runs stand for today's compiler: with the switch off, the prototype
only adds bookkeeping that can't change a result (two more lengths in each snapshot, an empty
table cleared, flag checks, a thread-local cleared at each dot call, and the retry-path
counters) [inferred from the diff; the off hashes were not compared with a build of `main`].

### 6.2 Acceptance changes

With W1 unscoped, two files change, one each way; with W1 scoped (recommended), only the first
**[measured]**:

| file | off | on | kind | work |
|---|---|---|---|---|
| `examples/accept/record-literal-inferred.sw` | accepted | `E-TYPE-MISMATCH` "expected `Nat`, but this has type `Int`" at `p.row`, in the test "in a list" | **needed fix: a default runs too late relative to another**: `[1, 4]` became `List Nat` at once, before the field-name default made `p` a `Position` | K4: number literals wait and default after the field-name rule (D2013) |
| `examples/reject/postponed-lambda-second-error.sw` | `E-UNKNOWN-FIELD` "`List` has no field or function `size`" | accepted | **a correct program today's order rejects**: `twice (c => c.size) (c => List.length c) (Counts.of 1)` with `Counts := List Nat`; with the queue, `c.size` is resumed three times, failing twice (as `List`) inside attempts that are undone, and the surviving route has `c : Counts`, where `Counts.size` exists. The test `a == 2` passes | with scoped W1 ([§6.5](#65-variants)), the recommended form, it stays rejected with today's error, so no change. Unscoped, the example would move to accept and need a replacement that is wrong under every order |

### 6.3 Hash changes

**26 declarations** of the 23,213 hashed (std 4,352, accepted examples 10,071, extract 1,910, aoc 6,068, rogue 812) change hash: 2 tests in `examples/accept/safe-fields.sw` and 24 declarations
in aoc (2024 days 5, 6, 8 and 24). **Std (all of it), rogue, the other 320 accepted examples and
all 53 extract examples are unchanged** **[measured]**. Exact terms (`{:?}` of the core term)
were compared for every changed declaration. Seven differ in their own term; the other 19 have
identical terms and differ only through the hash of a declaration they refer to.

| declaration | what differs | verdict | work |
|---|---|---|---|
| `safe-fields.sw`: tests "record equality", "record inequality" | `counter 3 (-2) == Some ({ … })`: the right side is wrapped in `Ann(…, Option Counter)`, because it is inferred (with a waiting literal) instead of failing and being checked [inferred] | harmless: `Ann` is erased by the kernel | none; or drop the `Ann` the group adds for an inferred leaf |
| `Day05.noRuleBroken` | `rule.before == laterPage`: `Decidable.toBool (DecEq.decide …)` instead of `Decidable.toBool (Nat.decEq …)` | **needed fix**: the same value, but the generic dictionary call where today's term has the specialised one; extraction and evaluation take the slower route | the known-instance projection decided at `finish` (§5.10) |
| `Day06.offRouteFree` | `Map.Spec.sameKey.%match1 (Position.%compare blocker other)` instead of `Map.Spec.sameKey blocker other` | **needed fix**: the placeholder is filled by reading back a value, which unfolds the call ([§5.10](#510-placeholders-filling-and-opacity-r7)) | fill placeholders with the checked term |
| `Day06.part2Correct` | inside `Eq.cong (patrolled => Option.map patrolled (visited => (visited.filter …).size))`, where `.filter` and `.size` are on a lambda parameter whose type `patrolRoute …` fixes later: the lambda's term is the one checked in place (shorter: 10,936 against 11,762 characters of `{:?}`) | harmless [inferred: the same kind as `carriesMentioned`; the kernel re-checked it against the same statement] | none |
| `Day08.harmonicsCorrect` | `stepFacts`'s motive `_` is solved to the folded goal `point ∈ City.harmonics city first second ↔ …` instead of its unfolding `point ∈ List.flatMap … ↔ …` | harmless, arguably better: definitionally equal, and as written | none |
| `Day24.carriesMentioned` | `List.memFlatMapIntro (each => [each.left, …])`: the lambda as written appears where today's term has the unifier's copy from `device.wires`'s definition (a different library call, its lambda named `gate`) | harmless, arguably better: today the in-place try fails, and the postponed lambda's own term is not what ends up in that argument [inferred] | none |
| 19 others in days 5, 6, 8, 24 (for example `Day05.part1Correct`, `Day24.shapeAdds.%match3`) | identical terms | harmless: they refer to a changed declaration | none |

All 24 aoc declarations are in `Proofs` namespaces: proof terms, re-checked by the kernel against
statements whose types are compared in [§6.3.1](#631-statements). None of the 26 is a sign that
the design is wrong. Two are bugs of the prototype that the design rules out (§5.10, both the
fill and the projection).

#### 6.3.1 Statements

The types (statements) of all 26 changed declarations were compared as exact terms: **all 26
are identical** with the switch off and on **[measured]**. So every change is in a body, and
for the 24 proofs a body is any term the kernel accepts for the same statement.

#### 6.3.2 Answers and behaviour

With the prototype on (W1 scoped, W2), `stitchwort test` passes all **914 AoC tests** and all
**100 roguelike tests** **[run]** (65.6 s and 8.8 s, none from the cache, since the worktree had
no test cache).

### 6.4 CPU time

Single-threaded, in process, seconds, two runs each (off / on) **[measured]**:

| | std | accept | reject | extract | aoc | rogue | whole run (user CPU) |
|---|---|---|---|---|---|---|---|
| run 1 | 4.61 / 4.59 | 2.52 / 2.50 | 1.53 / 1.51 | 0.56 / 0.56 | 38.28 / 35.87 | 2.31 / 2.34 | 50.66 / 48.17 |
| run 2 | 4.57 / 4.56 | 2.52 / 2.53 | 1.52 / 1.52 | 0.56 / 0.56 | 37.99 / 35.98 | 2.31 / 2.35 | 50.32 / 48.28 |

aoc is 5-6% faster: fewer failed tries and reruns. The rest is within noise.

### 6.5 Variants

| configuration | result **[run/measured]** |
|---|---|
| W3 and W4 only (`STITCHWORT_QUEUE=1`) | std doesn't load: `Map/Spec.sw:1862`, `E-TYPE-MISMATCH` |
| W1, W3, W4 (`…_APP=1`) | aoc fails: `Day08/Proofs/Part2.sw:148`, `E-MATCH-MOTIVE` |
| W1-W4, unscoped (`…_LIFT=1`): **the measured prototype** | as §6.2-6.4 |
| W1-W4, field-name rule at the literal (`…_NAMES_FIRST=1`) | "in a list" passes; "the other side says" and "appended" fail (§5.8) |
| W1-W4, W1 scoped (`…_SCOPED=1`): **the recommended form** (D2014) | one acceptance change, `record-literal-inferred.sw` as above; `postponed-lambda-second-error.sw` stays rejected with today's error, because `c.size` is resumed only at the end of the `twice` application, outside the attempts inside it; the same 26 hash changes; no error message changed; 179 items queued, 136 resumptions (149 unscoped); aoc 36.7 s against 38.0 s off (one run) |
| scoped, `.field` as syntax when its blocker predates the receiver (draft 3) | identical to the line above: every outcome, every hash (§6.7) |
| scoped, placeholders frozen (draft 3) | 1 accepted example and 4 aoc proofs fail (§5.10, §6.7) |

### 6.6 The work this implies

From §6.2-6.7, for the end state:
1. **Fill placeholders with the term**, through a placeholder table zonked as `lifted_calls`
   is (§5.10).
2. **Resume points W1 and W2**, scoped (§5.6).
3. **K4 and the defaults ladder** (D2013), which fixes `record-literal-inferred.sw`.
4. **The known-instance projection at `finish`** (`Day05.noRuleBroken`, §5.10).
5. **K2's receiver as syntax** when the blocker predates it (§5.5).
6. **K3** for sections, which removes the last 6 lambda postponements in accepted code.
7. **Examples**: rewrite `record-literal-inferred.sw`'s "in a list" with an annotation until K4
   (stage 2), unannotated after; move `section-unknown-receiver.sw` to accept after K3.
8. **The retry paths of §5.11**, removed once 3 and 6 are in.

### 6.7 Draft-3 runs

**What was run.** The prototype patch applied to `fcb12746` in a scratch worktree (removed
after), with counters added in `dot.rs`, `queue.rs` and `interfaces.rs` (not kept), and two
switches: `STITCHWORT_QUEUE_RESYNTAX=1` (a `.field` whose blocker predates its receiver restores
the snapshot taken before the receiver and is queued as syntax, resumed by `infer_call`) and
`STITCHWORT_QUEUE_FREEZE=1` (placeholders frozen until filled). The measurement test ran four
times, each under `dev/memguard --cap-gb 2` and `timeout`: off, scoped (W1 scoped, W2),
scoped + resyntax, scoped + freeze; about 50 s each. The three repros with tests ran with
`stitchwort test` under scoped + resyntax. Output: [postponement/prototype/draft3-counts.txt](postponement/prototype/draft3-counts.txt).

**Results** **[measured, run]**:
- K2 receivers: as in §5.5's table; the counters "receiver defaulted a number", "receiver chose
  a generic dictionary" and "`insert` would add at resume" are all 0;
- **scoped + resyntax against scoped: 0 outcomes and 0 hashes changed**; 131 `.field`s queued
  as syntax; the same 179 items, 136 resumptions, 4 defaults and 4 stuck; sw817run, sw847run
  and sw885run pass all 6 of their tests. Since every declaration's hash is the same, so is
  every term, so the AoC and rogue tests of §6.3.2 hold unchanged [inferred from the hashes;
  not re-run];
- **fills**: 135, of which 14 found the placeholder already solved by unification (10 in aoc,
  3 in `lambda-postponed-dependent.sw`, 1 in `lambda-postponed-dependent-argument.sw`);
- **scoped + freeze**: 0 fills found it solved, and `lambda-postponed-dependent.sw` and aoc fail
  (4 errors, 7 declarations without a hash, in 2024 days 9 and 24);
- **generic dictionary calls**: 486 off, 487 scoped.

## 7. Risks

- **Order-dependence through defaults and `true`/`false` unification.** The ladder is
  deterministic (creation order, priorities), not order-free as OmniML is. The two acceptance
  changes of §6.2 are both order effects. The defaults' priorities are a design choice (D2013).
  The review separates kernel soundness (the kernel gives it), coherence (scheduling choosing
  between two well-typed elaborations) and predictability; invariants 3, 6 and 8 are what
  protect coherence.
- **Resumption inside attempts.** An item resumed inside an attempt that then fails is undone
  and resumed again later. That is correct, and scoped resume points (invariant 3) keep it from
  changing which route survives: the one example where it did, unscoped, stays rejected.
- **Placeholders seen by comparisons.** A comparison that meets an unfilled placeholder may
  solve it (14 times in the corpus) or fail where today's order succeeded. W1 covers the
  corpus; new code may find more. The follow-up is tri-state unification (§5.13), with its
  trigger counted from stage 1.
- **The allowed choices of §5.10** (`if`'s reading, `in`'s container) can reject a program
  whose placeholder would have said otherwise. Each such program fails today; the error moves
  from `E-CANNOT-INFER` to a mismatch at the item.
- **Lifted helpers.** A placeholder must not reach `lift`. W2 handles `lift` and
  `lift_signature`; other places that zonk mid-declaration (`settle_let_lambda`, `decreasing`'s
  and `partial`'s callers of `finish`) must each be checked [inferred].
- **Saved contexts.** `Ctx::save` clones the context's vectors. Fine for 179 items; a
  declaration with thousands would want persistent vectors [inferred].
- **A new attempt site that breaks T1** (an unbounded retry) would make termination rest on the
  step budget alone. The review rule in `undo.rs` and the elaborator fuzzer's watchdog guard it
  (§5.7).
- **Interaction with SW-805.** The rule must stay a name rule (D1991's R1). Running it as a
  default doesn't change what it looks at. If it ever checks fields against candidate types,
  D2013's order is revisited (§5.8).

## 8. Stage plan

Accepted-program identity is no longer a requirement. Each stage must keep every test, every
example's expectation (accept, reject with its code, extract output), every AoC answer and
every rogue test right. A changed hash is fine; each changed hash is listed in the stage's
commit with its kind from §6.3, and the snapshots are re-baselined. The review calls the staged
rollout "sensible, including only removing each old path after its counter reaches zero".

**Stage 1: the queue, its invariants and its placeholders, nothing queued yet.** The table,
`Ctx::save`, item states and the resumption log, `Snapshot` and `rewind` handling, the ladder at
W1-W4 (scoped), the placeholder table (filled with the term, zonked as `lifted_calls` is;
solvable by unification and checked at the fill, D2016), the stuck report by root (first root
as the error, up to two more through `branch_errors`), debug assertions for invariants 3, 4 and
6, and counters in `STITCHWORT_TIMINGS` (items queued, resumed, defaulted, stuck; comparisons
that met an unfilled placeholder; fills that found it solved). The review rule for attempt sites
(T1) goes into `undo.rs`'s module comment. As a separate commit, the **known-instance
projection at `finish`** for operator dictionaries (§5.10), with its own hash list.
*Shown right by:* every hash and every error unchanged by the queue commits (nothing is queued
yet); the projection commit's hash list, each one a generic call becoming its specialised form;
the unit tests of §9 for invariants 1, 2, 4 and 5.

**Stage 2: K1 and K2, with the field-name rule as the default.** K2 with the receiver rule of
§5.5. *Changes:* the 26 hashes of §6.3, minus `Day06.offRouteFree`'s unfolding (stage 1's fill)
and `Day05.noRuleBroken`'s (stage 1's projection); `record-literal-inferred.sw` "in a list" fails
until stage 4, so stage 2 rewrites that one test with an annotation (`(p: Position) => p.row`)
and stage 4 removes it. With W1 scoped, no reject example changes. The ticket repros become
accept examples: `postpone-record-literal-argument.sw` (sw817), `postpone-let-lambda-field.sw`
(sw847), `postpone-effectful-record.sw` (sw885's four cases, with the run-time tests of §1).
*Shown right by:* the merge tier; `task test:aoc` and rogue's tests with every answer unchanged;
`task snap:examples` writing no changed error message; the hash diff matching the stage's list;
§9's must-hold tests for invariants 3, 6 and 8.

**Stage 3: K3, method sections.** **Also (D2035, Matt, 30 October 2026):** the choice that decides a proposition where a `Bool` is expected (`decide_to_bool`, `check.rs:4044`) waits for an unfilled placeholder, as instance search does; it was missing from §5.10's consumer list (found in stage 2: `let check := r => 3 ∈ r.items; check b` gave `E-AUTO-NONE` naming `?5 b b`). Remove the section-without-a-try path and
`section_unknown_name`'s special case. *Changes:* `section-unknown-receiver.sw` moves to accept
(D2011), with a new reject example for a section that nothing ever fixes; the 6 aoc lambda
postponements become section items, so their declarations may change hash.
*Shown right by:* as stage 2, and the lambda try-then-postpone counter at 0 in accepted code.

**Stage 4: K4 and the defaults ladder** (D2013). Number literals wait; the number group's `Nat`
default moves into the ladder; defaults by priority. *Changes:* `record-literal-inferred.sw`'s
"in a list" passes unannotated again; hashes wherever a literal's type is now decided later (to
be measured with the prototype extended first, as here). *Shown right by:* as stage 2, plus the
numbers examples (`examples/accept/*number*`, `*literal*`) unchanged in outcome, invariant 7's
tests, and `retrying`'s counter at 0.

**Stage 5: remove the retry paths** of §5.11: the lambda try-then-postpone, `retrying` and
`late_literals` with `defers_literal`, `else_first` and `check_items`' reordering, `held`,
`last_resort` and `FieldNames`, the three "infer the other side" catches. This also removes two
of T2's three same-state reruns (§5.7). *Shown right by:* as stage 2; each removal is its own
commit with the counters at 0 first.

**Stage 6: tri-state unification (expected follow-up, R4).** `unify` answers `Yes`, `No` or
`Blocked(unknowns)`; a blocked comparison becomes a declaration-level constraint, woken when one
of its unknowns is solved; placeholders become frozen (D2016's end state); W1 may then be made
less frequent. **Triggered** when the corpus or the elaborator fuzzer produces a program whose
placeholder crosses W1 unresolved and makes a comparison fail that would succeed after the
item's resumption (stage 1's counters). The queue doesn't wait for it.

**Later, each its own decision:** queueing the after-expected path, if it ever helps (§5.11);
queueing the allowed choices of §5.10 (`if`, `in`), if a case wants it.

## 9. Tests

**Per invariant** (unit tests in `crates/elab` unless an example is named; "must hold" marks the
tests the review's points R1 and R7 depend on):

| invariant | tests | stage |
|---|---|---|
| 1. one placeholder, one occurrence | an item queued inside an attempt that is undone leaves no item or placeholder; elaborating the same syntax again makes a new item with a new placeholder | 1 |
| 2. only its item fills | a placeholder solved by unification to `t` and filled with a term equal to `t` zonks to the item's term, a call kept folded (`Map.Spec.sameKey blocker other`, the `Day06.offRouteFree` case); filled with a term not equal to `t` gives the item's mismatch at its span; `lambda-postponed-dependent.sw` and `lambda-postponed-dependent-argument.sw` (the corpus's early-solved cases) stay accepted | 1, 2 |
| 3. isolation | **must hold**: `examples/reject/postponed-lambda-second-error.sw` stays rejected with today's error; an item created outside an application isn't resumed at its W1 even when its blocker is solved there; a debug assertion that W1 selects only items made since it began | 1, 2 |
| 4. no re-entry | an item whose check contains an application is resumed once (its resumption count is 1), not again by the inner W1; a debug assertion that the ladder never selects a running item | 1 |
| 5. restore restores the queue | a snapshot's restore drops items queued and resumptions made after it; an item resumed inside an undone attempt is waiting again; `rewind` empties the queue | 1 |
| 6. kept subterms stable (R1) | **must hold**: `p => p.row` with `p`'s type fixed by a later argument elaborates to the same core term as `(p: Position) => p.row` with the annotation stripped (receiver as syntax, prefix form chosen at resume); **must hold**: `((f.x a1).x a2).x a3` with `f`'s type known only later (Lean's chained case: blocker made inside the receiver, receiver kept) is accepted with the same term as with `f` annotated; a debug assertion, and a test that triggers it with a hand-built item, that a receiver kept as a term made no choice of §5.10 from an unknown; a receiver whose resumed type has a leading implicit parameter gets it inserted (a test constructed for it; none in the corpus) | 2 |
| 7. defaults at quiescence | a waiting record literal whose type a waiting obligation fixes is resumed through the obligation, with no default (defaulted counter 0); `record-literal-inferred.sw`'s "the other side says" and "appended" pass (stage 2), "in a list" unannotated (stage 4) | 2, 4 |
| 8. opaque to choices (R7) | **must hold**: `rule => rule.before == page`, with `rule`'s type fixed later and `before : Nat`, elaborates to `Nat.decEq` (the term inspected), and so does the same with the type annotated; **must hold**: a number literal next to a waiting `.field` in a group, `p.x + 1 == 3` with `p.x : Int` fixed later, is accepted as `Int` (stage 4; before it, rejected with a mismatch at the item, never accepted as `Nat`); `x in r.items` with `r`'s type fixed later to a record whose `items` is a set: rejected with a mismatch at the item, not accepted with a list (the allowed class) | 1, 2, 4 |

**Others:**
- **Repros become accept examples** (stage 2), with run-time tests as in §1.
- **Reject examples** pinning the stuck report: `record-literal-without-type.sw` unchanged; a
  literal whose type is fixed to a non-record (`E-NOT-A-RECORD` at the literal, its own error
  at resume); a `.field` whose receiver's type becomes a record without that field
  (`E-UNKNOWN-FIELD` at the field, against the type now known); a declaration with two
  independent stuck items (two errors) and one with a chain of three (one error).
- **Order examples**: "in a list" from `record-literal-inferred.sw`, unannotated (stage 4); two
  literals in one application where only the second's type is fixed by a later argument.
- **Termination**: the elaborator fuzzer (`task fuzz:elab`) at each stage, which checks that
  every mutated example finishes within its step limit and watchdog.
- **Counters** in `STITCHWORT_TIMINGS`: items queued, resumed, defaulted, stuck; comparisons
  that met an unfilled placeholder; fills that found it solved; each retry path's firings until
  stage 5 removes it.
- Lane tier for each stage, the merge tier at merge; AoC and rogue tests at each stage.

## 10. Decisions for Matt

**D2013. Run SW-805's field-name rule as a default in the queue's ladder, and default number
literals in the same ladder after it, instead of at the literal?** **Decided: yes (Matt, 30 October 2026).** In the end state a record
literal or a number literal whose type is unknown waits. When nothing else makes progress at the
end of the declaration, the ladder applies one default, the field-name rule first, then `Nat` for
a number, and goes round again. **[Recommend yes.]** **The reviewer agrees**: "for current
Stitchwort: record identity first, Nat last", because the field-name rule looks at names only, so
a number's type gives it no evidence; revisit if record inference ever checks fields against
candidate types (§5.8). The assumptions, in full:
- **(R1, from D1991)** The field-name rule looks only at the literal's field names and the names
  in scope at the literal, never at types learned later; running it later doesn't change what it
  looks at, only whether something else decided first.
- **(N1)** A number literal that waits ends with the type the rest of the declaration fixes, and
  `Nat` where nothing does. So in a program accepted today, where each such literal was made
  `Nat` and everything else agreed with that, it still ends as `Nat`; the change only accepts
  programs that fail today because a literal was made `Nat` too early. Stage 4 tests this over
  the corpus [inferred, not yet measured: K4 is not in the prototype].
- **(N2)** The field-name rule has priority over the number default because a record's field
  types say what its numbers are, never the reverse (§5.8's "in a list").
- **(N3)** Lean's numeral default is the precedent: low priority, in the ladder
  (`Prelude.lean:1411`, `SyntheticMVars.lean:237-243`).

The alternative is Agda's order, the rule at the literal when it finds one type. The prototype
shows it breaks `held`'s two tests unless `held` and `last_resort` stay, which keeps a second
mechanism.

**D2014. Resume queued checks at the end of every application, scoped to the items made inside
it, as well as before lifting and at the end of the declaration?** **Decided: yes (Matt, 30 October 2026).** This is instead of only at
the end of the declaration (Lean's definition-level ladder, Agda's freeze) or inside the unifier
when the blocker is solved (Agda's wake-up). **[Recommend yes.]** **The reviewer agrees, and
would make the scope non-negotiable**: unscoped, postponed syntax "can run inside speculative
attempts that are later rolled back and then run again under a different interpretation", so
"the scope isn't merely an optimisation. It's an elaboration isolation boundary" (invariant 3).
The reviewer also says W1 is "a pragmatic substitute for many cases, but not a complete
substitute" for waiting comparisons, which is stage 6. The assumptions, in full:
- **(S1)** Stitchwort's unifier can't wait: a comparison that meets an unfilled placeholder
  answers at once, solving it if it can as any unknown (14 times in the corpus) or `false`, and
  its caller takes another route. So a placeholder must be filled before the comparisons that
  would need it. The end of the application that created it is the first fixed point after the
  later arguments that may solve its blocker, and before the application's type is compared
  with what is expected of it. The prototype shows the end of the declaration is too late for
  std (`Map/Spec.sw:1862`), and the end of each application is enough for the whole corpus.
- **(S2)** Scoping to the application's own items keeps a failing item from being blamed on, and
  undone with, an attempt it doesn't belong to, as Lean's `withSynthesize` does; items from
  outside are resumed at their own application's end or at the declaration's. With the scope,
  `postponed-lambda-second-error.sw` keeps today's outcome; without it, it doesn't.
- **(S3)** Waking inside the unifier would elaborate syntax in the middle of a comparison that
  callers inside many of the 42 `Snapshot::take` sites and 48 `transaction`/`attempt` calls
  branch on; resume points give the same order at fixed places.
- **(S4)** If tri-state unification (stage 6) is added, W1 can become less frequent; this
  decision doesn't preclude that.

**D2016. Keep placeholders solvable by unification until unification can wait (stage 6), and
freeze them only then?** **Decided: yes (Matt, 30 October 2026).** The review suggests opaque placeholders, as Lean's synthetic-opaque
postponed metavariables (`TermElabM.lean:1458`). For *elaboration choices* draft 3 adopts that
(invariant 8, §5.10). For *unification*, the alternative is to freeze each placeholder until its
item fills it, with Stitchwort's existing frozen metavariables (`globals.rs:427-432`). Measured
(§6.7): 14 of 135 fills found the placeholder already solved by a comparison, and freezing makes
those comparisons fail, breaking `lambda-postponed-dependent.sw` and four AoC proofs (2024 days
9 and 24). **[Recommend yes: solvable now, frozen at stage 6.]** The assumptions, in full:
- **(P1)** A placeholder that unification solves is solved by a pattern solution forced by the
  comparison that found it (other comparisons are put aside or answer `false`,
  `unify.rs:30-80`), so the solution is a constraint the item's result must meet anyway, not a
  guess.
- **(P2)** The fill compares the item's term with any such solution, and a disagreement is the
  item's error at its own span; so solving early can reject a program only where the item's
  result contradicts a comparison the program makes, which would be an error anyway.
- **(P3)** Zonking writes the item's term from the placeholder table, never the unifier's
  solution, so the term is what was written (invariant 2), whoever solved the unknown first.
- **(P4)** A frozen placeholder needs comparisons that can wait: with a unifier that answers at
  once, a comparison that meets a frozen placeholder fails where the program is correct, which
  the 5 measured failures show. Once stage 6's `Blocked` exists, those comparisons wait for the
  fill instead, and freezing costs nothing.

The alternative, freezing now, would need stage 6 before stage 2, or would reject 1 example and
4 AoC proofs that today's compiler accepts.

**Caveat to P1** (orchestrator, 30 October, from the elaboration register §5.2): P1 holds for pattern solutions, but the unifier is also *lossy*: two calls of the same definition stuck on an unknown have their arguments equated (`unify.rs:929-944`), which for a non-injective definition picks one of several solutions. Such a solution could reach a placeholder as a guess, not a forced constraint. The fill (P2) would then report a disagreement at the item on a correct program: an incompleteness, never unsoundness, since the item's term is checked and the kernel re-checks everything. None of the 14 measured fills was solved this way. Stage 1 counts fills whose placeholder was solved through the lossy rule, and its tests include a constructed case (a non-injective definition stuck on the placeholder) to show what happens.

**Decided** (Matt, 30 October 2026): D2013, D2014 and D2016, all yes. None is open.

## 11. The prototype

**Where.** Scratch commit `8204158e` on `worktree-agent-a90adb251a628a470`, **dropped** before
draft 2 was committed: it was built to measure, not to keep (it scans the queue, unifies to
fill placeholders, and counts retry paths with the switch off too). Its whole diff, with the
measurement test (`crates/driver/tests/queue_scratch.rs`) and scripts (`dev/queue-prototype/`), is
[postponement/prototype/queue-prototype.patch](postponement/prototype/queue-prototype.patch);
it applies to `fcb12746` with `git apply` (checked again for draft 3).
It adds `crates/elab/src/queue.rs` and touches `check.rs` (`Ctx::save`, the W1 point, retry
counters), `records.rs` (K1 sites, `infer_literal_by_names`), `dot.rs` (K2, `resume_dot`),
`lift.rs` (W2), `auto.rs` (W3), `lib.rs` (W4, the table), `undo.rs` and `rewind.rs`.

**Switches** (all off by default):
- `STITCHWORT_QUEUE=1`: K1 and K2, W3, W4, the field-name default;
- `STITCHWORT_QUEUE_APP=1`: W1 (unscoped); `STITCHWORT_QUEUE_SCOPED=1`: W1 scoped;
- `STITCHWORT_QUEUE_LIFT=1`: W2;
- `STITCHWORT_QUEUE_NAMES_FIRST=1`: the field-name rule at the literal when it finds one type;
- `STITCHWORT_QUEUE_TRACE=1`: each item queued and resumed, on standard error.

Draft 3's runs added, in a scratch copy not kept, `STITCHWORT_QUEUE_RESYNTAX=1` and
`STITCHWORT_QUEUE_FREEZE=1` and the counters of §6.7. Each is a few lines on top of the patch:
the resyntax switch takes a snapshot before `infer_receiver` in `infer_dot`, and, when the
blocker's unknown is older than that snapshot, restores it and queues a `DotSyntax` item that
waits on that unknown and is resumed by `infer_call`; the freeze switch calls `freeze_meta` on
each placeholder when it is queued and unfreezes it in `fill`.

**Not in it:** K3, K4, the blocker index (it scans), filling with the term (it unifies), the
projection at `finish`, the root-grouped report, scoping by default.

**Outputs** kept in [postponement/prototype/](postponement/prototype/): the comparison of the
off and on runs, with the exact-term and type comparison of the changed declarations
(`changes.txt`); the queue and retry-path counters per file (`counts.txt`); draft 3's counters
and variants (`draft3-counts.txt`); and the three repros with run-time tests (`sw817run.sw`,
`sw847run.sw`, `sw885run.sw`).

## As built (stage 1)

Built in SW-817's stage-1 lane, on `ec69866e`, in two commits: the queue (`0cfa7b6b`), then the
known-instance projection at the end (`cded0c9b`). Nothing is queued yet: no construct makes an
item until stage 2 (K1, K2). Line numbers are of `cded0c9b`.

**What exists.**
- **The queue**, `crates/elab/src/queue.rs`. `Check` (`:64`) is what an item does when resumed,
  one implementation per kind (K1-K4 to come); it gives `Resumed::Done(term)` or
  `Resumed::Waiting(type)`, and may have a default (`Priority`, field names before `Nat`,
  D2013). `State` (`:110`) is waiting (on a type, whose head is the blocker), running, done or
  failed. `Queue` (`:141`) holds the items, their states and the resumption log, every state
  change with the state it replaced, as `meta_trail` does for solutions; `Queue::restore`
  (`:170`) puts states back newest first and drops the items queued since, and a fill taken back
  takes its term out of the placeholder table. `queue` (`:239`) makes an item with a fresh
  placeholder (`Ctx::fresh_meta`) and the context saved (`Ctx::save`, `Saved`,
  `check.rs:139`, `:246`). It is the `Elaborator`'s `queue` (`lib.rs:343`), emptied by
  `clear_metas` and `rewind` (`rewind.rs:150`, `:256`), recorded by `Snapshot`
  (`undo.rs:54`, `:78`, `:145`).
- **The ladder.** Step 1, `resume_from` (`queue.rs:345`): every waiting item in scope whose
  type's head is no longer an unknown, in creation order, again while any was; `resume_item`
  (`:374`) marks it running, runs its check in its saved context and fills its placeholder.
  Step 3, `apply_default` (`:470`): the first default that applies, by priority then creation
  order, undone if it doesn't apply. Step 4, `stuck_report` (`:502`).
- **The resume points.** W1: `resume_application` (`queue.rs:322`), called at the end of
  `apply_args_postponing` (`check.rs:2218`) with the queue's length when the application began
  (`check.rs:1980`). W2: `resume_before_lifting` (`queue.rs:446`) at the start of `lift` and
  `lift_signature` (`lift.rs:550`, `:566`): the obligations loop, if anything waits. W3: step 1
  at every round of `solve_obligations_until_stuck` in which no obligation is left
  (`auto.rs:108`). W4: `settle_queue` (`queue.rs:457`), from `finish` (`lib.rs:1108`): the
  obligations loop, then while anything waits one default and the loop again, then the stuck
  report.
- **Placeholders.** `fill` (`queue.rs:410`): if unification solved the placeholder first
  (D2016) the item's term must agree with that solution, or it is the item's mismatch at its own
  span; either way the term goes into `Globals::lifted_calls` as a call in the variables the
  placeholder is applied to (`placeholder_call`, `:286`), so zonking writes it wherever the
  placeholder is, with its arguments (`unify::lifted_call`, `unify.rs:1768`, now also for a bare
  placeholder, `:1857`; a helper's bare frozen metavariable is still read back, as before).
- **The lossy rule's mark** (the caveat to P1): the comparison of two stuck calls by their
  arguments (`unify.rs:981`) notes what it solved, by metavariable and place in the trail
  (`note_lossy`, `:107`); `solved_lossily` (`:124`) says whether a metavariable's current
  solution was made so; restores and `undo_since` forget what they take back
  (`forget_lossy_since`, `:134`).
- **The stuck report.** Waiting items are grouped: an item waiting on another's placeholder or
  on the unknown that is its type depends on it, and items so linked, or waiting on the same
  unknown, are one group. Each group is reported by its first item, in creation order, that
  depends on no waiting item; the first group's error is the declaration's, the next two go to
  `branch_errors`, the rest are consequences.
- **The T1 rule** for attempt sites is in `undo.rs`'s module comment.
- **The projection at the end** (§5.10, the `==` regression). `decide_eq_of` and `method_call`
  note each dictionary they leave generic (`note_operator_dictionary`, `interfaces.rs:1746`;
  `Elaborator::operator_dictionaries`, `lib.rs:527`, restored by snapshots). At `finish`
  (`lib.rs:1110`) and when lifting (`lift.rs:924`), `specialise_operators`
  (`interfaces.rs:1760`) writes each such call whose dictionary is by then a global instance's
  record literal as that instance's field applied to the operator's arguments, by the rule
  `method_call` uses when the dictionary is found at once (`projected`, `:1823`). A dictionary
  that is a local variable, a superclass projection of one, or a record whose field isn't a
  definition stays generic, as before. A dictionary found in scope (§5.5 step 4) is noted as
  such (`Elaborator::local_dictionaries`, dropped by a restore that undoes its solution) and is
  never projected: a `let`'s value is written in place of its variable, so without the note
  `let d: Add Nat := pick; x + x`, with `pick`'s own dictionary found later, was projected to
  `Nat.add` (driver test `a_local_dictionary_not_yet_settled_is_used`, broken by stage 1).

**Invariants, how each is kept and tested.** Debug assertions run in debug builds only (the
lane tier builds with `--release`); the queue's tests were run both ways.

| invariant | kept by | debug assertion | tests (`queue.rs` unless named) |
|---|---|---|---|
| 1. one placeholder, one occurrence | a fresh unknown per item; a restore drops the items queued since | after a restore no item outlives its placeholder; a placeholder is filled once | `restoring_takes_back_items_resumptions_and_fills` |
| 2. only its item fills | `fill`, only from `resume_item`; the term recorded for zonking | only a running item fills | `a_fill_that_disagrees_with_unification_is_the_items_error`; `a_filled_placeholder_zonks_to_the_items_term` (`two`, not `S (S Z)`); `a_filled_placeholder_is_its_term_in_the_arguments_it_is_given`; `lambda-postponed-dependent.sw` and `-argument.sw` stay accepted (the examples test) |
| 3. isolation | W1 resumes from the length at the application's start; W2-W4 are declaration-level | W1's start is within the queue | `the_end_of_an_application_resumes_only_its_own_items`; `postponed-lambda-second-error.sw` keeps its error (the examples' snapshots) |
| 4. no re-entry | states; only waiting items are selected | no item in a resume point's scope is running (T3) | `an_item_whose_check_has_an_application_is_resumed_once`; `a_running_item_is_never_selected_again` (in a debug build it expects the assertion's panic, in release that the item isn't selected again); `an_item_that_meets_another_unknown_waits_again` |
| 5. restore restores the queue | the resumption log, in every snapshot; `clear_metas`, `rewind` | as 1 | `restoring_takes_back_items_resumptions_and_fills`; `clearing_and_rewinding_empty_the_queue` |
| 6. kept subterms stable | about what K2 keeps: stage 2 | stage 2 | stage 2 |
| 7. defaults at quiescence | only `settle_queue` (W4) applies one, after the obligations loop | a default solves what its item waits on | `defaults_apply_one_at_a_time_field_names_before_nat` (W1-W3 apply none; then field names, resume, `Nat`, resume) |
| 8. opaque to choices | the projection at the end, for operators | none | `crates/driver/tests/interfaces.rs`, `an_operator_whose_dictionary_is_found_later_is_projected_too` |
| §5.9 report | `stuck_report` | none | `stuck_items_are_reported_by_root_at_most_three` (a chain of three reports its root; four independent items report two more, through `branch_errors`) |
| caveat to P1 | `solved_lossily` | none | `a_placeholder_guessed_by_comparing_calls_is_counted`: `pred` ignores its second argument; `pred x ?p` against `pred x Z` solves `?p` with `Z`; the item's `two` would do as well (`pred x two` and `pred x Z` are the same stuck term), but the fill reports a mismatch at the item, and the lossy counter counts it. An incompleteness on a right program, as the caveat says, never unsoundness |

**Counters**, printed with `STITCHWORT_TIMINGS` after the `wall` line (`timings.rs:294`), and
readable as `stitchwort_elab::queue_counts()`. Process-wide, attempts undone included:
```
postponement queue: 0 queued, 0 resumed, 0 defaulted, 0 stuck, 0 crossed W1, 0 solved first, 0 lossy, 0 disagreed, 0 read back
```
- `queued`, `resumed`, `defaulted`, `stuck`: items made, resumptions, defaults applied, items
  still waiting at a stuck report;
- `crossed W1`: items still waiting at the end of the application they were queued in, each
  counted once. This is the first half of the stage-6 trigger (§5.13): a placeholder that
  crosses its W1 is one a comparison may meet before its item can say what it is;
- `solved first`: fills whose placeholder unification had solved already (D2016; 14 in the
  prototype), and of those `lossy`, solved by comparing two stuck calls' arguments (the caveat
  to P1; 0 expected);
- `disagreed`: fills whose term disagreed with that solution (each is an error at the item);
- `read back`: fills whose term couldn't be written as a call of the placeholder (a `let`'s or a
  split variable's value that isn't in the placeholder's variables either), so zonking reads the
  solution back, as for any unknown.

All are 0 over the corpus in stage 1, since nothing is queued.

**Identity checks.** Run on the queue commit, then again on the projection commit:
- every declaration's hash with std and every library file plus aoc (10,420 declarations), and
  plus rogue (5,164), dumped sorted by a scratch test (not committed; `Session::eager_for_stack`
  and `load_project`, as hash_stability's `dump`, which itself fails on main today with
  `E-RESOURCE` on its default stack) from main `ec69866e` before any change and from each
  commit: **byte-identical** both times;
- `hash_stability` and the examples test (`crates/cli/tests/examples.rs`: accepted, rejected,
  goal and soundness examples and projects, with every error-message snapshot) at
  `STITCHWORT_TIER=full`, every file rather than the lane's quarter: **unchanged** on the queue
  commit; on the projection commit one hash changes, below, and no error message;
- `stitchwort check --no-cache` and `stitchwort test` in `aoc/` (135 namespaces, 914 tests) and
  `games/rogue/` (3 namespaces, 100 tests): pass on both commits.

**The projection's hash list:** one declaration of all of the above.
`examples/accept/effect-rows-uses.sw`, test "a pure use on a computed receiver", `(if useFirst
then [1, 2] else [3]).map (n => n * n) == [1, 4]`, whose `DecEq` instance waits for the row to be
defaulted: `Decidable.toBool (DecEq.decide [List Nat] [List.instDecEq [Nat.instDecEq]] …)`
becomes `Decidable.toBool (List.decEq … Nat.decEq …)` (the definitions its body mentions,
compared with the projection switched off in a scratch build). Generic to specialised, as
expected; its tests pass. Every other generic operator call at `finish` in std and aoc has a
dictionary that is a local variable, a superclass projection `Ord.%eq` of one, or a record whose
field isn't a definition (1,425, 234 and 66 matches of the pass in a scratch-instrumented `aoc`
check, a call matching once per application node of it, so about a third as many calls; the
commit message calls the matches "calls"), so none changes. `Day05.noRuleBroken`, the case
§6.3 found, only goes generic with K1 and K2 on; the driver test above covers that shape (an
operator whose dictionary is found later), and shows the generic `DecEq.decide [Nat]
[Nat.instDecEq]` without the projection.

**Timing**, `stitchwort check --no-cache` in `aoc/`, user + system CPU, alternating main's
binary (`/Users/matt/repos/mdr/stitchwort/target/release/stitchwort`, the same crates as
`ec69866e`) with the lane's, on a shared machine (load average 5-6):
- queue commit: main 35.99, 36.10, 36.17 s; lane 35.95, 35.92, 36.01 s;
- projection commit: main 37.00, 37.52, 36.53, 37.78, 37.83, 37.70, 37.61 s; lane 38.37, 36.92,
  39.21, 40.53, 37.94, 37.68, 37.84 s. The lane's spread is the machine's: the projection pass
  itself, timed in a scratch build, ran about 4,200 times in that check for about 5 ms in all.

**Deviations from the note, with why.**
1. **W1 runs ladder step 1 only**, not step 2. A round of obligations and rows at an
   application's end would solve obligations made outside the application, which invariant 3
   forbids, and the measured prototype's W1 only resumed. W2-W4 run steps 1 and 2 (W3 is
   inside the obligations loop; W2 and W4 run that loop). If stage 2 finds an item at W1 that
   only an obligation made inside the application would unblock, the round can be scoped to the
   obligations made since the application began, as `retry_rows_from` is for rows.
2. **W2 applies no default.** The ladder and the task say defaults are W4's only; the prototype
   applied them before lifting too. The failure W2 exists for (`Day08/Proofs/Part2.sw:148`, a
   record literal holding a `match`) has to be checked in stage 2: if that literal is resumed by
   step 1 there, nothing changes; if it needs its field-name default first, W2 needs one.
3. **No blocker-to-items map.** A resume point scans the items in its scope in creation order,
   which with nothing queued is a length comparison, and with items is one forced head per
   waiting item (the prototype scanned too). §5.3's map, from `meta_trail`, is worth adding
   only if a declaration's queue gets long.
4. **No counter of comparisons that met an unfilled placeholder** (§5.13, §8): the unifier
   doesn't know which unknowns are placeholders, and telling it is stage 6's change. `crossed
   W1` counts the placeholders such a comparison could meet; stage 2 can add the comparison
   counter where that is non-zero.
5. **A placeholder's term mentioning a `let`'s or a split variable** is written with that
   variable's value, read back folded, where the placeholder isn't applied to the variable
   (fresh metavariables leave those out of their spines); zonking may fold a `let`'s value back
   to its name. One whose value isn't in the placeholder's variables either falls back to
   reading the solution, counted as `read back`.
6. **The stuck report's dependency** is the two direct links (another item's placeholder, or
   its type's unknown) plus a shared blocker, not "solved only through it" in general. Each
   group is reported by its first *root* in creation order, which is the note's "first item"
   in every case the note gives, and the review's choice where they differ.
7. **Invariants 6 and 8's assertions** wait for the kinds they are about (K2's kept receiver;
   the choices of §5.10 a kept receiver could make): stage 2. §8 listed 3, 4 and 6 for stage 1.
8. **The lossy mark is thread-local**, in `unify.rs` beside its other comparison state, keyed by
   metavariable and place in the trail: a debug count, never acted on.
9. **The projection runs at `finish` and when lifting only**, not in every zonk: the zonks that
   read a type to decide something (`find_ready_dictionaries`, `effects.rs`, `defaults.rs`) see
   the terms they saw before.

## As built (stage 2)

Built in SW-817's stage-2 lane, on `85af9c08`, in four commits: the hash dump fixed (SW-906,
`0caa1f93`), K1 and K2 (`b0ea8c3b`), the assertions and the counter (`ffcff48e`), the tests and
examples (`9c95bf57`); this section is the fifth. Line numbers are of `9c95bf57`.

**What changed.**
- **K1, record literals** (`crates/elab/src/records.rs`). A literal inferred (`infer_literal`,
  `:792`) or checked against a type whose head is an unknown (`check_record`, `:886`) is queued
  by `queue_literal` (`:843`) as a `Literal` (`:806`) waiting on that unknown; `infer_literal`
  gives it a fresh unknown type first. Resumed, it is `check_record` at the type now known. Its
  default (`:821`, priority `FieldNames`, D2013) is SW-805's field-name rule: the one record type
  in scope by its short name with exactly the literal's fields, with fresh parameters, unified
  with what the literal waits on; the ladder applies it at W4 only. A literal still waiting at
  the end is reported with the rule's error, the candidates noted as before. A literal waits
  whether or not `held` holds the rule back, so `FieldNames::hold` is no longer reached and
  `last_resort` never reruns; stage 5 removes them.
- **K2, `.field` and dot calls** (`crates/elab/src/dot.rs`). The type-head view reports the
  unknown it meets (`Step::Unknown(m)`, `find_or_block`, `:668`, `:724`). `infer_dot` (`:269`)
  and `infer_call` (`:1881`) elaborate through `dot_or_block` (`:301`) and `call_or_block`
  (`:1894`), which give the stop to their caller instead of failing, and `queue_call` (`:434`)
  queues a `DotCall` (`:414`) by §5.5's receiver rule (`keep_receiver`, `:463`): a blocker
  numbered below the snapshot taken before the receiver was made before it, so the snapshot is
  restored and the receiver kept as syntax; otherwise the receiver's term is kept. Resumed
  (`:478`): from syntax, by the entry it came in by (`Route`, `:363`: `infer_call`, which picks
  the prefix form or the dot form then, or `infer_dot` for `x |> r.g` and the effect pass's
  call heads); with the term kept, `insert` and then the view and the call (`dot_on`, `:326`).
  The call's implicit arguments are inserted unless its placeholder's type is still unknown or
  itself takes them. A call with an argument already elaborated (piped in, or a parameter's
  default) doesn't wait: it is the error it was.
- **Waiting again** (§5.7, T4's second measure). A resumption that meets another unknown applies
  the same rule to it: the receiver undone and `Resumed::Waiting`, or, where the receiver (made
  again from syntax, or given implicit arguments at resume) made the new unknown,
  `Resumed::WaitingAs` (`queue.rs:106`), a check holding that receiver from then on. The check
  is part of the state (`Queue::check`, `:263`), so a restore takes it back with the resumption.
- **Filling** (`unify.rs:1861`). A filled placeholder's term may mention unknowns solved after
  the fill (a literal's type parameters, `({ label = "n", contents = 5 }).contents`); zonking
  the placeholder's call now zonks the term in its own variables first. A lifted helper's call,
  zonked before it is recorded, is unaffected.
- **Invariant 6's assertion** (`queue::kept_receiver`, `:655`, called from `keep_receiver`,
  `dot.rs:473`): a receiver kept as a term made no number literal `Nat` at once (the
  `defaulted` list) and left no operator with a generic dictionary, since the snapshot before
  it (`Snapshot::metas`, `::defaulted`, `undo.rs:92`, `:98`). A debug assertion; counted in
  release. *Note, 12 November 2026 (SW-3045): the generic-dictionary clause was dropped from
  the assertion and from `kept chose`. Since stage 1's projection at `finish`, such a dictionary
  is no choice from an unknown: it is found by the same search and projected by the same rule
  as with the type known at once, and the clause fired in a debug build on std's
  `Int.toIntSumBy` (receivers shaped like `((x => x * x) 3).toInt`). The assertion now checks
  number literals defaulted only. Stage 2's "`kept chose` is 0 everywhere" predates that case.
  Review: `docs/reviews/SW-3045-invariant-6-review.md`.*
- **Invariant 8's assertions**, for the consumers of §5.10 that K1 and K2 meet: the field-name
  rule chooses a type only as W4's default (`Queue::settling`, `queue.rs:181`, set by
  `settle_queue`, `:517`; asserted in `Literal`'s default, `records.rs:824`); a resumed call
  has its implicit arguments before it fills a placeholder that doesn't take them
  (`dot.rs:538`). The others are stage 1's (operators decided at `finish`) or later stages'
  (sections, numbers).
- **The counter stage 1 couldn't add** (its deviation 4): the unifier now knows the unfilled
  placeholders, a thread-local set (`unify.rs:110`) that `Queue::sync_unfilled` (`queue.rs:230`)
  keeps in step with every state change, restore and clear; a comparison that fails at a pair
  one side of which is headed by an unfilled placeholder, or is a definition stuck on one, is
  counted (`note_unfilled`, `unify.rs:135`). New counters: `met unfilled`, `requeued`, `kept`
  and `kept chose` (`queue::counts`, `queue.rs:683`).
- **SW-906**: `hash_stability`'s `dump` runs on a 64 MB thread with `Session::eager_for_stack`,
  and takes `HASH_DUMP_PROJECT`; on main it failed with `E-RESOURCE` in Day22's `part1Correct`
  **[run]**. How to run it: docs/testing.md, "Hash dumps".

**Hash changes**, against `0caa1f93` (std + aoc, 10,420 declarations; std + rogue, 5,164; the
accepted and extract examples at `STITCHWORT_TIER=full`), each changed term compared exactly
with a scratch test (not kept) on the base and the lane **[measured]**:

| declaration | what differs | kind | in §6.3 |
|---|---|---|---|
| `safe-fields.sw` "record equality", "record inequality" | the right side of `==` wrapped in `Ann(…, Option Counter)`, since it is now inferred with its literal waiting | harmless: `Ann` is erased | yes |
| `record-literal-inferred.sw` "the other side says" | the same `Ann`, around `Some ({ value = one })` | harmless | no: the prototype rejected this file ("in a list"), so its hashes weren't compared |
| `record-literal-inferred.sw` "appended" | the `Ann` moves from the right operand of `++` to the left: the left now infers, with its literal waiting | harmless | no, as above |
| `Day08.harmonicsCorrect` | `stepFacts`'s motive solved to the folded goal, `City.harmonics city first second`, not its `List.flatMap …` unfolding | harmless, arguably better | yes |
| `Day24.carriesMentioned` | the lambda as written (`each`) and `List.flatMap`'s lemma, not the unifier's copy (`gate`) through another library call | harmless, arguably better | yes |
| `Day08.part2Correct`; `Day24` `adderAdds`, `part2Correct`, `part2Sound`, `part2Sound.%match1`, `shapeAdds`, `shapeAdds.%match3` | identical terms: each refers to a changed declaration | harmless | yes |

**13 changes: 4 example tests and 9 aoc declarations; std, rogue, the extract examples and
every other accepted example unchanged.** Against §6.3's 26: Day05's 9 (`noRuleBroken` and the
8 that refer to it) and Day06's 5 (`offRouteFree` and the 4 that refer to it) are gone, as
expected, since stage 1 fixed both causes; the 2 `record-literal-inferred.sw` tests are new.
**`Day06.part2Correct`, which §6.3 found changed in its own term, is unchanged**: the lane's term
and the base's are identical but for `Loc` wrappers **[measured]**. [inferred] SW-822 part 1
(`47a6ec9b`, after the prototype's base) makes a lambda argument wait for the later arguments
when any parameter type is unknown, so that lambda is no longer tried in place and its `.filter`
never meets an unknown. "In a list", annotated, has the hash it had unannotated (identical
terms but for `Loc`), as §9's first must-hold for invariant 6 says it should.

**Statements, answers and errors.** None of the 9 aoc declarations' types changed (the scratch
comparison shows each type identical). `stitchwort check --no-cache` and `stitchwort test` pass
in `aoc/` (914 tests) and `games/rogue/` (100) **[run]**. `task snap:examples` at the full tier
writes no snapshot: **no error message changed**, and `postponed-lambda-second-error.sw` keeps
its error (invariant 3) **[run]**.

**Counters**, `STITCHWORT_TIMINGS`, `stitchwort check --no-cache`, each accepted and rejected
example checked on its own and summed **[measured]**:

| | queued | resumed | defaulted | stuck | crossed W1 | met unfilled | solved first | lossy | disagreed | read back | requeued | kept | kept chose |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| aoc | 117 | 94 | 0 | 0 | 15 | 8 | 10 | 7 | 0 | 0 | 0 | 21 | 0 |
| rogue | 11 | 8 | 0 | 0 | 5 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 |
| accepted examples | 149 | 133 | 1 | 0 | 80 | 2 | 4 | 3 | 0 | 0 | 0 | 2 | 0 |
| rejected examples | 105 | 88 | 0 | 8 | 66 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 0 |

- `kept chose` is 0 everywhere: no receiver kept as a term chose from an unknown (invariant 6).
- `met unfilled`: aoc's 8 are all at one place, `Day24/Proofs/Adder.sw:193`, `allMember (wire
  => wire.zBit.all (found => found ≤ bits)) …`: a chained `.field` on the lambda's parameter
  whose placeholders a comparison inside the same application meets before its W1 (found with a
  scratch trace, not kept). The declaration's hash is unchanged, so the route that survives gives
  today's term. Not the stage-6 trigger: nothing is rejected that would be accepted.
- `lossy`: **7 of aoc's 10 fills found solved first had been solved by comparing two stuck calls
  by their arguments** (Day09 `Proofs/Part2.sw:55`, `:64`, `:78`, `(free.moveFile file).snd`,
  §5.10's example; Day24 `Proofs/Complete.sw:61`, twice; Day24 `Proofs/Part2.sw:101`, twice),
  and all 7 agreed with the item's term (`disagreed` 0). The caveat to D2016's P1 expected none;
  it holds in the sense that matters (no right program rejected), but the solutions here came
  from the lossy rule, not from pattern solutions.
- The one default is `record-literal-inferred.sw`'s "a parameter is inferred", at W4.

**Timing**, `stitchwort check --no-cache` in `aoc/`, user + system CPU, alternating main's
binary (`/Users/matt/repos/mdr/stitchwort/target/release/stitchwort`, built at 17:00 on 30
October from main) with the lane's, on a shared machine (load average 5 to 19) **[measured]**: main 41.67, 41.49, 40.18 s; lane 39.84, 37.99, 37.90 s. The lane is about 5
to 8% faster, as the prototype was (§6.4): fewer failed tries.

**The Day08 literal** (stage 1's open point, its deviation 2). The literal `{ forward = …,
backward = … }` holding a `match`, now at `Day08/Proofs/Part2.sw:143` (§5.6 and §6.5 say `:148`),
is **not queued** in stage 2: a scratch trace (removed) of every item queued and resumed while
`aoc` is checked shows none at its span **[run]**; its expected type is known when it is
reached. No item anywhere in the corpus needs a default before lifting: aoc and rogue default
nothing, and the one default in the examples is at W4 in a declaration with no `match`.
**Decision: W2 keeps applying no default**, as stage 1 built it; the ladder and invariant 7 say
defaults are W4's only, and nothing in the corpus asks otherwise.

**Tests.**
- `queue.rs`, 6 new, on modules without the library: K1 waits and is checked at its type; its
  default applies only at W4, and two candidates report the rule's error; K2 on a variable waits
  as syntax, its receiver's inference undone; K2 on a waiting literal keeps it; K2 that meets
  another unknown waits again; invariant 6's assertion, made to fire by hand (in release, that it
  counts). Run in release and debug.
- `crates/driver/tests/postponement.rs`, 6, with the library, on a 64 MB thread so a debug build
  passes too: §9's must-hold tests for invariant 6 (`p => p.row` fixed later, the annotated
  term; Lean's chained `((f.x 1).x 2).x 3`, the annotated term), invariant 8 (`r => r.before ==
  page` decides with `Nat.decEq` as annotated, also with `page` fixed later; `3 ∈ r.items` with
  `r` later a record holding a set is a mismatch at `r.items`) and invariant 3
  (`postponed-lambda-second-error.sw`); and a resumed `.field` the type hasn't, or a literal
  whose type is no record, reported against the type now known at its own place.
- Accept examples, each rejected on main with `E-CANNOT-INFER`, with tests of what they
  compute: `postpone-record-literal-argument.sw` (SW-817), `postpone-let-lambda-field.sw`
  (SW-847), `postpone-effectful-record.sw` (SW-885's four cases, `Size` kept, and a fifth for
  `Size` itself).
- Lane tier `elab`, `core`, `std`, `examples`, `hashes`, `lsp`: pass; clippy and `cargo fmt
  --check` clean; `stitchwort fmt --check` clean on the new files.

**Deviations from the note, with why.**
1. **K1 and K2 are one commit.** K1 alone rejects `record-literal-inferred.sw`'s "a parameter is
   inferred", `({ label = "n", contents = 5 }).contents`: the literal waits, and the `.contents`
   on it fails until K2 lets it wait too.
2. **A `.field` waits on the bare blocker**, not on the type at the view's step: that type may
   mention what the receiver's elaboration made, which the restore takes back. A blocker solved
   as a function whose body is another unknown is resumed and waits again (`requeued`; 0 in the
   corpus).
3. **`Resumed::WaitingAs`** is new: §5.5's rule, applied again at resume, can find that the
   receiver now made the new unknown; the item then keeps that receiver. 0 in the corpus.
4. **Invariant 6's check** covers what §5.5 counted (number literals made `Nat` at once, generic
   dictionaries), not the number group's `Nat` default (`numbers.rs:944`), which leaves no
   record; that moves to the ladder with K4. *Note, 12 November 2026 (SW-3045): the
   generic-dictionary clause was dropped later, because operators are decided at `finish`
   (§5.10); see the stage 2 record above.*
5. **`met unfilled`** counts failing pairs headed by an unfilled placeholder or a definition
   stuck on one, not every comparison that meets one deeper inside.
6. **The membership must-hold test is written as a proposition** (`def has (b: Box): Prop`).
   Where a `Bool` is expected, see the first finding below.

**Findings for later.**
1. **A consumer missing from §5.10's table: a proposition where a `Bool` is expected**
   (`decide_to_bool`, `check.rs:4044`, which calls `bind::decide` at once). With a `.field`
   waiting inside the proposition, made outside the application whose type is compared (`let
   check := r => 3 ∈ r.items; check b` with `has: Bool` and `items: List Nat`), the decision
   runs before the `.items` can resume, finds nothing to decide `List.Any (y => y = 3) (?5 b
   b)`, and the declaration fails with `E-AUTO-NONE` naming the placeholder **[run]**. Main
   rejects the same program with `E-CANNOT-INFER`, so no accepted program changes and no
   example's error changes; but it is a right program the queue could accept, and the message
   shows an unknown. Either that decision waits (an obligation, as instance search does) or it is
   left to stage 6. A question for Matt, not patched.
2. **The lossy rule solves most early-solved placeholders** (7 of 10 in aoc, above). The fill's
   comparison guards it; worth keeping in view for D2016's caveat.
3. Unrelated to the queue: on main and here alike, a `let`-bound curried lambda written `r => p
   => …` with nothing known isn't inferred ("this is a function, but the expected type is `?2
   page r`"), where `r p => …` is **[run]**.

## As built (stage 3)

Built in SW-817's stage-3 lane, on `d031ca0c`, then rebased onto `06865190` (which brings
SW-910 and SW-800), in two commits: K3 and D2035 (`40651819`), then an inferred section's result
type (`936da6b9`); this section is the third. Line numbers are of `936da6b9`; "on `d031ca0c`"
marks a line of the base the lane started from. Everything below was measured on `d031ca0c` and
its lane, and the hash dumps, tests, AoC and rogue were run again after the rebase (below).

**What changed.**
- **K3, method sections** (`crates/elab/src/dot.rs`). A section checked against `dom -> cod`
  whose `dom` has an unknown at its head is queued whole by `queue_section` (`:989`), called
  first in `check`'s lambda case (`check.rs:3459`), as a `Section` (`:974`) waiting on that
  unknown. Resumed, it is `check` against the function type, now with `dom` known, so
  `section_partial` (D506) or the lambda follows exactly as when `dom` is known from the start.
  Its error, if it is still waiting at the end, is today's "can't tell what `.f` is applied to"
  (`section_unknown`, `:1010`).
- **Inferring a section** (`let g := .drop 1`, `(.length) "abcd"`) is inferring a lambda,
  `infer_section` (`check.rs:1736`, from `:1313`): its type is `(x: ?D) -> ?R`, the result not
  depending on the argument (deviation 2).
- **Removed**: the section postponed without a try (`apply_args_postponing`, `check.rs:2037` on
  `d031ca0c`, with its `dependents`); a section's own early `E-CANNOT-INFER` when inferred
  (`check.rs:1313` on `d031ca0c`) and in `find_in_view` (`dot.rs:721` on `d031ca0c`). Where a
  section's argument type is known but its view meets an unknown further on (`Id ?a`), the
  `.f` inside the lambda is now a K2 waiting with the section's message (`dot.rs:724`).
- **D2035, the decision into a `Bool`** (`check.rs`). `decide_to_bool` (`:4113`) first asks
  `queue::unfilled_in` (`queue.rs:322`) for a placeholder in the proposition's value that its
  check hasn't filled and unification hasn't solved; with one, it queues a `Decide` (`:4152`)
  waiting on it, whose placeholder is the `Bool`. Resumed, it waits on another such placeholder
  if there is one, or decides (`decided`, `:4172`, today's decision and error). `unfilled_in` is
  free while nothing waits; it reads the value back as `interfaces::unsolved_in` does
  (`scanned`, now `pub(crate)`, `interfaces.rs:1330`). §5.10's table has the consumer.
- **A counter**: `lambda postponed` (`queue::note_lambda_postponed`, `queue.rs:675`, counted at
  `check.rs:2101`), the lambda try-then-postpone path's firings.

**Hash changes: none** **[measured]**. The std + aoc (10,420 declarations) and std + rogue
(5,164) dumps of `61515018` are byte-identical to those of `d031ca0c`, taken before any
change (and after the rebase, `936da6b9`'s to `06865190`'s, below).
`hash_stability` at `STITCHWORT_TIER=full` changes only the snapshots of the two new accepted
examples. So **the 6 aoc lambda postponements that are sections, now section items, have the
hashes they had**: they were checked at the end of their application, after the later
arguments, and are now resumed at that application's W1 with the same type known
[inferred from the code, and measured as identical hashes].

**Statements, answers and errors** **[run]**. `stitchwort check --no-cache` and `stitchwort
test` pass in `aoc/` (914 tests) and `games/rogue/` (100). `task snap:examples` at the full
tier changes no error message but the planned move:
- `reject/section-unknown-receiver.sw`, `E-CANNOT-INFER` "can't tell what `.drop` is applied
  to" → accepted, as `accept/section-unknown-receiver.sw` (D2011), with run-time tests; its
  snapshot is removed;
- `reject/section-never-applied.sw`, new: a section nothing applies, `E-CANNOT-INFER` with the
  same message at its own span.

**Counters**, `STITCHWORT_TIMINGS`, `stitchwort check --no-cache`, each example checked on its
own and summed, `d031ca0c` (with a scratch build adding the counters) → `61515018`
**[measured]**. `requeued`, `read back`, `disagreed` and `kept chose` are 0 everywhere, and
`defaulted` is as in stage 2 (1, in the accepted examples):

| | queued | resumed | stuck | crossed W1 | met unfilled | solved first | lossy | kept | lambda postponed | section untried (scratch) |
|---|---|---|---|---|---|---|---|---|---|---|
| aoc | 117 → 166 | 94 → 143 | 0 → 0 | 15 → 15 | 8 → 8 | 10 → 16 | 7 → 11 | 21 → 21 | **6 → 0** | 43 → (path gone) |
| rogue | 11 → 35 | 8 → 32 | 0 → 0 | 5 → 5 | 0 → 0 | 0 → 0 | 0 → 0 | 2 → 2 | 0 → 0 | 24 → (gone) |
| accepted examples | 149 → 2,847 | 133 → 2,830 | 0 → 0 | 80 → 81 | 2 → 2 | 4 → 4 | 3 → 3 | 2 → 2 | 0 → 0 | 2,661 → (gone) |
| rejected examples | 105 → 4,182 | 88 → 4,158 | 8 → 9 | 66 → 66 | 0 → 0 | 0 → 0 | 0 → 0 | 3 → 3 | 2 → 2 | 4,070 → (gone) |

- With `--no-cache` every run elaborates the library modules it imports, and the library's own
  sections are now items (the prelude alone queues 5): that is most of the examples' rise, and
  rogue's. aoc's rise is 49: its 43 sections postponed without a try and its 6 sections tried
  and then postponed.
- **The lambda try-then-postpone counter is 0 in accepted code** (aoc, rogue, the accepted
  examples). Its 2 firings in rejected code are both `reject/lambda-body-error-against-goal.sw`,
  a proof lambda (not a section) whose `omega` fails both ways; it keeps its `E-OMEGA`.
- `solved first` +6 and `lossy` +4 in aoc, all agreeing with the item's term (`disagreed` 0):
  [inferred] the 6 sections that were tried in place because a later parameter's type mentions
  them, so the later arguments' comparisons meet, and solve, their placeholders before W1.
- In aoc and rogue the new items are exactly the sections that used to be postponed (aoc 49 =
  43 + 6, rogue 24 = 24), so no `Decide` is queued there.

**Timing**, `stitchwort check --no-cache` in `aoc/`, user + system CPU, alternating `d031ca0c`'s
binary with the lane's **[measured]**. The machine was shared (load average 5 to 45). Last set,
load 5 to 18: base 36.52, 34.61, 35.93 s; lane 34.81, 34.89, 36.47 s. Two earlier sets, under
heavier load: base 37.65, 38.32, 36.70 and 39.82, 37.95, 36.71 s; lane 42.48, 38.23, 39.66 and
41.00, 38.54, 37.26 s. Each pair within the noise of the next; no cost shows clearly.

**SW-910: stage 3 doesn't change it** **[run]**. On `d031ca0c`, `let f := r => p => r.before
== p; f r page` was `E-TYPE-MISMATCH` ("this is a function, but the expected type is `?2 r page
r`") with and without stage 3, and `r p => …` was accepted by both. SW-910's fix is in
`06865190`; after the rebase both forms are accepted by main and by the lane. The rebase's one
conflict was there: `infer_value`'s lambda case, where a section now goes to `infer_section`
before SW-910's `curried_lambda` (which already leaves a section inside a lambda alone).

**After the rebase onto `06865190`** **[run]**: the std + aoc (now 10,450 declarations) and std
+ rogue (5,164) dumps are byte-identical between `06865190` and the lane; `hash_stability` at
the full tier and `task snap:examples` change nothing further; aoc (914) and rogue (100) pass;
the lane tier, the queue's unit tests and `postponement.rs` pass; aoc's and rogue's counters are
those of the table above.

**Tests.**
- `queue.rs`, 3 new, on a module without the library, release and debug: a section waits whole
  (no `.row` queued inside it) and, its argument's type known, is `P.row` itself; one with an
  argument is the lambda; one nothing fixes, and one whose argument's type is `Id ?a`, are
  reported with the section's message.
- `crates/driver/tests/postponement.rs`, 2 new, release and debug: the section's form of
  invariant 6's must-hold (`anyOf .snd pairs`, with `.snd`'s argument fixed by the later
  `pairs`, has the hash of `anyOf Pair.snd pairs`); D2035 under invariant 8 (`let check := r =>
  3 ∈ r.items; check b` against `Bool` decides with the definitions the annotated version uses,
  and with `items` a set it is a mismatch at `r.items`).
- Accept examples `section-unknown-receiver.sw` (moved; a let-bound section, a section at an
  application's head, a section holding another, D506 with the argument fixed later) and
  `postpone-decide-waiting-field.sw` (D2035, each rejected on `d031ca0c`: `E-CANNOT-INFER` and
  `E-AUTO-NONE` naming `?5 b b`); reject example `section-never-applied.sw`.
- Lane tier `elab`, `core`, `std`, `examples`, `hashes`, `lsp`: pass. Clippy with `--deny
  warnings` and `cargo fmt --check`: clean (clippy's `err_expect` in `postponement.rs`, already
  failing on `d031ca0c`, is fixed); `stitchwort fmt --check` clean on the new files.

**Deviations from the note, with why.**
1. **K3 queues the section whole**, not as the lambda `x => x.f …` with a K2 body (§5.2, §5.4,
   §5.12). The lambda reading loses D506 for every section whose argument's type comes later:
   the K2 fills the lambda's body with `T.f x`, so `.snd` becomes `x => Pair.snd x`, not
   `Pair.snd`, and a proof that restates the program with the qualified name no longer finds it
   by the comparison `match` generalisation makes (method-sections.md §5). Run with a scratch
   switch for the lambda reading **[run]**: aoc still checks, but 12 declarations change hash
   (Day24 `Proofs`: `adderAdds`, `inputsNotZ`, `part2Correct` and its `%match1`, `part2Sound`
   and its `%match1`, `shapeAdds` and its `%match2`, `wellFormedInputs` and its `%match1`,
   `xNamed`, `yNamed`), and the driver test above fails; queued whole, none changes. The
   scheduling is K2's (wait on `?D`, resume from syntax, nothing kept elaborated, so invariant
   6 holds as for K1); only the term differs, and only for sections in D506's shape, since the
   lambda path is what `check` takes for every other section [inferred from the code]. The
   K2-inside-a-lambda form remains where `?D` is not the argument's type itself (`Id ?a`).
2. **An inferred section's result doesn't depend on its argument.** With `infer_lambda`'s
   `(x: ?D) -> ?R x`, `(.length) "abcd"` against `Nat` compares `?R "abcd"` with `Nat`, which
   nothing solves, and the declaration was `E-TYPE-MISMATCH` naming that unknown (rejected on
   `d031ca0c` too, with `E-CANNOT-INFER`). With `?R` alone it is accepted. A section whose
   result type does depend on its argument would be a mismatch at the section when resumed;
   there is none in the corpus, and every inferred section was rejected before [inferred].
3. **D2035 waits as a queue item**, not as an obligation: its blocker is a placeholder, which
   only the queue fills, and as an item it is restored by snapshots, resumed after the item it
   waits on (creation order), and in the stuck report depends on that item, so the report names
   the `.field` that couldn't be resolved, not the decision. It keeps the proposition's term,
   elaborated before it waited (invariant 6): only the decision is chosen later; what the
   proposition's elaboration chose from the placeholder's shape is §5.10's allowed class
   (`in`'s container), as the set test shows.
4. **`section_unknown_name`** keeps its message as `section_unknown`, the error a stuck section
   or a section's waiting `.f` reports; what is removed is its separate path, which failed at
   once.

## Stage 6: design (tri-state unification)

Written in SW-817's stage-6+4 lane (D2051: stage 6 first, then stage 4, one lane), on
`b6f8d2ae` (main `edd5243b` plus the `retried` counter, cherry-picked from the stopped stage-4
experiment `03d76458`). Line numbers are of `b6f8d2ae`.

**Why now.** Stage 4 (K4, number literals wait) was tried and stopped (branch
`postponement-stage4-experiment`, `27f66005`): with literals waiting until the end of the
declaration, 11 proofs main accepts failed, 7 in std (`List/Lemmas.sw:977`, `:1149`, `:1154`,
`:1546`, `:1793`; `List/Index.sw:245`; `PrefixSums/BlockSum.sw:40`) and 4 in aoc (2024
`Day08/Proofs/Part1.sw:81`, `Day10/Proofs/Proofs.sw:140`, `Day17/Proofs/Search.sw:46`; 2025
`Day08/Proofs/Part2.sw:287`). In each, only the `Nat` default fixes a literal's type, and a
proof in the same declaration compares against its value first; the comparison can't wait, so it
fails on the unfilled placeholder. Rerun on this base with `27f66005` applied **[run]**: 6 are
`E-TYPE-MISMATCH` or `E-REFL` at a comparison with a placeholder in it (`?2 ?3` and `?4`; `[?7
[]] ∉ [[?14 []]]`; `DecEq.%decide (?22 …) …`), one is `rfl` against an expected type that *is*
a placeholder (`Lemmas.sw:977`, "the expected type is `?3 ?4`"), and one is `rewrite` finding
nothing in a goal that holds one (`Day17/Proofs/Search.sw:46`, `E-REWRITE-NOTHING`). That is
§5.13's trigger, so stage 6 comes first.

### The unifier's callers

`unify::unify` answers `true` or `false` (`unify.rs:26`, `run` at `:41`). Every call outside
the unifier, by kind, with what each does with `false` today **[checked]**:

| kind | sites | `false` means today |
|---|---|---|
| **checking against an expected type** | `check::compare` (`check.rs:4198`): `undo::unify`, then dictionaries found and compared again (`:4210-4243`), `effects::coerce`, `rows::postpone`, `lift::await_helpers`, then the mismatch. Direct shortcuts that give their own message or choose a shape: `check.rs:2146`, `2855`, `3145`, `3259`, `3352`, `3394`, `3619`, `4350`, `4450`, `4913`, `4921`, `4942`, `5054`; `numbers.rs:257`, `:299`, `:973`, `:999`, `:1161`; `dot.rs:543`, `:942`, `:1632`; `records.rs:836`, `:1034`, `:1042`; `calc.rs:74`, `:130`; `patlet.rs:232`, `:287`; `ring.rs:1257`; `omega.rs:3350`; `quot.rs:253`; `defaults.rs:658`; `reify.rs:142`; `lib.rs:4306`; `families.rs:217` | `compare`: the declaration's (or the enclosing attempt's) `E-TYPE-MISMATCH`, after every other way. The shortcuts: another way, or their own error |
| **`rfl`** | `check.rs:3514` (with `lift::await_helpers` at `:3515` and `refl_after_instances`, `:5170`, `:5176`), its message at `:3522`; `lift.rs:266` (a comparison kept for helpers, made again after lifting) | `E-REFL` |
| **`rewrite`** | `rewrite.rs:531`, `:578`, `:1124-1127`, `:1207`, `:1380`, `:1471`, `:1507`; `rewrite/under.rs:337`; `search.rs:265`, `:271` | this occurrence, hypothesis or motive doesn't fit: try the next, or `E-REWRITE-NOTHING` |
| **instance and proof search** | `interfaces.rs:1031`, `:1276`; `auto.rs:172`, `:246`, `:267`, `:412`, `:417`, `:475`, `:479`, `:657`, `:982`, `:984`, `:1009` | this candidate doesn't apply: the next; an obligation whose type is unknown already waits (`Attempt::Wait`) |
| **`cases`, `omega`, decisions** | `omega.rs:2056`, `:3325`; `ring.rs:1179`, `:1243`; `matching.rs:279`; `decreasing.rs:2551`; `calc.rs:256`, `:499`, `:500` | not this atom, branch or shape: the next |
| **try-and-undo** | `undo::unify` and `undo::unify_solving_arguments` (`undo.rs:213`, `:218`), used by `compare`, `rfl`, `check.rs:2289-2290` (expected-type propagation), `:3335`, `records.rs:1042`, `matching.rs:279`, `effects.rs:655`, `lift.rs:266`, `rewrite.rs`; and the 51 `Snapshot::take` sites outside `undo.rs` and 35 `transaction`/`attempt` calls, each of which may wrap any of the above | undone; the attempt takes its next alternative (§5.7, T1) |
| **effects and rows** | `rows.rs:225`, `:295` (`unify_postponing`, which already puts a row comparison aside: `RowConstraint`, the precedent for this stage), `:390`, `:394`; `effects.rs`, 25 sites | rows: kept as a row constraint, retried in the obligations loop; the rest: their own error or route |
| **the queue's own** | `queue.rs` `fill`; `check.rs:2264`, `:2300` (a postponed lambda's placeholder); `lift.rs:233` (`unify_awaiting_helpers`, the other precedent: a helper's frozen unknown taken as equal, compared again after lifting) | the item's mismatch at its span |
| **inside the unifier** | `unify.rs`: the nested comparisons of `unify_step` (a call's arguments, `same_arguments`, stuck case trees, the `+` rule) | the enclosing pair fails, or is put aside (SW-896) |

### What `Blocked` means, per kind

`unify` gains a tri-state form, `unify_waiting`, answering **Yes**, **No** or
**Blocked(pairs)**. A pair is set aside, rather than failing the comparison, only if it fails
where one side is a **pending** unknown applied to anything, or is flexible (another unknown
applied, a stuck call, a sum on one) and mentions a pending one. **Pending** means: a
placeholder no check has filled, or the unknown a waiting item waits on (`queue::pending`). These
are exactly the unknowns the queue *owns*: each is settled by the end of the declaration (by its
item's resumption, a default, or the item is reported stuck), so a comparison that waits on one
always gets an answer by W4. An ordinary unknown is not pending: a pair stuck on one fails, as
today. (Agda waits on any unknown; restricting waits to the queue's own keeps every comparison
that doesn't meet postponed syntax exactly as it is.) Comparisons nested inside a pair answer for
themselves: the outer pair is what waits (`unify::nested`). The rest of the comparison goes on,
and what it solves stays solved: those are pattern solutions forced by other pairs, as today.

| kind | `Blocked` | why |
|---|---|---|
| checking against an expected type: `compare`'s **last** step | **waits**: a queued comparison (`Failure::Mismatch`) | `compare` is where a mismatch becomes the error. Asked only after every other way failed, so a comparison that succeeds today never reaches it |
| the direct shortcuts | No, as today | each is a shape test with another way after it, or `compare` follows |
| `rfl`'s **last** step | **waits** (`Failure::Refl`) | as `compare`; `rfl` against an expected type whose head is pending (`Lemmas.sw:977`) is stage 4's, below |
| `rewrite` | No inside its search; the **rewrite as a whole** may wait as an item when its goal holds an unfilled placeholder (as D2035's `Decide` waits) | a search over occurrences can't commit to a pair that may not hold; but its goal is known once the placeholder is filled. Built in stage 4 only if K4 needs it (`Day17/Proofs/Search.sw:46`) |
| instance and proof search | No | a candidate is chosen now; obligations already wait at their own level |
| `cases`, `omega`, decisions | No | a decision procedure that waited would commit to a branch |
| try-and-undo | No: the boolean `unify` is unchanged | an attempt chooses between alternatives now. A `compare` or `rfl` *inside* an attempt may wait; the waiting comparison belongs to that attempt (invariant 5: undone with it) |
| effects and rows | No, as today | rows have their own postponement |
| the queue's own | No | a fill solves its placeholder |
| inside the unifier | the enclosing pair | nesting (`unify::nested`) |

**The risk this keeps** [inferred]: a `compare` or `rfl` inside an attempt that today fails, so
that the attempt takes another alternative, now waits, and the attempt succeeds. If the waiting
comparison later holds, the program is accepted on that route (a hash may change); if it fails,
it fails at a resume point. Within its own application's W1 that is still inside any attempt
that encloses the application; outside it, the route is committed and the program is rejected
where another alternative would have succeeded. Only comparisons that meet a pending unknown can
take this path, which is measurable: the stage-2 counters found 8 such comparisons in aoc and 2
in the accepted examples ("met unfilled"). Every one is checked below.

### Waking, the ladder, and invariant 7

A blocked comparison becomes a queue item, a `Comparison` (no syntax, no term: its placeholder
stands for nothing), with its pairs, the two types, its caller's failure kind, and its blockers:
the pending unknowns its pairs mention. It is created in the scope it was made in, so the
queue's own rules apply unchanged:
- **woken** at the resume points, when **any** of its blockers is solved (`Check::wakes`), not
  only the first; selected at ladder step 1 with the items, in creation order, scoped as items
  are (invariant 3: at W1 only if made inside that application);
- **resumed** in its saved context by its caller's ways again (`compare`: the comparison, then
  with dictionaries found; `rfl`: the comparison, then `refl_after_instances`), then by
  `unify_waiting`: Yes, it is done; No, it fails with its caller's error against the types now
  known, at its own span (§5.9's rule for resumed items); Blocked, it waits again on what it is
  now stuck on (`Resumed::WaitingAs`, so a restore takes that back);
- **invariant 7**: a comparison has no default. A default is applied only when no item and no
  comparison can resume and the obligations loop is quiet; after a default the ladder goes back
  to step 1, where the items it unblocks fill their placeholders and the comparisons on them
  wake;
- **invariant 5**: it is an item, so snapshots record and restore it.

**Stuck at the end.** A comparison still waiting at W4 waits on a pending unknown; after the
ladder, that is a stuck item's placeholder or blocker. The stuck report groups it with that
item (it depends on it, or shares its blocker), and reports the item, the root, as §5.9 does;
the comparison is a consequence. Its own error, computed when it began waiting (its caller's
error then), is reported only if it were a root, which the definition of pending rules out.

### D2016's end state: placeholders frozen

With comparisons able to wait, a placeholder is frozen until its check fills it: unification
treats it as a rigid unknown equal only to itself (as `Globals::frozen_metas` are), never solves
it, never prunes it, and never solves it by comparing two stuck calls' arguments (the lossy rule
of the caveat to P1). The set lives on `Globals` (`unfilled_placeholders`), kept in step with
the queue, so it can't leak between elaborators on one thread. The fill unfreezes and solves it.
**Decided: freeze now**, from the measurement **[run, with this design prototyped]**:
- unfrozen, aoc waits once (`Day24/Proofs/Adder.sw`, the `allMember` of §"As built (stage 2)"),
  with every std + aoc hash unchanged;
- frozen, aoc waits 17 times and `solved first` falls from 16 to 0 (`lossy` from 11 to 0); every
  std + aoc hash, every accepted and extract example hash at `STITCHWORT_TIER=full` is unchanged;
  every example keeps its outcome and its error message (no snapshot written). The example and
  the four aoc proofs that draft 3's freeze broke (§6.7) pass: their comparisons wait.

### Termination (extending §5.7)

T1 is unchanged: no attempt site is added (`compare_waiting` takes one snapshot, restored if the
answer is No: straight-line, one alternative). T3 holds for comparisons as for items. T4 gains
one fact: **a waiting comparison is resumed only after one of its blockers was solved since it
began waiting**, and resuming it either finishes it, fails, or makes it wait again on pending
unknowns still unsolved. Within a branch solutions are never taken back, and the branch's
unknowns are finite (each is made by elaborating finite syntax, measure 1), so a comparison is
resumed at most once per unknown solved in its branch. A comparison makes no items and no
syntax, and `unify_waiting` steps the budget as `unify` does. So measure 1 (a waiting comparison
counting as an unfinished occurrence) falls when it finishes, and between its resumptions the
count of unsolved unknowns in the branch falls. Across branches, comparisons are items, undone
with their attempt (T1-T2 unchanged).

### What stage 6 doesn't do

- W1 stays as frequent as it is (D2014's S4 allows fewer; nothing asks for it).
- Shortcuts, searches and decisions answer as today. If a case needs one of them to wait, it is
  queued as an item at that site, as `Decide` was (D2035), not by making the search tri-state.
- The note's "met unfilled" counter keeps its meaning (failing pairs headed by an unfilled
  placeholder or a call stuck on one), counted in every comparison, waiting or not; a new counter,
  `waited`, counts comparisons queued.

## As built (stage 6)

Built in SW-817's stage-6+4 lane on `b6f8d2ae`, in four commits: the design pass (`8f24df0f`),
the stage (`37352546`), and two fixes stage 4 found in it (`2907420d`, `18762a20`); this section
is the fifth. Line numbers are of `18762a20`.

**What exists.**
- **Tri-state unification** (`crates/elab/src/unify.rs`). `unify_waiting` (`:70`) answers
  `Answer::Yes`, `No` or `Blocked(pairs)` (`:51`), with the queue's pending unknowns given for
  the call (`PENDING`, `:237`). In `run`, a pair that fails (`:181`), or a pair put aside that
  still fails with nothing solved (`:188`), is set aside by `sets_aside` (`:92`) when one side is
  a pending unknown applied, or flexible (an unknown applied, a stuck call, a sum on one) and
  mentioning one (`on_pending`, `:116`; past `KNOWN_CAP` it looks for each pending unknown as the
  occurs check does, `18762a20`). Only the outer comparison sets pairs aside: `unify` and the
  nested runs of `unify_step` go through `nested` (`:34`), which suspends `WAITING` (`:240`), so
  every existing caller's boolean answer is unchanged by construction.
- **Placeholders frozen** (D2016's end state). `Globals::unfilled_placeholders`
  (`crates/core/src/globals.rs:445`, cleared with the metavariables) holds the placeholders their
  checks haven't filled, kept in step by `Queue::sync_unfilled` (`queue.rs:256`); `unify::frozen`
  (`unify.rs:153`) treats them as `frozen_metas` are, everywhere the unifier asked
  `meta_frozen` (solving, pruning, the row and `+` rules, `blocked`). The fill unfreezes its
  placeholder before solving it (`queue.rs:766`).
- **A waiting comparison** (`queue.rs`). `compare_waiting` (`:426`) is the last step of
  `check::compare` (`check.rs:4224`, after `await_helpers`) and of `rfl` (`check.rs:3517`): with
  anything queued, it asks `unify_waiting` with `pending` (`:374`: the unfilled placeholders and
  each waiting item's blocker); on `Blocked` it queues a `Comparison` (`:477`) through
  `queue_constraint` (`:564`): an item with no term (`Item::constraint`, `:169`; resumed it gives
  `Resumed::Holds`, `:720`), woken when any of its blockers is solved (`Check::wakes`, `:107`,
  `:552`). Resumed (`:507`), its sides are evaluated afresh (`2907420d`), then its caller's own
  ways run again (`check::unifies_with_instances`, `check.rs:4245`, split out of `compare`; or
  `undo::unify` and `refl_after_instances` for `rfl`), then `unify_waiting`: it holds, fails with
  its caller's error against the types now known (`Failure::error`), or waits again
  (`Resumed::WaitingAs`). Counter `waited` (`:926`).

**The caller table and the policy** are §"Stage 6: design" as written; nothing deviated from
it. The `rewrite` row's "the rewrite as a whole may wait" was not needed by stage 6 alone.

**Hash changes: none** **[measured]**. The std + aoc (10,657 declarations) and std + rogue
(5,228) dumps of `37352546`, `2907420d` and `18762a20` are byte-identical to `b6f8d2ae`'s;
`hash_stability` at `STITCHWORT_TIER=full` (accepted and extract examples, projects, prelude)
writes no snapshot.

**Error messages and outcomes: none changed** **[run]**. The examples test at the full tier
(accepted, rejected with every message snapshot, goals, soundness, projects) passes on
`37352546` and on `18762a20` with no snapshot written. `stitchwort check --no-cache` and
`stitchwort test` pass in `aoc/` (135 namespaces, 914 tests) and `games/rogue/` (3 namespaces,
100 tests) on both. `task audit`: 1,363 aoc and 190 rogue theorems, 0 failed, 0 warnings. A
mismatch that now waits and then fails reports what main reports (the driver test below compares
the message).

**Counters**, `STITCHWORT_TIMINGS`, `stitchwort check --no-cache`, base `b6f8d2ae` → lane
**[measured]** (each example checked on its own and summed; the examples on `37352546`, aoc and
rogue on `18762a20`; `requeued`, `read back`, `disagreed`, `kept chose`, `defaulted` and `retried`
are as on the base):

| | queued | resumed | stuck | met unfilled | solved first | lossy | waited |
|---|---|---|---|---|---|---|---|
| aoc | 166 → 166 | 143 → 160 | 0 → 0 | 8 → 218 | 16 → **0** | 11 → **0** | **17** |
| rogue | 35 → 35 | 32 → 32 | 0 → 0 | 0 → 0 | 0 → 0 | 0 → 0 | 0 |
| accepted examples | 2,944 → 2,944 | 2,927 → 2,931 | 0 → 0 | 2 → 42 | 4 → **0** | 3 → **0** | **4** |
| rejected examples | 4,233 → 4,233 | 4,209 → 4,209 | 9 → 9 | 0 → 0 | 0 → 0 | 0 → 0 | 0 |

- **The 8 comparisons that "met unfilled" at `Day24/Proofs/Adder.sw:193`** belong to one
  comparison, the `allMember (wire => wire.zBit.all (found => found ≤ bits))` argument checked
  against its parameter; it now **waits** (one of the 17, at `Adder.sw:193`, found with a scratch
  trace, not kept) and holds once the `.zBit` placeholders are filled.
- **The 16 fills unification solved first** (10 in stage 2, +6 sections in stage 3) now wait
  instead: the other 16 of aoc's 17 waits are those comparisons (by the same trace: 2024 day
  7's `couldBeTrue` statement, day 9's three `moveFile` proofs of §5.10, day 16's two
  reindeer-path proofs, and ten more in day 24's proofs, two of them in `Adder.sw`) [the files
  other than `Adder.sw` identified by their content, inferred]. `solved first` and `lossy` are 0:
  no placeholder is solved by unification, guessed or otherwise (the caveat to D2016's P1 is
  gone).
- `met unfilled` rises because frozen placeholders now fail the boolean comparisons that used to
  solve them (in attempts, shortcuts and searches, where `Blocked` is `No` by design); none of
  those changes an outcome or a hash (above).

**Timing**, `stitchwort check --no-cache` in `aoc/`, user + system CPU, alternating `b6f8d2ae`'s
binary with `18762a20`'s, on a shared machine **[measured]**: base 37.41, 34.77, 34.43 s; lane
35.34, 34.50, 34.43 s (load average 26 falling to 4). No cost shows.

**Tests.**
- `unify.rs`, 3 new: a pair on a pending unknown waits and the rest is solved (the placeholder
  never is); only pending unknowns make a comparison wait (a rigid mismatch and a frozen unknown
  the queue doesn't own are `No`); a nested comparison answers for itself.
- `queue.rs`, 6 new: a comparison on a placeholder waits and holds once it is filled, after its
  item; a waiting comparison that fails reports its caller's error (`E-REFL`) at its own span; a
  comparison that can never hold doesn't wait and keeps nothing it solved; restoring takes back a
  waiting comparison and its resumption (invariant 5); a stuck comparison is reported through the
  item it waits on (§5.9); a side stuck on the placeholder computes again when resumed. Three
  stage-1 tests of D2016's unfrozen placeholders are rewritten for frozen ones (the fill's guard
  is kept and tested with a placeholder solved directly; the lossy guess can no longer happen).
  Release and debug.
- `crates/driver/tests/postponement.rs`, 2 new: `anyPerm` with the lambda's parameter fixed later
  is the annotated term (the shape where unification used to solve the placeholder); the same
  with a wrong number is `E-TYPE-MISMATCH` with main's message, no unknown in it.
- Lane tier `elab`, `core`, `std`, `examples`, `hashes`, `lsp` on `37352546`: pass. The examples,
  `hash_stability`, `postponement` and the elab unit tests at the full tier on `18762a20`: pass
  (151). Clippy `--deny warnings` and `cargo fmt --check`: clean.

**Merge-readiness of stage 6 alone: ready** by the gate set for it: every hash classified (none
changed), no error message changed, aoc 914 and rogue 100 pass, audit clean. Two caveats for the
merge: the lane tier was run on `37352546`, before the two small fixes (`2907420d`, `18762a20`),
whose effect was re-measured with the dumps, the full-tier examples and AoC/rogue but not the
lane tier itself; and the merge tier was not run (lane rules).

**Deviations from the design pass.**
1. **On resume a comparison is made again whole**, not pair by pair: its caller's ways (finding
   dictionaries) are what make some hold (`examples/accept/finite-check.sw`'s `rfl`, which waits
   on `u.bits` and then needs `Finite.all`'s dictionary).
2. **`effects::coerce` is not retried on resume**: it changes the term, and a waiting comparison
   has none. No case needs it.
3. **The pending set is computed per call** (`queue::pending`), not kept in step with the queue:
   it is asked only where a comparison has already failed every other way.

## Stage 4, second attempt: stopped

Built on stage 6 in this lane as `ac4587c9` (**EXPERIMENT, not for merge**), from `27f66005`'s
K4 (number literals and undecided groups wait, `Nat` default after the field-name rule) plus what
stage 6 and the first failures asked for. Stopped, as the brief asks, because outcomes of reject
examples change and the design shows a consumer missing from §5.10.

**What stage 6 fixed** **[run]**: with comparisons waiting, `27f66005` applied on stage 6 checks
`k4-proof.sw` and the std failures of the first attempt at `:977` aside; the runs then found, one
after another, `List/Lemmas.sw:625` (a rewrite rule's literal, new), `:1793` (stage 6 resumed a
comparison on stale stuck values: `2907420d`), 2025 `Day08/Proofs/Part2.sw:286` (a side too large
to read back: `18762a20`), `PrefixSums/BlockSum.sw:40` (a rewrite's goal holding a waiting
literal), and the rest below.

**What was added on top, each found by a failure** **[run]**:
1. `rfl` against an expected type whose shape is pending (`?3 ?4`, `?3 ?5 < ?5`) is `?x = ?x`
   compared with it, which waits (`List/Lemmas.sw:977`).
2. A rewrite rule's own items are settled before its search, defaults included, scoped to the
   rule, as Lean elaborates a `rw` rule with postponement off (`queue::settle_rule`;
   `List.sumByOne`'s `(x => 1)`). **This applies a default before W4** (invariant 7, scoped).
3. `rewrite` and `cases` that fail on a goal holding a pending unknown wait whole
   (`queue::tactic_or_wait`; `PrefixSums/BlockSum.sw:40`, `cases-solved-unknown.sw`).
4. W2 applies defaults (helpers are lifted at the end of a part; `match-eq-auto.sw`'s
   `| Less => 0 | _ => 1`).
5. A pending placeholder applied twice (`?p a` against `?p b`) waits rather than comparing its
   arguments (`quot-lift-types.sw`'s `a => 7`).
6. **Groups built at an unknown type**: a group with only `+`, `*`, `<`, `<=` and equations that
   nothing decides is built at once at a fresh type, its literals waiting and its dictionaries
   obligations, so its shape is known (`0 = 0` is `Eq ?T ?a ?b`, as Lean's `@Eq ?α 0 0`);
   `27f66005` made the whole group a placeholder, which hid `Eq` and `<` from `J`, `rfl`,
   decisions and tests: 12 accepted examples failed (`and-or-not`, `greater-than`, `big-numbers`,
   `kernel-2026-neighbours`, `effect-logic-in-lambdas`, the three `quot-*`, `match-eq-auto`,
   `cases-solved-unknown`, `postpone-let-lambda-field`, `match-in-lambda-restated`).

**Where it stands at `ac4587c9`** **[run]**:
- `k4-proof.sw` checks; `record-literal-inferred.sw`'s "in a list" passes unannotated; every
  accepted example and project checks; rogue checks and passes 100 tests.
- **10 of the 11 proofs check**; aoc 2024 `Day17/Proofs/Search.sw:46` (`rewrite outputs in
  DecEq.refl target` inside `Bool.andIntro _ _ positive …`, the filter's `0 < a ∧ …`) checked
  before change 6 and fails again after it, `E-REWRITE-NOTHING`.
- **3 reject examples change outcome**: `int-binding-nat.sw` (`let m := 3 - 5; m + i == 0` with
  `i: Int`) and `match-bad-motive.sw` are **accepted**; `calc-step-callback.sw` is
  `E-TYPE-MISMATCH` instead of `E-CALC-STEP` (its step's `(rfl: 0 = 0)` now waits, and fails at a
  resume point, outside `calc`'s own error mapping).
- **4 reject messages change**, same code: `expected-type-retry.sw` and
  `operators-generic-literal.sw` now blame the literal against the type the rest fixes ("expected
  `Bool`, but this has type `Nat`", note "a numeral can only be the prelude's `Nat` or `Int`")
  rather than the other part against `Nat` (arguably better); `let-refutable.sw` says `Option ?0`
  for `Option Nat` and `soundness/quot-of-proposition.sw` says `?1 = ?2` for `0 = 0` (worse: an
  unknown shown).
- Std + rogue: 12 std declarations change hash (not classified at this commit). At an earlier
  point (before change 6) std + aoc changed 17 (13 aoc, 4 std), 6 in their own terms, every one a
  call kept folded where the base's term had its unfolding (a `J` motive, an implicit argument);
  all statements identical **[measured, scratch term dump]**.

**Why stop** (the brief's conditions):
- **Reject outcomes change.** `int-binding-nat.sw` is the D2013/N1 change itself: a literal made
  `Nat` too early on main is now the `Int` the declaration fixes, so syntax.md's "A `let` binding
  keeps its own type" no longer holds. That is a language change to list for Matt, not a bug.
  `match-bad-motive.sw` is not: see the next point.
- **A consumer missing from §5.10: a `match`'s generalisation of its scrutinee.**
  `match List.length [1, 1] with …` abstracts the occurrences of its scrutinee in the context; with
  the body's `[1, 1]` waiting, the scrutinee is `List.length [?1, ?2]`, the signature's
  `List.length [1, 1]` doesn't match it, `q` isn't generalised, and the program the example
  rejects with `E-MATCH-MOTIVE` is accepted. The kernel accepts the term (no unsoundness), but
  it is an elaboration choice made from a placeholder's shape, invariant 8's class "a different
  well-typed meaning", not "a type error". The fix in kind is change 2's: settle the scrutinee's
  own items before generalising. With changes 2 and 4 that makes three places where a default
  runs before W4, which is a revision of invariant 7 for Matt, not a patch.
- **Error reporting.** A comparison that waits and then fails reports outside the construct that
  maps its error (`calc`), and two messages now print unknowns. Both need a rule (an item's error
  wrapped by its caller; a waiting literal printed as itself) rather than case-by-case fixes.
- **Not converging.** Change 6, needed by 12 accepted examples, undid Day17's fix; each of the six
  changes was a new consumer of a type's shape that a waiting literal hides.

**What a stage 4 that can be merged needs, as I see it** [inferred]:
- K4 with groups built at an unknown type (change 6) as the base design: only literals and
  `-`/`/`/`%` groups wait, never a proposition's shape.
- A decision for Matt on **where defaults may run before W4**: at the end of a closed
  sub-elaboration whose result is searched or matched against (a rewrite rule, a `match`
  scrutinee, a `calc` step?), as Lean runs `synthesizeSyntheticMVarsNoPostponing` for tactic
  arguments; and at W2. Invariant 7 would then say "at quiescence of the declaration, or of a
  closed sub-elaboration that a search consumes".
- §5.10's table extended with: `match` scrutinee generalisation, rewrite rules and goals,
  `cases` goals, `rfl`'s expected shape, decisions of tests and `if` conditions.
- A rule for errors of waiting checks: the message rendered after defaults, or with a waiting
  literal printed as written.
- D2013's N1 restated: accepted programs keep their literals' types (measured so far: yes, every
  changed term is a folded/unfolded difference), and some rejected ones are now accepted (list:
  `int-binding-nat.sw`, syntax.md's "Known limit" `let v = chooseFirst 5 i`).

## Stage 4: design for the third attempt

Written in the D2086 design lane (SW-817), 31 October 2026, on main `7d9544dc`, from the stopped
experiment `ac4587c9` and two commits on top of it, `71d5f1fd` and `9ca412a0` (branch
`d2086-prototype`, **PROTOTYPE, not for merge**: everything behind switches, off by default).
Labels in this section: **[run]** run on 31 October; **[read]** read in source (Stitchwort at
`ac4587c9` unless a line says main; Lean 4 at `0f852cc8`, the commit of [L1]-[L7]); **[inferred]**
my reasoning, not tested. Repros, the Lean files and their output are in
[postponement/d2086/](postponement/d2086/).

### In short

**The issue.** Stage 4 makes a number literal wait for its type instead of becoming `Nat` at
once. While it waits, it is a placeholder: an unknown that stands for `3` but doesn't look like
`3`. Some parts of the compiler look at the *shape* of a term, not only at its type: a `match`
looks for its scrutinee in the types around it, a `rewrite` looks for its rule in the goal, an
error message prints the terms it is about. Meeting a waiting literal, they see an unknown. Then
they either decide something wrong (a `match` accepts a program that its annotated twin rejects)
or print `?1 = ?2`. The second attempt patched these one at a time and didn't converge.

**The options**, for each part that reads shapes:
- (a) it **waits** until the unknown is settled, as a queued check;
- (b) the literal is **settled first**: given its default (`Nat`) early, but only inside the bit
  of code being looked at;
- (c) it learns to **see through** a waiting literal, as Lean does: there a numeral is an
  ordinary term whose type is unknown, so a search can match `1` against `(1: Int)`.

**The recommendation.**
- A `match` **waits** until what it reads holds no unsolved unknown. This also fixes a bug that
  main has today, without stage 4 (two repros below).
- A `rewrite` rule is **settled first**, defaults included, but only its own literals: the rule
  is read like a small statement of its own, which is what main does with it today. This is the
  only place a default runs early, and invariant 7 is restated to say so (D2087).
- A proof search (`rewrite`, `cases`) that fails on a goal holding an unknown the declaration
  will still settle **waits** and tries again, as in the experiment. "Will still settle" must
  include the dictionaries that obligations will find, which the experiment left out.
- **Errors.** A construct that turns the errors inside it into its own (a `calc` step's
  `E-CALC-STEP`) still does so when the failure comes later, at a resume point: the waiting check
  carries an *error frame* from that construct. A waiting check's placeholder prints as the
  source it stands for (`0`, `r.items`). An unknown that is a waiting literal's *type* is never
  printed: what would print it waits too.
- **Attempt 3** lands these rules on main first, before number literals wait, then K4 on top.

**What the prototype shows** [run]: with all its switches on, against stage 6's base
(`18762a20`), the examples change only where they should: `record-literal-inferred.sw` is
fixed and `int-binding-nat.sw` is accepted (D2084). Every other reject example keeps its code and
its message, except two messages that blame the literal instead of the other side (better, and
a decision). The experiment's two wrong reject outcomes (`match-bad-motive`,
`calc-step-callback`) and its two messages with unknowns are gone. aoc fails only where the
experiment did (2024 Day17; my reading of why, speculative, is below).

### What the prototype is, and what it shows

**Switches** (`71d5f1fd`, `9ca412a0`; all off by default) [read]:
- `D2086_MATCH_WAIT=1`: a generalising `match` whose scrutinee as elaborated, goal, or a
  variable's type mentions an unknown the queue still has to settle waits for it, whole, its
  scrutinees kept as elaborated (`WaitingMatch`, `matching.rs`). `D2086_MATCH_WAIT_ANY=1` adds
  any unsolved unknown in the scrutinee, not only the queue's.
- `D2086_FRAMES=1`: items and waiting comparisons carry the error frames they were made in; a
  `calc` step is one (`StepFrame`, `calc.rs`).
- `D2086_DISPLAY=1`: a waiting number's placeholder prints as the number (a print label).
- `D2086_NO_RULE_DEFAULT=1`: a rewrite rule's own items are resumed but not defaulted before the
  search (the experiment's addition 2 taken back, to test it).

**Runs** [run]. Binaries: base `18762a20` (stage 6), the experiment `ac4587c9`, the prototype
`9ca412a0`. Outcomes are the first error line or `checked` of every file under
`examples/{accept,reject,soundness}` (1,140); messages are the whole output of every reject and
soundness example (804).

| | base | experiment | prototype, all switches |
|---|---|---|---|
| outcomes changed from base | | 5: `record-literal-inferred` passes; `int-binding-nat`, `match-bad-motive` accepted; `calc-step-callback` `E-TYPE-MISMATCH` | 2: `record-literal-inferred` passes; `int-binding-nat` accepted |
| messages changed from base | | 7 | 3: `int-binding-nat`, `expected-type-retry`, `operators-generic-literal` |
| messages that print an unknown (`?N`) | 15 | 17: also `let-refutable` (`Option ?0`), `quot-of-proposition` (`?1 = ?2`) | 15, the same files as base |
| aoc (`check --no-cache`) | checks | `E-REWRITE-NOTHING` at 2024 `Day17/Proofs/Search.sw:46` | the same, only that; 6 matches waited (0 with the queue's unknowns only) |
| rogue | checks | checks | checks; 0 matches waited |

One switch at a time [run]:
- `match-bad-motive.sw`: `MATCH_WAIT` gives base's `E-MATCH-MOTIVE`, message identical.
- `calc-step-callback.sw`: `FRAMES` alone gives `E-CALC-STEP`, but "this proves `?16 n = ?17 n`";
  with `DISPLAY` too, base's message exactly.
- `let-refutable.sw`: `MATCH_WAIT` gives "doesn't match every `Option Nat`" (the refutable `let`
  is a one-alternative `match`, which now waits, so its message is built after the default).
- `quot-of-proposition.sw`: `DISPLAY` gives "`0 = 0` is a proposition".
- `NO_RULE_DEFAULT`: std doesn't load: `List/Lemmas.sw:625`, `E-REWRITE-NOTHING`, "looking for
  `List.sumBy (Cons x rest) (x => ?3)`".

Not measured: hashes, and `stitchwort test` in aoc and rogue (the prototype only checks).

### Question 1: parts that read a term's shape

#### What really happened in `match-bad-motive.sw`

Not what the stop report guessed. The occurrence test is `matching::same` on normal forms
[read]. `List.length [?1, ?2]` computes to `2` (length doesn't look at the elements), so the
occurrence in `q`'s type *is* found [run, scratch print]. What fails is the check after it:
`check_motive` (`matching.rs:736`, on main too) builds the helper's type, and when an unknown in
it isn't solved yet it returns `Ok` (`:766`, "something isn't known yet: checked when it's
admitted") [read]. Here building it fails with "can't work out an implicit argument" [run,
scratch print]. Admission checks the helper with only the variables its body uses, so `q`'s
copy, which the body doesn't use, is never checked: the helper admitted is `bad.%match1: Nat →
Nat` [run, scratch print in `declare_helper`, `lift.rs:791`].

**Main has the same hole today, without stage 4** [run, main's binary and base]:
- `motive-field-later.sw`: the scrutinee holds `r.x` waiting for `r`'s type (stage 2's K2).
  Accepted. Its twin with `(r: P)` is `E-MATCH-MOTIVE`.
- `motive-param-later.sw`: the scrutinee holds a lambda parameter whose type is an ordinary
  unknown (no queue item). Accepted. Its annotated twin is `E-MATCH-MOTIVE`.

**And the occurrence test can decide from a placeholder too** [run]: `motive-literal-later.sw`,
`match 1 + 1 with …` with `q: two 2 rfl b = 2` in scope. Main and base: `E-MATCH-MOTIVE`. The
experiment accepts it: `1 + 1` is a group built at an unknown type, `?a + ?b`, which computes to
nothing and is found nowhere, so nothing is generalised. Making `check_motive` stop skipping
would not catch this one: nothing was copied, so there is nothing to check [inferred]. So the
`match` must not *decide* anything while what it reads holds an unsolved unknown.

#### Lean 4, for comparison

Run with Lean 4.34.1 [run, `lean-m1.lean` to `lean-m5.lean`, output in `lean-runs.txt`] and read
at `0f852cc8` [read]:
- **Lean's term `match` generalises less.** Only variable scrutinees have their dependents
  generalised (the remark before `generalize`, `Match.lean:870-880`), so
  `match-bad-motive.sw` written in Lean is accepted (m1's `bad`).
- **It finds occurrences by unification.** The expected type's occurrences of a scrutinee are
  abstracted by `kabstract` (`Match.lean:137`), which compares with `isDefEq`
  (`Meta/KAbstract.lean:30-60`). A pending numeral takes its type from the occurrence: m1's `t2`
  prints its scrutinee's list as `List Int`.
- **`rw` too.** A rule whose numeral's type is pending, `myLen 3 1`, rewrites
  `(List.replicate 3 (1 : Int)).length` (m2's and m5's first example); the same rule written at
  `Nat` doesn't (m2's second, "did not find"). `rw` applies defaults only after the rewrite: the
  rule and the search both run inside `withSynthesize` (`Tactic/Rewrite.lean:54`, `:65`).
- **Lean also defaults early, and unscoped.** A term `match` runs
  `synthesizeSyntheticMVarsUsingDefault` after its alternatives (`Match.lean:1150`), which
  defaults *every* pending numeral, also ones made before the `match`. m4: `let m := 3 - 5; m + i
  == 0` makes `m` an `Int` (`f 2` is `true`, D2084's check), but the same with an unrelated
  `match` in between makes `m` a `Nat` (`g 2` is `false`). `calc` defaults after each step
  (`Calc.lean:123`, `:128`); `induction` and `cases` targets are elaborated with postponing off
  (`Tactic/Induction.lean:807`).
- **Messages.** Numerals print as written (`0 = 0`, m2, m3), because they are terms; their
  pending *types* print as `?m.2` (`Option ?m.2`, m3).

So Lean avoids most of this by making a numeral a term of an unknown type,
`@OfNat.ofNat ?α 1 ?inst`, which unification can match, and pays with early defaults that reach
outside the construct. Stitchwort can't build a literal before its type is known: a `Nat` literal
and an `Int` literal are different terms (`check_literal`, `numbers.rs`) [read]. So its
placeholder is opaque, and waiting is the price; in exchange, defaults stay late and scoped.

#### Every part that reads a term's shape, and its rule

"Pending" below means an unknown the declaration's ladder will still settle: a placeholder no
check has filled, the unknown a waiting item waits on, **and an unknown in a waiting obligation**
(the last is new; see addition 3). "Unsolved" also counts ordinary unknowns.

| part | where [read] | what it reads | from a placeholder it would | rule | evidence |
|---|---|---|---|---|---|
| a `match` that generalises: `match e`, `match h: e`, a refutable `let` or lambda pattern (a one-alternative `match`), `cases`' split (`cases.rs:1413`, `generalised_named`), `match reify` (`reify.rs:62`) | `matching.rs`: `generalised`, the occurrence test `same`, `check_motive` | the scrutinee's normal form, the goal, the types in scope | generalise the wrong hypotheses, or skip the motive check: **a different outcome** | **waits**, whole, while any of them holds an **unsolved** unknown; the scrutinee is kept as elaborated | the three repros and `match-bad-motive.sw` are rejected as their twins; `let-refutable`'s message; aoc 6 waits, no new failure [run] |
| a `rewrite` rule, the pattern searched for | `rewrite.rs`, `elaborate_rule` | the rule's two sides | find nothing (`x => ?3`) | **settled first**: the rule's own items resumed, obligations, then defaults, scoped to the rule (D2087) | without the default std doesn't load (`Lemmas.sw:625`) [run] |
| the `rewrite` search over a goal; `cases` looking for atoms and closers | `rewrite.rs`, `replace_occurrences`; `cases.rs` | the goal and hypotheses | find nothing, or split nothing | **try; if it fails while the goal holds a pending unknown, wait whole** and try again when it is settled (the experiment's `tactic_or_wait`) | `PrefixSums/BlockSum.sw:40`, `cases-solved-unknown.sw` in the experiment [run there]; Day17 [inferred, below] |
| `rfl` against an expected type whose head is pending | `check.rs`, `check_value` | the head `Eq` | `E-TYPE-MISMATCH` | `rfl` is `?x = ?x` compared with it, which waits (stage 6) | `List/Lemmas.sw:977` in the experiment [run there] |
| a `calc` step joined to its line, a comparison | `calc.rs` | the step's relation | a mismatch | waits (stage 6); its error goes through the step's frame (Q2) | `calc-step-callback.sw` [run] |
| a decision (`if`, a proposition where a `Bool` is expected) | `bind::decide`, `decide_to_bool` | the proposition | `E-AUTO-NONE` | waits (D2035, built) | stage 3 |
| `omega`, `ring`, congruence closure, `auto`: atoms compared by `same` | `omega.rs`, `ring.rs`, `congruence.rs`, `auto.rs` | the goal's atoms | no proof found | as `rewrite`: try, then wait if the goal holds a pending unknown | no failure in the experiment names them [run]; counted in step 4.2 before it is decided |
| a written motive (`J`, `infer_j`) | `check.rs:5104` | nothing: the motive is written | | no change; its comparisons wait (stage 6) | |
| head-only checks: a quotient's carrier is a type (`quot.rs`), a termination measure is a `Nat` | | the type's head | a type error | allowed, as §5.10's third class; `Eq ?T ?a ?b` is a proposition whatever `?T` is | `quot-of-proposition.sw` keeps `E-UNIVERSE` [run] |

So the parts fall into §5.10's classes plus one: a choice that changes the outcome **waits**
(`match`); a search **tries, then waits** (a different successful search proves the same
statement, so only failure needs care); a comparison **waits** (stage 6); and a pattern made only
to be searched for is **settled first**.

**Why a `match` waits on any unsolved unknown, not only the queue's.** `motive-param-later.sw` is
the same mistake with an ordinary unknown. Waiting costs nothing when the unknown is solved
later, and an ordinary unknown still unsolved at the end is an error anyway. Measured: 6 waits in
aoc, none in rogue, no new failure; no example's outcome changes [run]. Hashes not compared.

**Why the scrutinee is kept as elaborated** (invariant 6): it was inferred with no expected type,
like a `.field`'s receiver kept as a term (§5.5), so nothing learnt later would have changed it.
What it holds that waits is its own items, which resume on their own.

**Why not settle the scrutinee first, as a rule is.** It isn't closed: its value and type flow
into the alternatives and the generalised types, and the `match` has to wait anyway for unknowns
no default settles (a `.field`, an ordinary unknown). One rule, waiting, covers every case. A
literal only the alternatives could type (`match 3 - 5 with | n => n + i`, `i: Int`) ends as `Nat`
either way, as on main; Lean would make it `Int` [inferred].

**Option (c), seeing through, later.** A unifier rule "a waiting literal `k` meets the numeral `k`
at a known type and takes that type" would let a `rewrite` rule find `(1: Int)` as Lean does. It
is more permissive than main, and attempt 3 doesn't need it.

#### Invariant 7, restated (D2087)

> **7. Defaults at quiescence only.** A default is applied only when resuming, obligations and row
> comparisons have all stopped making progress, at one of three points: the end of the
> declaration (W4); a part about to be lifted (W2); and a **closed pattern**, a term elaborated
> only to be searched for (a `rewrite` rule), whose own items, and only those, are settled,
> defaults included, before the search. Nothing else applies a default early: a `match`, a `calc`
> step, `cases` and the proof searches wait instead.

- **W2 isn't a bend** [inferred]. A part's helpers are lifted at its end: everything in the part
  has been elaborated, and nothing outside it can mention the unknowns inside its `match`es'
  alternatives. It is the part's own quiescence (the experiment's addition 4).
- **Why a `rewrite` rule may settle early**: the search can't wait for its own pattern; the rule
  is elaborated with no expected type, so its literals' types are new unknowns nothing outside
  it mentions before the search reads them [read: `elaborate_rule` calls `infer`]; and it gives
  what main gives today, where the literal is `Nat` at once, so no program main accepts changes
  [inferred]. It is how Lean elaborates `induction` and `cases` targets
  (`Tactic/Induction.lean:807`), not how it elaborates `rw` rules (above).
- **What "closed" is checked by.** A debug assertion at the settle: no unknown the rule's items
  waited on occurs in the goal, the context or another item's saved state [inferred design].

### Question 2: errors from waiting checks

**Three problems** [run, experiment]: a failure reported outside the construct that maps it
(`calc-step-callback.sw` is `E-TYPE-MISMATCH`, not `E-CALC-STEP`); a waiting literal printed as
an unknown (`?1 = ?2`); a waiting literal's type printed as an unknown (`Option ?0`).

**The mechanism, three rules.**
1. **Error frames: the construct that made a check reports its error.** A construct that turns
   the errors of a check inside it into its own (a code, a label, a note) runs that check inside a
   frame. Every item and waiting comparison made inside records the frames active then (part of
   the item, so a restore takes it back, invariant 5). If it fails after the construct returned,
   at a resume point, its error goes through those frames, innermost first, exactly as it would
   have inline; a frame still active is skipped, since the inline path applies it. Each construct
   has one mapping function, used both ways: today's `match check(…) { Err(e) if … }` becomes the
   frame. The frame decides the location, as inline (`calc`: the step's proof). Prototype: `calc`'s
   step as a frame; `calc-step-callback.sw` gets back base's message, code and span [run]. Lean
   has no step-specific error here (m2: plain "Type mismatch"); Idris reports a delayed elaborator's
   error at its own location (§3).
2. **A placeholder prints as the syntax it stands for**: `0` for a waiting number, `r.items` for a
   waiting `.field`, the literal for a record literal, the proposition for a `Decide`. Prototype
   for numbers: `quot-of-proposition.sw` prints `0 = 0` again [run]. This also fixes the stage-2
   finding where `E-AUTO-NONE` named `?5 b b` [inferred].
3. **An unknown that is a waiting check's type is never printed as the answer.** It isn't known
   yet, so no printing rule can be honest about it. Whatever would print it reads that type, so it
   falls under question 1's rules and waits: the refutable `let` is a `match`, waits, and is
   reported after the default, `Option Nat` [run]. A message may show `?N` only for an unknown
   that is genuinely unsolved at the end. **Tested**: the examples test fails if a reject or
   soundness message prints `?N` and the file isn't on a list (today's 15 files).

**Constructs with their own error mapping of a check that can now wait** [read, `ac4587c9`]; each
becomes a frame in step 4.1:

| construct | where | what it does to the inner error |
|---|---|---|
| a `calc` step | `calc.rs:250` (`check_step`) | `E-TYPE-MISMATCH`/`E-REFL` at the proof becomes `E-CALC-STEP`, the line in a note |
| an argument of a callback parameter | `check.rs:2436` (`check_arg`) | partial and total callback notes, the local signature |
| a call's last comparison | `check.rs:4003` (`fallback`) | the awaiting and negative-argument notes |
| a proposition decided as a `Bool` | `check.rs:4190` (`decided`); `logic.rs:145` | `E-AUTO-NONE` relabelled with its own note |
| a value against a `Comp` type | `check.rs:3297` (`check_inner`) | the SW-851 note |
| a number group's leaf | `numbers.rs:1444` (`check_leaf`), `:1463` (`prop_not_equal`), `:837` (`function_operand_note`) | "decided by" labels; a proposition compared with `=` |
| named and default arguments | `named.rs:614` (`apply_slots`); `defaults.rs:591`, `:897` | the rigid-parameter and left-out-default notes |
| a record update | `records.rs:1275` (`update_fields`) | the pinned-field note |
| an automatically bound name | `autobind.rs:67` (`explain`) | the "bound automatically" note |
| a `match`'s alternatives | `matching.rs`, `in_context` | the alternative's context |
| a termination measure | `decreasing.rs:1125` | the measure note |

Only the first was in the prototype. The rest are found by the same search (`grep` for `e.code
==` and `map_err`) and each gets a test only where a check inside it can wait.

**The two re-blamed messages** [run]: `expected-type-retry.sw` (`chooseFirst 5 True` against
`Int`) and `operators-generic-literal.sw` (`xs.foldLeft 0 …` in generic code) now point at the
literal, "expected `Bool`, but this has type `Nat`" with the note "a numeral can only be the
prelude's `Nat` or `Int`", where base points at the other part with "this literal made it a
`Nat`". With K4 no literal makes anything `Nat` early, so base's explanation is no longer true.
The examples' comments change with them (D2091).

### Question 3: the six additions, and the plan

**The six additions of the second attempt** [read `ac4587c9`; evidence as cited]:

| addition | verdict | why | the test that would have caught its problem |
|---|---|---|---|
| 1. `rfl` against a pending head is `?x = ?x`, compared | **right** | `rfl` reads its expected type's head, like a record literal; the comparison waits (stage 6) | `List/Lemmas.sw:977`'s shape as an accept example |
| 2. a rewrite rule settled before its search, defaults included | **right, once stated** | the closed-pattern default of invariant 7 (D2087); without it std fails [run] | `Lemmas.sw:625`'s shape (`(x => 1)` in a rule) as an accept example |
| 3. `rewrite` and `cases` wait whole when they fail on a pending goal | **right in kind, boundary too narrow** | for a proof search, only failure needs care. But "pending" there is the queue's placeholders and blockers only (`queue::pending`) [read], not unknowns in waiting obligations | a cut-down Day17 (below) |
| 4. W2 applies defaults | **right** | a part's quiescence (invariant 7 restated) | `match-eq-auto.sw` (in the examples) |
| 5. a pending placeholder applied twice waits | **right** | comparing a frozen placeholder's arguments is a choice from its shape: its term may ignore one (invariant 8, in the unifier) | `quot-lift-types.sw` (in the examples) |
| 6. a group nothing decides is built at an unknown type | **right, as the base design** | its shape (`Eq`, `<`) is known at once, as Lean's `@Eq ?α 0 0`; only its literals wait. It moved the group's dictionaries into obligations, out of addition 3's "pending" | the 12 accepted examples (already caught it) |

**Day17** (`Search.sw:46`, `rewrite outputs in DecEq.refl target` inside `Bool.andIntro _ _
positive …`, with the filter's `0 < a ∧ …` in the goal). It checked before addition 6 and fails
after it. My reading, **speculative** [inferred]: addition 6 turned the group `0 < a` from one
waiting placeholder (pending) into a term whose `<` dictionary is an obligation (not pending), so
the `rewrite` fails on a goal stuck on that dictionary and doesn't wait. Step 4.2 tests this
first, with a trace of what the goal is stuck on.

**What the second attempt lacked**, as a process: a rule for each shape-reading part before
literals waited, so each failure was met one at a time; a check that no message prints an
unknown; reject examples with annotated twins.

**Attempt 3, in steps.** Each step stops if an example's outcome or message changes beyond its
list, or a hash changes beyond its classified list.

- **4.0, on main, no K4: the `match` rule.** A generalising `match` whose scrutinee as elaborated,
  goal or types in scope hold an unsolved unknown waits whole (a `WaitingMatch` item, the
  scrutinee kept). `check_motive` no longer skips: after waiting nothing is unknown, and a debug
  assertion says so. *Tests*: `motive-field-later.sw`, `motive-param-later.sw` as reject examples
  (`E-MATCH-MOTIVE`), their twins as reject examples too; `match-bad-motive.sw` unchanged.
  *Changes*: a bug fix on main (programs main accepts wrongly become `E-MATCH-MOTIVE`); aoc's 6
  waits may change hashes, each classified.
- **4.1, on main, no K4: errors.** Error frames for the constructs above; every kind of
  placeholder printed as its syntax; the examples test's list of messages allowed to print `?N`.
  *Tests*: a unit test that an item failing after a framed construct returned gets the frame's
  code and span; a `calc` step whose `rfl` waits on a `.field` keeps `E-CALC-STEP`; the stage-2
  `E-AUTO-NONE` case prints `r.items`. *Changes*: none expected in the examples.
- **4.2, on main, no K4: searches and the pending set.** "Pending" includes unknowns in waiting
  obligations; `rewrite` and `cases` try, then wait (addition 3); a counter of `omega`, `ring`,
  congruence and `auto` failures on a goal holding a pending unknown, to decide whether they join.
  *Tests*: a `rewrite` and a `cases` whose goal holds a waiting `.field` (accept examples); the
  Day17 shape once cut down.
- **4.3: K4.** Literals wait; groups built at an unknown type (6); `rfl` (1); a placeholder applied
  twice (5); W2 defaults (4); the rule settled (2). *Changes, from the prototype* [run]:
  `record-literal-inferred.sw` unannotated; `int-binding-nat.sw` to accept, with syntax.md's "a
  `let` keeps its own type" changed (D2084); the two re-blamed messages (D2091); nothing else in
  the examples. *Gates*: the 11 proofs of the first attempt and `k4-proof.sw`; Day17; the hash
  dumps classified; aoc 914 and rogue 100 tests; `task audit`.
- **4.4: stage 5**, as planned (§8).

### Decisions for Matt

D2088 and D2089 are taken (SW-915), so these are D2087, D2090 and D2091.

**D2087. Restate invariant 7 so that defaults run at the end of the declaration, at the end of a
part before lifting, and in a `rewrite` rule before its search, and nowhere else?** **[Recommend
yes.]** The text is above. The alternative for the rule is to keep invariant 7 as it is and have
the whole `rewrite` wait until W2 or W4; that gives the same answers here (nothing outside the rule
can type its literal before the search) but holds a proof back as a placeholder for longer. The
other alternative is Lean's, option (c), later. The assumptions, in full:
- **(C1)** A `rewrite` rule is elaborated with no expected type, so the unknowns its literals wait
  on are made inside it and nothing outside it mentions them before its search reads them.
- **(C2)** Settling them early gives what main gives today, where a literal is `Nat` at once, so no
  program main accepts is rejected because of it.
- **(C3)** At W2, every part of the declaration that a lifted helper is made from has been
  elaborated, so a default there can't pre-empt information that comes later.
- **(C4)** Every other early default (a `match` scrutinee, a `calc` step, `cases`) is replaced by
  waiting, which ends with the same default at W4 where nothing else decides.

**D2090. Make a `match` wait, whole, while what its generalisation reads holds any unsolved
unknown, and land it on main first as a fix of today's bug?** **[Recommend yes.]** Alternatives:
only the queue's unknowns (leaves `motive-param-later.sw` accepted); only stop `check_motive`
skipping (misses `motive-literal-later.sw`: nothing is copied); Lean's rule, generalising only
variable scrutinees (a language change, and proofs rely on generalisation by occurrence,
method-sections.md §5). The assumptions, in full:
- **(M1)** The occurrence test and the motive check are choices whose result can change the
  outcome (which hypotheses are refined, whether the `match` is accepted), so they may not be made
  from an unsolved unknown (invariant 8's "different well-typed meaning" class).
- **(M2)** The scrutinee, inferred with no expected type, is stable (invariant 6), so keeping it
  elaborated while the `match` waits loses nothing.
- **(M3)** An ordinary unknown still unsolved when the declaration ends is an error anyway, so
  waiting on one can't turn an accepted program into a stuck one.
- **(M4)** Measured with the prototype: no example's outcome changes, and aoc and rogue gain no
  failure (6 waits in aoc). Hashes are measured in step 4.0.

**D2091. Report a waiting check's error through the error frames of the constructs it was made in,
print its placeholder as its syntax, and never print a waiting check's type unknown (what would
print it waits)? And take K4's two re-blamed messages (`expected-type-retry.sw`,
`operators-generic-literal.sw`) as the new messages, their comments changed?** **[Recommend
yes.]** The alternative is to render every message after the
declaration's defaults, which needs messages to hold terms instead of text, a larger change with
no case that frames and waiting leave over (the prototype keeps every base message). The
assumptions, in full:
- **(E1)** Every construct that maps the errors inside it does so by a function of the error and
  of what it saved, so the same function can run later, at a resume point.
- **(E2)** An item's error happens in its own saved context, so a frame applied then sees what it
  would have seen inline.
- **(E3)** A placeholder's syntax is what the user wrote, so printing it is never wrong, only less
  resolved than its filled term (which zonking prints once it is filled).
- **(E4)** A message that prints a type unknown of a waiting check is produced by a check that reads
  that type, which question 1's rules make wait; the examples test's list catches any that doesn't.

## As built (step 4.0)

Built on main (`02e83151`, no K4) in the D2090 lane, 31 October 2026. Labels as in the design
section above.

**What waits** [read, `matching.rs`]. `generalised` is the entry of every generalising `match`
(`match e`, `match h: e`, a refutable `let` or lambda pattern, `match reify`). Before it reads
anything it asks `blocker` for an unknown, and if there is one the `match` is queued whole as a
`WaitingMatch` on it, with a placeholder standing for it:
- **an unsolved unknown in a scrutinee as elaborated or in its type, or in a variable's type in
  scope**, whatever made it (a lambda parameter's type, a `.field` waiting for its receiver's
  type, a dictionary the obligations will find). Frozen unknowns (a helper's call, a local
  definition, an open goal) are never solved by elaboration and are not waited for;
- **an unknown the queue has to settle** (`queue::pending`) **in the expected type**.

The scrutinees are kept as elaborated, the alternatives as syntax. Resumed (W1-W4, like any
item), it evaluates the expected type, the types in scope and the scrutinees afresh, asks
`blocker` again (and waits again if needed), and only then generalises (`generalised_now`, the old
body). It has no default. Still waiting at the end, it reports the unknown it waits on as
finishing would (`Check::stuck_error`, `Elaborator::unsolved_error`): a lambda parameter's type is
base's `E-CANNOT-INFER`, unchanged (`reject/match-waits-unknown-parameter.sw`). `cases`' split
(`skip`) doesn't wait: it is a proof search, step 4.2's.

**Its own type is pending while it waits** (`Check::settles_type`). An inferred `match`'s type is
a new unknown (`unknown_type`) that its alternatives fix. Without this, a comparison meeting it
before the `match` resumes failed: `let g := acc => match List.length [acc] with …; g 0` gave
"expected `Nat`, but this has type `?2 n 0`" [run, before the fix], where main accepts it. With
it, the comparison waits (stage 6) and holds once the `match` resumes
(`accept/match-waits-inferred-type.sw`). A waiting `match` doesn't wait for its own type.

**One change from the design: an ordinary unknown in the expected type is not waited for.** The
design said "goal or types in scope hold an unsolved unknown". An inferred `match`'s expected
type is the unknown above, which only its own alternatives solve: waiting for it would wait for
ever, and every inferred generalising `match` would be stuck [read: `infer_match`,
`unknown_type`]. So for the expected type only the queue's unknowns are waited for. The motive
check can then still meet an unknown there; it no longer skips: `check_motive` leaves it for the
lifting of the helper (`Draft::motive_later`), and `check_motive_when_lifted` runs it then, with
every variable the `match` copied, once the alternatives have solved the unknown (`lift`,
`lift_signature`; `preadmit` admits such a helper only if it holds). The same happens when a
`let` in scope holds an auto argument not proved yet (the prelude has one: a `let` whose value
divides by 2, its proof an obligation) [run, debug build]: the occurrence test doesn't read a
`let`'s value, so there is nothing to wait for. A debug assertion says the unknown is in one of
these two places, never in a variable's type or a scrutinee. This closes the expected type's form of the
hole: `reject/match-motive-goal-later.sw` (`apply2 (r => match List.length [n] with …) n`,
`apply2: (a → c) → a → c`) was accepted on main and is `E-MATCH-MOTIVE` now;
`accept/match-motive-goal-later.sw` is the same with a motive that holds. What is left
[inferred, no repro]: the occurrence test can't find a scrutinee inside the expected type's
unknown, so where the alternatives solve it to a type that mentions the scrutinee, the expected
type isn't abstracted. Its annotated twin would abstract it, and could be rejected if that
abstraction alone made the motive ill-formed, while the unannotated one is accepted. Main has the
same behaviour; waiting can't fix it (the alternatives are what solve it); Lean's last resort
below could.

**M3 doesn't always hold** [run]. D2090's assumption M3 says an ordinary unknown still unsolved at
the end is an error anyway, so waiting can't turn an accepted program into a stuck one. It can,
when the only thing that fixes the unknown is the waiting `match`'s own alternatives:

```
let g := acc => match List.length [acc] with   -- or `[n]`: `acc` is in scope
  | Zero => 0
  | Succ k => plus acc k
n                                              -- `g` never applied
```

main accepts both forms (the alternatives make `acc` a `Nat`); step 4.0 rejects both with "can't
work out the type of this function's parameter `acc`". The first form follows from the approved
scrutinee rule; the second from waiting on types in scope. No example, std, aoc or rogue program
has this shape (all check). The alternative that keeps them is Lean's last resort: at quiescence,
generalise anyway, then check the choices once the alternatives have solved the unknown (redo
the occurrence test; reject if it would now copy differently). That is a check, not a default,
but more machinery; a decision for Matt.

**Repros** [run, `sw` at `02e83151` and this branch]:

| file | main | step 4.0 |
|---|---|---|
| `motive-field-later.sw` (`reject/match-motive-field-later.sw`) | checks | `E-MATCH-MOTIVE`, as its twin |
| `motive-param-later.sw` (`reject/match-motive-param-later.sw`) | checks | `E-MATCH-MOTIVE`, as its twin |
| `reject/match-motive-hypothesis-later.sw` (a hypothesis's type fixed later) | checks | `E-MATCH-MOTIVE`, as its twin |
| `reject/match-motive-goal-later.sw` (the expected type fixed by the alternatives) | checks | `E-MATCH-MOTIVE` |
| the three `-annotated` twins (`reject/match-motive-*-annotated.sw`) | `E-MATCH-MOTIVE` | the same |
| `motive-literal-later.sw` | `E-MATCH-MOTIVE` | the same (on main its literals are `Nat` at once) |
| `reject/match-bad-motive.sw` | `E-MATCH-MOTIVE` | the same message |

**Measured** [run]:
- **Examples**: the examples test at the full tier passes (every accept, reject, soundness and
  project example, with their snapshots): no outcome or message changes beyond the new files.
- **Hashes**: `HASH_DUMP_PROJECT=games/rogue` (std and rogue, 5,228 declarations): identical.
  `HASH_DUMP` for std and aoc (10,657): 8 change, all in 2024 Day15's `Proofs/Part2.sw`:
  `moveWideSeparate`, its helpers `%match1` and `%match4`, and the five theorems that use it
  (`moveAllWideCount`, `moveAllWideSeparate`, `moveAllWideWhole`, `part2Count`, `part2Whole`).
  Why [run, scratch prints, removed]: the `match after box held` inside
  `Bool.falseOfNotTrue _ (heldRight => …)` waits for `heldRight`'s type (the `_`, solved by the
  application around it). Nothing is generalised differently: the same scrutinees, no copies,
  either way. What differs is `%match4`'s type (the waiting one): a subterm that comes from the
  solved unknown is a folded call when the `match` is drafted before the unknown is solved (as on
  main) and its unfolding (a `Quot.lift` term) when drafted after; the binders are the same. So
  the change is the form of a definitionally equal type, and the hashes that include it. With only the queue's unknowns
  waited for in the types in scope, no hash changed (the first build of this step), and the
  hypothesis repro was accepted.
- **`task audit`**: std 2,328, aoc 1,363, rogue 190 theorems, all passed.
- **Counters** (`STITCHWORT_TIMINGS`, `check --no-cache`): std and aoc, 8 matches waited, 23
  motive checks left for lifting, 0 stuck; the queue's other counters are base's except `queued`
  and `resumed` (166 and 160 before, 174 and 168 after) and `crossed W1` (15 before, 17 after:
  two waiting `match`es outlived their application). Rogue: 0 and 0, all counters as base.
- **Time**: aoc `check --no-cache`, user time over three runs, base 39.2, 37.0, 37.5 s; step 4.0
  37.1, 36.6, 36.5 s. No difference beyond the noise of a loaded machine.
- **Debug build**: the `builtins` test (the prelude in the debug profile) passes; the assertion
  above first fired there on the `let` case, and was corrected to include it.

## As built (step 4.1)

Built on main (`b6d3626a`, no K4) in the D2091 lane, 31 October 2026. Labels as in the design
section above.

**Error frames** [read, `queue.rs`]. A construct that maps the errors of a check inside it runs
the check in `queue::framed(cx, body, frame)`. On an error from `body` the frame's mapping runs
at once, as the old `match … Err(e) if …` did. If `body` returns with items it queued still
waiting, the frame is made then (its mapping and the context the construct ran in, `Saved`) and
each such item keeps it. An item that fails later, when resumed (W1-W4) or stuck at the end
(`stuck_report`), has its error passed through its frames, innermost first, skipping those still
running: their constructs map the error as it passes through them, as inline. What an item
queues while it is resumed inherits that item's frames, which count as running during the
resumption. So each mapping runs once, at the time and in the context it would have inline.
Frames are made only when something waits, so a construct that waits for nothing costs a push
and a pop. Each construct's mapping is one function used both ways (`ErrorFrame::map`). Two
mappings that work the call out again now get the call kept (`named.rs`: `RigidFrame` keeps the
head and the slots, owned) rather than notes worked out early. Worked out at the call's end, the
"write `(n := 3)`" note was missing: the argument's type wasn't known yet [run].

**Placeholders print as their source** [read, `queue.rs`, `pretty.rs`]. `Check::display` gives
the source a waiting check stands for: `r.items` for a `.field` (with its arguments), the literal
for a record literal, `(.f a)` for a section, the proposition for a decision, `match … with …`
for a waiting `match`. A comparison has no placeholder. `queue::syntax` writes an expression back
out: names, numbers, fields, calls, operators and record literals in full, anything larger as
`…`. The queue keeps `Globals::placeholder_syntax` in step with its unfilled placeholders, as it
does `unfilled_placeholders`, so a restore takes an entry back with its item. The printer shows a
placeholder that way only while it is applied to the variables it was made with, by name. Applied
to others (a lambda's parameter replaced by its argument), the source would name the wrong
variable, so it prints as before (`?4 b b`) [run, scratch file, not an example].

**Type unknowns** (rule 3). On main without K4, every check that waits has a type that is an
ordinary unknown, which unification solves or the stuck report names. The 16 messages that print
`?N` today are each read: each prints an ordinary unknown left unsolved where its error is found
(an implicit argument, a hole, a row, a rewrite rule's argument, the callback's type a
`List.sumByCong` call has not fixed yet). None is a queue placeholder or a waiting check's type,
so none changes here. The design counted 15; `unify-last-arguments-types-differ.sw` (SW-919) was
added after it, the same day. `lambda-after-expected-unfolded.sw`'s goal (`?3 xs x = ?4 xs x`) is
a `rewrite` on a goal holding unknowns, which is step 4.2's.

**The allowlist** [read, `crates/cli/tests/examples.rs`]. `PRINTS_UNKNOWNS` lists those 16 files,
with a comment. The reject and soundness tests fail if a message (its text, labels or notes, not
the source it quotes) shows `?` followed by a digit and the file isn't on the list, and also if a
file on the list no longer does, so the list can't go stale.

**Constructs with their own error mapping** [read; run where an example is named]. Found by the
design's search (`e.code ==`, `map_err`) on main. "Example" means a reject example whose waiting
check gets the mapping only through its frame. Each has an annotated twin in the same file, and
the two messages are the same.

| construct | where | frame | through a waiting check |
|---|---|---|---|
| a `calc` step | `calc.rs`, `check_step` | `StepFrame` | `calc-step-later.sw`: `E-CALC-STEP`; before, `E-REFL` |
| an explicit argument | `check.rs`, `check_arg` | `ArgFrame` | `local-signature-later.sw`: the local signature note; before, none |
| a call's last comparison | `check.rs`, `fallback` | `CallFrame` | none found (a call whose type holds a pending unknown when compared); the mechanism's unit tests |
| a value against a `Comp` type | `check.rs`, `check_inner` (only when the type is `Comp` or `Delay`) | `CompFrame` | none found; the mechanism's unit tests |
| a number group's leaf | `numbers.rs`, `check_leaf` | `LeafFrame` | `negative-argument-later.sw`: "this arithmetic is on `Int`…"; before, none |
| an unbracketed negative argument | `numbers.rs`, `group_tried` | `NegatedFrame` | `negative-argument-later.sw`: the `-g` note; before, none |
| named arguments leaving a parameter out | `named.rs`, `apply_slots` | `RigidFrame` | `named-argument-rigid-later.sw`: both notes; before, none |
| a field given after one left out | `defaults.rs` (`left_out_notes`) | `LeftOutFrame` | `field-default-left-out-later.sw`: the default's note; before, none |
| a local definition's parameter default | `defaults.rs`, `local_helper` | `HelperFrame` | none found; the mechanism's unit tests (a top-level default's helper is finished inside its mapping, so nothing in it fails later) |
| a record update's replaced field | `records.rs`, `update_fields` | `PinnedFrame` | `record-update-pinned-later.sw`: the pinned note; before, none |
| a signature's automatically bound names | `lib.rs`, `local.rs` (`autobind`) | `AutoFrame` | none found; the mechanism's unit tests |
| a `match`'s alternatives | `matching.rs`, `in_alternatives` | `AltsFrame` | none found; the mechanism's unit tests (a waiting `match` maps its own coverage error when resumed) |
| a `decreasing` measure | `decreasing.rs`, `measure_term` | `MeasureFrame` | `decreasing-measure-later.sw`: the measure note; before, none |
| a lambda whose parameter shadows a function | `check.rs`, `check_value` (not in the design's list) | `ShadowFrame` | none found; the mechanism's unit tests |

Not frames, with why:
- **A proposition decided as a `Bool`** (`check.rs`, `decided`; `logic.rs`). The waiting decision
  (`Decide`, D2035) runs `decided`, mapping included, when it resumes. The decision is a proof
  search and queues nothing, so no waiting check fails inside it.
- **`check`'s own `explain_default`.** A waiting comparison applies it itself
  (`Failure::error`), and with K4 no literal is made `Nat` early.
- **Hints the caller of `check_arg` adds** (`unit_call_hint`, `not_a_function_hint`), `if h:`'s
  note on its guard, and `PureFirst::error`. They are not mapped at a resume point, so a waiting
  check that fails inside one of these loses that hint. No example reaches them; they can become
  frames the same way if one does.
- **Operator dictionaries** (`numbers.rs`, `E-INSTANCE-NONE`): obligations, not queue items.

**Tests** [run]:
- Unit tests in `queue.rs`: a later failure goes through nested frames, innermost first; a frame
  still running maps once; a stuck item is reported through its frames; an item queued by a
  resumed item keeps its frames, failing during or after that resumption, mapped once; a waiting
  `.field` prints as `p.row`, and the entry goes when it is filled or taken back by a restore.
- The 7 frame examples above, and `placeholder-shown-as-source.sw`: an `E-REFL` while
  `r.items` waits, shown as `(r.items, 1)` and `(r.items, 2)` (before, `(?4 b r, 1)` and
  `(?6 b r, 2)`). The design's test for the stage-2 `E-AUTO-NONE` naming `?5 b b` has no
  program left to run: stage 3 (D2035) made that decision wait, and the program is accepted
  (`accept/postpone-decide-waiting-field.sw`).

**Measured** [run]:
- **Messages**: the examples test at the daily tier (every file, every snapshot) passes with no
  snapshot changed. The only message changes are the new files above, each an improvement
  (before: base's code or a missing note, or `?N` for a placeholder).
- **Hashes**: `HASH_DUMP` std+aoc (10,658 lines) and `HASH_DUMP_PROJECT=games/rogue` (5,229)
  byte-identical to `b6d3626a`'s.
- **`task audit`**: std 2,328, aoc 1,363, rogue 190 theorems, all passed.
- **Time**: aoc `check --no-cache`, user time, base and step 4.1 alternately on a loaded machine:
  base 40.3, 38.8, 42.2 s; step 4.1 40.7, 43.8, 40.0 s. No difference beyond the noise.
- Lane tiers `elab`, `core`, `std`, `lsp`, `examples`, `hashes`, `aoc`: pass. Clippy with
  `--deny warnings` and `cargo fmt`: clean.

## As built (step 4.2)

Built on main (`a4638278`, no K4) in the D2087 lane, 31 October 2026. Labels as in the design
section above.

**Invariant 7, restated (D2087)** [read, `queue.rs`]. Defaults run at three points, each with
`Queue::settling` set, and `apply_default` asserts it (debug):
- **W4**, `settle_queue`, as before.
- **W2**, `resume_before_lifting`: after the obligations loop, while anything waits, one default
  and the loop again, as at W4. Every caller of `lift` and `lift_signature` calls `finish` right
  after (`lib.rs`, `decreasing.rs`, `defaults.rs`, `partial.rs`), so this is the part's own
  quiescence (C3). What still waits is reported at W4, as before.
- **A `rewrite` rule**, `Elaborator::settle_rule`, called by `elaborate_rule` after the rule is
  inferred: the items queued since the rule began are resumed, then defaulted one at a time and
  resumed again; items queued before the rule are not touched (invariant 3). Where something was
  settled, the rule's type is computed again. The design's "closed" check is a debug assertion
  (`assert_rule_closed`): an item about to be defaulted waits on an unknown made inside the rule,
  which no variable's type in scope mentions and no item from before the rule waits on. The goal
  isn't checked: the rule is elaborated before the goal is read, and an unknown made inside the
  rule can be in the goal only through a solution made while the rule was elaborated, which the
  context check would see first [inferred].

One shared loop (`defaults_from`) runs the three. On main the only default is K1's field-name
rule, so W2 and the rule are reachable only with a record literal; K4 adds `Nat`.

**The pending set of the searches** [read]. `queue::search_pending` is the queue's `pending` plus
the unknown of each obligation not proved yet (an operator's dictionary, an instance, an `auto`
argument), which the obligations loop solves (W3) or reports (W4). The unknowns *in* an
obligation's type (`Add ?T`'s `?T`) are not added: finding the instance doesn't settle them. Only
the searches use it; `pending` itself, which the waiting comparisons (stage 6) and the waiting
`match` (step 4.0) use, is unchanged, so their behaviour is as built.

**`rewrite` and `cases` try, then wait** (`queue::tactic_or_wait`, `WaitingTactic`, the
experiment's addition 3). The tactic runs at once. If it fails while its goal holds an unknown of
`search_pending`, what it did is undone and it is queued, whole, on that unknown; resumed (W1-W4),
it runs on the goal computed afresh, and fails with its own error, or waits again if the goal
still holds such an unknown. Still waiting at the end, it reports the error it first gave. A
`cases` inside a split of a `cases` doesn't wait (the split can't wait in the middle of itself).
Its placeholder prints as `(rewrite …)` or `(cases …)`.

**Counters** (`STITCHWORT_TIMINGS`): `rule settled` (a rule whose own items still waited after
resuming), `rule defaulted`, `tactic waited`, and for `omega`, `ring` and `auto` the runs on a goal
holding an unknown of `search_pending` and the failures among them (`omega on pending`, `omega
failed on pending`, and the same for `ring` and `auto`; `queue::counted_search`). There is no
congruence-closure tactic to count: `congruence.rs` is the lemma lookup used by `rewrite` and
`decreasing`. The `auto` count sees the obligations still in the list when it runs; the round being
proved has been taken out of it, so a goal holding a sibling's dictionary from the same round is
not counted [read, `auto.rs`].

**Day17's hypothesis: refuted** [run, on the experiment `ac4587c9` with scratch traces, not kept].
The design guessed that the `rewrite` at 2024 `Day17/Proofs/Search.sw:46` fails on a goal stuck on
the `<` dictionary, which addition 6 made an obligation. The trace at the failure says otherwise:
- the goal is `?9 output shape target other positive outputs = True`, and `?9` is the only
  unknown in it: `Bool.andIntro`'s second `_`, an ordinary unknown, not a placeholder and not an
  obligation's;
- the obligations then are `Ord Nat` (the `<` dictionary, its type already known), `DecEq (List
  Nat)` and `DecEq Nat`; none is in the goal;
- with the obligations' unknowns counted as pending, for the tactics only and in `pending` itself,
  the result is the same `E-REWRITE-NOTHING`.
`?9` would be solved by comparing `Bool.andIntro`'s result type, `(?8 && ?9) = True`, with the
expected type first (`check::propagate`). That doesn't happen: the expected type of the
`Bool.andIntro …` argument is itself a bare unknown when it is elaborated (`?0 output shape target
other positive outputs`, not pending, made before any queue item), so `propagate` is skipped and
the `rewrite` is elaborated before `?9` is known. Why that argument's type is a bare unknown with
K4 and not on main is not established [not run]; it is the first thing step 4.3 has to look at.
So the widened pending set is right in kind (`rewrite-waits-for-dictionary.sw` needs it) but is
not Day17's fix.

**Tests** [run]. Each accept example is rejected by main (`a4638278`) and has an annotated twin in
the same file that main accepts:

| example | main | step 4.2 | what it shows |
|---|---|---|---|
| `accept/rewrite-waits-for-field.sw` | `E-REWRITE-RULE` | checks | a `rewrite` waits on a waiting `.field` |
| `accept/rewrite-waits-for-dictionary.sw` | `E-REWRITE-NOTHING` | checks | a `rewrite` waits on an obligation's unknown (`Add ?`), with nothing queued |
| `accept/cases-waits-for-field.sw` | `E-CASES` | checks | `cases` waits on waiting `.field`s |
| `accept/rewrite-rule-settled.sw` | `E-REWRITE-RULE` | checks | a rule's record literal gets its field-name default before the search |
| `accept/match-type-default-before-lifting.sw` | `E-UNSOLVED` | checks, test passes | W2's default: a `match`'s helper made with its type known |
| `reject/rewrite-waits-then-fails.sw` | `E-REWRITE-NOTHING`, "looking for `Succ ?8`" | the same code, "looking for `Succ c.size`", as its twin | a waiting `rewrite` that still fails gives its own error against the known goal |

Unit tests in `queue.rs`: W2 applies the defaults as W4 does; a rule's own items are resumed and
defaulted and an item from before the rule is not; the closed assertion fires on a default whose
unknown was made before the rule (debug only). The existing tests that said W2 applies no default
were changed to say it does. `an_item_queued_by_a_resumed_item_keeps_its_frames` (step 4.1)
failed in the debug profile on main (it queued an item on an unknown already solved, which
`queue` asserts against); its item is now solved right after it is queued, and it passes in both
profiles.

**Measured** [run]:
- **Examples**: the examples test at the full tier and `hash_stability` pass; no existing
  snapshot or message changed; the only new snapshots are the new files'.
- **Hashes**: `HASH_DUMP` std+aoc (10,897 lines) and `HASH_DUMP_PROJECT=games/rogue` (5,240)
  byte-identical to `a4638278`'s.
- **Counters** (`check --no-cache`): std+aoc and std+rogue, all of this step's counters are 0
  (no rule settled or defaulted, no tactic waited, no `omega`, `ring` or `auto` run on a pending
  goal); the queue's other counters are `a4638278`'s exactly (aoc: 176 queued, 170 resumed, 17
  waited, 8 matches waited, 23 motives later; rogue: 35 queued, 32 resumed). So on main the change
  is reached only by programs main rejects, which is why no hash moves.
- **Time**: aoc `check --no-cache`, user time, base and step 4.2 alternately on a loaded machine:
  base 36.5, 42.1, 36.7 s; step 4.2 42.5, 37.9, 36.3 s. No difference beyond the noise.
- **`task audit`**: std 2,338, aoc 1,388, rogue 190 theorems, all passed. aoc 944 and rogue 100
  tests pass. The `builtins` test in the debug profile passes, so the new assertions hold on the
  prelude.
- Lane tiers `elab`, `examples`, `hashes`, `aoc`, `std`: pass. Clippy with `--deny warnings` and
  `cargo fmt`: clean.

**What step 4.3 (K4) still needs**, from this step:
- Day17: find why `Bool.andIntro`'s argument is checked against a bare unknown with K4 on (the
  `List.memFilterIntro` call's lambda `a => 0 < a ∧ …` and its group at an unknown type are the
  first suspects) and give it a rule of §5.10's kinds, not a patch; the widened pending set is
  already in.
- K4's `Nat` default plugs into the ladder as it is: `Priority::Nat` loses its `dead_code`
  allowance, and the three points of invariant 7 apply it with no other change. The rule's settle
  should also find the dictionaries its operators need once their types are known
  (`solve_ready_instances`, as the experiment did), which K4's groups at an unknown type create.
- The experiment's additions 1 (`rfl` against a pending head), 5 (a placeholder applied twice
  waits) and 6 (groups built at an unknown type) are not in; additions 2, 3 and 4 are, with
  addition 3's pending set widened.
- The counters decide whether `omega`, `ring` and `auto` join the try-then-wait rule: measure them
  again with K4, where literals wait.

## As built (step 4.3)

Built on main (`c3d51826`) in the D2103 lane, 31 October to 1 November 2026: K4, number literals
wait. Labels as in the design section above.

**What changed** [read].
- **K4** (`numbers.rs`, the experiment's literal and group code, `ac4587c9`): a literal checked
  against a type whose head is an unknown is a `Number` item waiting on it; a number group that
  nothing decides is built at once at an unknown type when it has only `+`, `*`, `<`, `<=` and
  equations (its literals wait, its dictionaries are obligations: addition 6), and waits whole
  (`NumberGroup`) when it has `-`, `/` or `%`. Both default to `Nat` (`Priority::Nat`, no longer
  `dead_code`) at invariant 7's three points, after the field-name rule. A waiting number prints
  as the number, a waiting group as its source (D2091; without that three messages showed `?N`).
- **Addition 1** (`check.rs`): `rfl` against an expected type whose shape is pending is `?x = ?x`
  compared with it, which waits (`queue::headed_by_pending`).
- **Addition 5** (`unify.rs`): a pending placeholder applied twice (`?p a` against `?p b`) is
  not compared by its arguments; the pair waits.
- **The rule settled** (`queue::settle_rule`): after its own checks are settled, the dictionaries
  made inside the rule whose types are now known are found (only those, at or after the rule's
  first unknown). Nothing in the corpus needs it today [run: with it switched off in a scratch
  build, std, aoc and the new example check]; it is kept as the design asks.
- **Decisions wait for their form** (`check.rs`, `decide_or_wait`, `decision_blocker`,
  `DecideTerm`; `logic.rs`, `Condition::Waiting`; `numbers.rs`, `==`): Day17's fix, below.
- **The fills are specialised** (`Elaborator::specialise_fills`, from `finish` and lifting): a
  check resumed late (a decision of `==` waiting for a literal) leaves its operator generic when
  its dictionary is found after it; the projection at the end (§5.10) now runs on the terms the
  checks filled their placeholders with, as on the declaration's own term. Without it
  `effect-rows-uses.sw`'s "a pure use on a computed receiver" lost stage 1's `List.decEq`.
- **A waiting literal is an operand like a literal** (`bind::operand`,
  `queue::waiting_literal`): a decision's search keeps it rather than binding it as a variable,
  and an `if`'s branches holding one don't count as using the proof (`unused_proof_if`).
  Without these, `x == 3` and `if 5 > 0` were written in their bound form, `(%0 => …) 3`.

**Day17: the cause** [run, scratch traces, removed]. Step 4.2's reading (an argument checked
against a bare unknown) was off; the argument's expected type is
`(?4 … other < other && toBool (…)) = True`. What breaks it is the *form* of `0 < a`:
- With K4, in `List.memFilterIntro _ (a => 0 < a ∧ output a == target) …`, `a`'s type is unknown
  when `0 < a` is elaborated (only the later `output a` says it is a `Nat`). Addition 6 builds the
  group at an unknown type, so `<` is the generic `Ord.lessThan [?d]`, and its literal waits.
- `0 < a` is a `&&` operand, a condition: `logic::condition` decides it **at once**
  (`bind::decide`), not through D2035's waiting `Decide`. The decision of a relation written
  through a dictionary is its paired decider, `Ord.decLessThan [?d]`, later projected to
  `toBool (Nat.decLessThan 0 a)`.
- On main, `0` is a `Nat` at once, `0 < a` is `Nat.lessThan 0 a`, the search decides it, and
  `bind::comparison` writes the `Bool` as `Nat.leq 1 a`. `toBool (Nat.decLessThan 0 a)` does not
  compute to `Nat.leq 1 a` (it is stuck on `a`), so they are different values.
- `Bool.andIntro _ _ positive (…)`: `positive: 0 < other` solves the first `_` with main's form,
  `Nat.leq 1 other`; the comparison of `(Nat.leq 1 other && ?9) = True` with the expected type
  (the after-expected path) then fails, `?9` stays unknown, and the `rewrite` finds nothing.
- Evidence: the cut-down repro (now `positiveKept` in `accept/number-literals-wait.sw`) gave the
  same `E-REWRITE-NOTHING`; with the expected type printed, the after-expected comparison read
  `(1 <= other && ?9 …) = True against (Decidable.toBool (Nat.decLessThan 0 other) && …) = True`;
  `positiveAlone` (`positive` passed straight as `p v = True`) was `E-TYPE-MISMATCH` the same
  way; both check once the decision is made from the specialised form.

**The rule** (invariant 8, a consumer §5.10 lacked): a decision is chosen from the
proposition's form, so it waits while the form isn't the one the proposition has when its types
are known at once: while it holds an unfilled placeholder (D2035, as before) or an operator
whose dictionary isn't found yet (found first if its type is known now). Then it is made from
the proposition with its operators specialised and its fills written in. Every decision of a
proposition into a `Bool` follows it: `decide_to_bool` (D2035's, scanning the value, as built),
a condition's (`&&`, `||`, `not`, `if`), and `==`'s (scanning the proposition as written: an
operand's value may be costly to compute, and scanning it ran `bananasBySequence 50 buyers` in
2024 Day22's tests, which then didn't finish). Where the decision itself is a term (`if`'s or
`&&`'s branches using the proof), it is a placeholder of type `Decidable p` that a `DecideTerm`
fills.

**Not needed: resuming between arguments.** I first resumed an application's checks between its
arguments (so the later argument's type held `0`, not its placeholder); Day17 failed the same
way, since the form of `<` was the cause, and once decisions wait it checks without it (the
after-expected path fills in the second conjunct). Dropped.

**Outcomes and messages** [run, every accept, reject and soundness example's whole output,
`c3d51826` against the lane]: exactly the planned ones. `int-binding-nat.sw` moved to accept
(D2084, with tests that `m` is `-2`), `record-literal-inferred.sw`'s "in a list" checks
unannotated, and `expected-type-retry.sw` and `operators-generic-literal.sw` blame the literal
(D2091; the first's comment rewritten). The `?N` allowlist test passes; no other message moved.
syntax.md's "a `let` keeps its own type" and its "Known limit" (`let v := chooseFirst 5 i`, now
accepted) are rewritten.

**Hashes** [measured, `HASH_DUMP` against `c3d51826`, each changed term compared with a scratch
term dump]. Every statement is identical; no literal changes type outside the planned files.
- std + aoc (11,279 lines): 17 change. 5 in their own terms, each a call kept folded where
  main's term has its unfolding: `Std.List.sumByOne` (`List.sumBy` for `List.foldLeft …`),
  `Std.PrefixSums.atOf`, `Std.List.memDifferenceByExample` (`List.Mem` for its unfolding), 2025
  `Day08.Proofs.oneAfterTells` (`joinAll`, `Circuits.separate`) and `Day09.Proofs.allRedOrGreenKeys.%match1`
  (`PrefixSums.block`, `Floor.outside`). 12 only refer to those (2024 Day11's four through
  `sumByOne`; 2025 Day08's two and Day09's five; `PrefixSums.blockSum`).
- std + rogue (5,251): the same 4 std declarations.
- accepted examples (`hash_stability`, full tier): 4 files besides the two new ones, all
  harmless: `generic-constructor-literals.sw` (the constructor wrapped in an `Ann`, the alias
  `IntMark` written as `Mark Int Nat`), `literal-first.sw` (an `Ann`), `rewrite-waits-for-field.sw`
  (the `let`'s type with `Nat.add` read back as `Add.%add [Nat] Nat.instAdd`, its unfolding), and
  `lambda-nested-arrows.sw` (a filled placeholder's `let` value folded back to the other `let`
  with the same value, `nested` for `flat`, as stage 1's deviation 5 allows: equal values).

**Counters** (`STITCHWORT_TIMINGS`, `check --no-cache`) [measured], main → lane:
- aoc: queued 182 → 884, defaulted 0 → 62, waited 17 → 55, rule settled/defaulted 0 → 6, tactic
  waited 0 → 2, stuck 0, `retried` 0 → 0; rogue: defaulted 52, rule 1, retried 0.
- accepted examples, each checked alone and summed: `retried` 1 (main 14 in stage 4's lane),
  in `lambda-propagated-alias.sw`, which main retries too (SW-858's alias, not a literal);
  rejected: 3 (`decreasing-lambda-in-data.sw`, `generic-constructor-literal-conflict.sw`).
- `omega`, `ring` and `auto` on a goal holding a pending unknown: **0 runs** in std, aoc, rogue
  and every example. So they don't join the try-then-wait rule: nothing asks for it.

**Answers and time** [run]: aoc 998 and rogue 100 tests pass; `task audit` (std 2,347, aoc
1,470, rogue 190) passes. aoc `check --no-cache`, one pair on a loaded machine: main 36.8 s, lane
37.2 s wall.

**Stopped after the rebase: 2021 Day08** [run]. Everything above was measured on `c3d51826`.
Rebased onto `a937906d`, which adds AoC 2021 days 6 to 9, aoc fails once, in a proof main
accepts: `Day08/Proofs/Proofs.sw:54`, `E-TYPE-MISMATCH`, "expected `10 * n + decodeDigit …
output = ?4 wiring entry wired perm outputs n output`, but this has type `… = 10 * n + digit`"
(an unknown printed, too). The proof is `List.foldLeftCongMem entry.outputs 0 _ _ (n output m =>
…)`. With `(0: Nat)` written it checks [run], so the waiting literal is the cause. My reading,
**speculative** [inferred, not traced]: `foldLeftCongMem`'s `b` is fixed only by the `0`, the
lambda fails in place (its `n` has no type), and the after-expected path compares
`List.foldLeft xs ?z ?f1 = List.foldLeft xs ?z ?f2` with the statement's unfolding, `List.foldLeft
entry.outputs 0 (…)`; `?z` is the waiting literal's placeholder, frozen (stage 6), and that
comparison is a boolean try-and-undo, so it can't wait or solve it, fails, and `?f1`/`?f2` (the
`_`s) stay unknown. On main `0` is the number and the comparison solves both `_`s. This is the
design's option (c), "seeing through" a waiting literal (a waiting `k` met by the numeral `k` at
a known type takes that type), which the design left for later; it is a decision for Matt, not
a patch. Also from the rebase, on main itself (not this lane) [run, main's binary]:
`reject/if-guard-bracketed-true.sw` checks (SW-944's second reading accepts
`(Succ low < high) = True`), and `goals/bool-constant-branches.sw` has no snapshot (SW-946), so
the examples test fails at the full tier on main.

**Resumed (D2110, SW-986): a waiting literal seen through.** Rebased onto `93eab0f8` (AoC 2021
days 1 to 18, SW-975, SW-982, SW-962, SW-981): no conflict in the code; the one conflict was
`hash_stability__prelude.snap`, taken from main and regenerated. Option (c), narrowly [read,
`unify.rs`]:
- **Where.** `unify_step`, the arm before the one for frozen unknowns: a pair whose one side is
  an unfilled placeholder of a waiting number literal `k` (`Globals::waiting_literals`, kept in
  step with the queue as `unfilled_placeholders` is, from `Check::literal`) and whose other side
  is the numeral `k` at a known type: `Nat`'s `k`, or `Int`'s `OfNat k` (`literal_seen_through`).
  Nothing else: not another number, not a value that only computes to `k`, not `Fin`, `Float`,
  `SafeNat` or a negative `Int`, whose terms differ.
- **What it does.** It solves the placeholder with `other` (a pattern solution; a placeholder
  applied to more than variables fails as before) and compares the type the literal waits on
  with that type. Only while the placeholder is frozen: its own fill unfreezes it and solves it
  as any unknown, and without that guard the fill met the rule and left it unsolved [run: std
  didn't load].
- **Why it can't change a meaning.** A literal `k` checked at `Nat` is the numeral `k`, and at
  `Int` is `OfNat k` (`check_literal`), whether it waited or not; so the solution is the term the
  literal's check will give, and the type it fixes is the only type at which that term is `k`.
  When the literal resumes, its fill finds the placeholder solved and compares (invariant 2):
  the same term, so it agrees (`disagreed` stays 0). It is what main does, where the literal is
  the number from the start.
- It is where the comparison meets the literal: in a boolean try-and-undo too (the after-expected
  path, Day08), not only in stage 6's waiting comparisons, so what such a comparison solves from
  the numeral (Day08's two `_`s) is solved as on main.
- First built without solving the placeholder (only the type compared, the pair taken as equal):
  `quot-transport-ind.sw` failed, since a later comparison still met the frozen placeholder; with
  it solved, it checks [run].
- Test: `accept/number-literals-wait.sw`'s `foldSeenThrough`, Day08's shape (a fold's `0` and
  two `_`s, the lambda failing in place on a `match`): rejected with the rule switched off in a
  scratch build, as Day08 was; checks with it, and on main [run].

**2021 Day17's negative literal (SW-978 item 4): still needs its annotation.** In
`[(7, 2), …, (17, -4)].map (…)`, the tuples' numbers are *inferred* (a tuple checked against an
unknown infers its parts), and an inferred literal is still `Nat` at once: K4 makes a literal
checked against an unknown wait, not one inferred with nothing expected. Making inferred literals
wait too (a fresh unknown, then the waiting check) passes that test and every aoc namespace, but
`accept/calc.sw` (`calc 0`) and `accept/let-patterns.sw` (`let one := 1`) fail, and four
messages change, one printing `?0 a b h` [run]. So it is not in; a decision of its own (it is K4
widened to inferred literals, with its own consumers to find).

**Gates after the rebase** [run, against `93eab0f8`'s binary]:
- **aoc**: `check --no-cache` checks all 207 namespaces (2021 days 1 to 18 included);
  `stitchwort test` 1,216 passed; `task audit`: std 2,358, aoc 2,119, rogue 190, all passed.
  Rogue: 100 tests pass.
- **Examples** (accept, reject, soundness and goals, every file's whole output): the same
  planned changes as above and nothing else: `int-binding-nat.sw` accepted,
  `record-literal-inferred.sw` unannotated, the two re-blamed messages. The examples test and
  `hash_stability` at the full tier pass with the snapshots committed.
- **Hashes** (`HASH_DUMP`, std + aoc 13,877 lines, std + rogue 5,301; each changed term
  compared): 21 and 2 change; every statement identical. Own terms: `Std.List.sumByOne`,
  `Std.List.memDifferenceByExample`, 2025 `Day08.oneAfterTells`, `Day09.allRedOrGreenKeys.%match1`
  (each a call kept folded, as above), and 2021 `Day08.easyCorrect.%match2`, the other way round:
  in `Eq.cong (k => [2, 3, 4, 7].contains k) …`, whose list's literals wait, the call
  `List.contains [2, 3, 4, 7] k` is written as its unfolding (an `if` on `Nat.decEq`), a
  definitionally equal term. 16 refer to those (2021 Day08's `easyCorrect`, its `%match1`,
  `part1Correct`, `part1FromInput`, `part1AnswerUnique`; 2024 Day11's four; 2025 Day08's two and
  Day09's five). `PrefixSums.atOf` no longer changes. 2021 `Day08.valueCorrect`, the proof the
  rule is for, has main's hash.
- **Counters** (aoc): `retried` 1 on main and lane alike (a 2021 day, not a literal); `omega on
  pending` 1 on both, failing 0; `ring` and `auto` 0. `solved first` 37 and `lossy` 3 (0 on main):
  placeholders solved before their fill, the rule's solutions among them [inferred; not traced
  one by one], every one agreeing with its fill (`disagreed` 0).
- **Time**: aoc `check --no-cache`, one pair at load 5 to 17: main 61.7 s, lane 60.1 s.

**Search patterns, found at merge** [run]. The merge tier failed two `stitchwort search` tests
(`search_match`'s `arithmetic_on_holes_is_tried_at_nat_and_at_int`: `_ + 0 = _` found only
`intPlus`; `search_bench`'s hand query `(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _` lost `Nat.leTrans`). Two
causes, both K4's:
- **A pattern is never finished.** `Elaborator::search_pattern` infers it and searches with it;
  nothing settles its queue, so `_ + 0 = _`'s `0` stayed a placeholder and its group on an unknown
  type, and the reading that should be `Nat` matched only what the `Int` reading did. A pattern is
  invariant 7's closed pattern, as a `rewrite` rule is (it is elaborated only to be searched
  for, and nothing else is elaborated with it): it is now settled as a rule is, its own checks
  resumed and defaulted before the search (`Elaborator::settle_pattern`, `settle_rule` without
  the rule's "closed" assertion, since the holes' types it would count as outside are the
  pattern's own).
- **A group with no literal had no default.** `_ ≤ _` on holes (or `a < b` on two values of
  unknown type) is built at an unknown type with its dictionary an obligation, and only its
  literals' defaults made that type `Nat`; with none, nothing did, where main made it `Nat` at
  once. Such a group now queues its type's own default (`GroupType`, a waiting constraint with
  no term, priority `Nat`), so "Nat where nothing says" holds for every undecided group, as §5.4
  says. The tests' expectations are unchanged.

Re-measured after this, rebased onto `8f632914` [run]: aoc 207 namespaces and 1,237 tests, rogue
100, `task audit` (std 2,397, aoc 2,104, rogue 190), the search lane tier (30 tests) and every
lane tier pass. Examples: the same planned changes only. Hashes against `8f632914` (std + aoc
13,820 lines; std + rogue): 24 and 2 change, every statement identical, six in their own terms:
the five above and `Aoc.Common.Proofs.sumByThree` (new on main: `List.sumBy` kept folded, as in
`sumByOne`); the other 18 refer to them. On main itself, `reject/export-record-unchecked-proof.sw`
checks (main's binary too), so the examples test fails at the full tier there.

**What stage 5 can now delete** [inferred from the counters and code]: `retrying` and
`late_literals` with `defers_literal`, `else_first` and `check_items`' reordering (no retry is
about a literal any more; the 1 + 3 left are the cases above, which stage 5 must look at
first); `FieldNames::hold`, `held`, `last_resort` (stage 2); the three "infer the other side"
catches; the lambda try-then-postpone (0 in accepted code since stage 3; 2 in
`lambda-body-error-against-goal.sw`); and `explain_default`'s "this literal made it a `Nat`"
note with `Defaulted`'s literal list, which no literal reaches now except the ladder's own
default.

## As built (stage 5)

Built on main (`7ed84de5`, after step 4.3) in the SW-987 lane, 1 November 2026: step 4.4, the
catch-and-retry paths of §5.11 removed where nothing uses them any more. Labels as in the design
section above.

**Method** [run]. A first commit adds a `STITCHWORT_TIMINGS` counter for each path that had none
(`retried for a constructor`, `last resort`, `append other side`, `calc from goal`, `leaf
uninferred`; `lambda postponed` and `retried` were there). Each counter was read over std and aoc
(`check --no-cache` in `aoc/`), std and rogue, and every example (each accept, reject, soundness,
extract and goals file and each project, checked alone). A path is removed only with its counter
at 0, or, where it fired only in a rejected example, with that example's message unchanged without
it. Each removal is its own commit, and removes its counter.

| path | counter before | commit | what replaces it |
|---|---|---|---|
| `held`, `last_resort`, `FieldNames` | `last resort` 0 everywhere (`FieldNames::hold` was already dead code) | `fa1a45b3` | K1 and the field-name default (stage 2) |
| `++`'s "infer the other side" | `append other side` 0 everywhere | `594ae4c7` | the left side always infers: what can't say its type waits; `[] ++ xs`, a `match` of lists and a mapped list on the left were tried and infer |
| `calc`'s first term checked against the goal (`hint`) | `calc from goal` 0 everywhere | `28e96524` | the same; `elaborate` no longer takes the expected type |
| the lambda try-then-postpone (`unknown_domain`) | `lambda postponed` 0 in std, aoc, rogue and accepted code; 2 in `reject/lambda-body-error-against-goal.sw` | `7a08a533` | K1-K4 and the waiting `match` inside the lambda, resumed at W1. The reject example's lambda now takes the after-expected path (kept, §5.11) and gives the same `E-OMEGA`, byte for byte |
| a constructor with literals put last: `defers_literal`, `else_first`, `check_items`' reordering, the `if`, list and comparison retries, the group's pass-2 reordering | `retried for a constructor` 0 in std, aoc, rogue and accepted code; 2 in `reject/generic-constructor-literal-conflict.sw` | `98d768a6` | K4: the literal waits, so order doesn't matter. The reject example's first and second runs gave the same error; its message is unchanged |

About 310 lines of the elaborator go (416 removed, 103 added, counters included). Two of T2's three
same-state reruns (§5.7) were the lambda postponed and the constructor retry; the first is gone,
and `retrying`'s second run now happens only for a list of numbers.

**Kept: `retrying` and `late_literals`, for a list of numbers in an application** [run]. `retried`
is 1 in aoc and 2 in the examples, and in two of them the second run is what makes the program
check (or fail the right way). Each is a gap in what waits, not a literal ordering:
- **2021 Day17's tests**, `[(7, 2), (6, 3), (9, 0), (6, 9)].map (((dx, dy)) => firstHit
  exampleTarget { dx, dy }) == …` (`Tests/Examples.sw:27`). The first run fails with "expected
  `Int`, but this has type `Nat`" at `dx`: a tuple checked against an unknown *infers* its parts,
  so its literals are `Nat` at once (step 4.3 found the same for item 4 of SW-978). The second run
  checks the list after the lambda, against `List (Int, Int)`. Fix in kind: a tuple checked
  against an unknown makes it a pair of two new unknowns and checks its parts against them, so
  its literals wait (K4 widened to tuples); not done here.
- **`reject/decreasing-lambda-in-data.sw`**, `List.map [d => if h: d < n then stored d else 0]
  ((g: Nat → Nat) => g (n - 1))`. The first run fails with "this is a function, but the expected
  type is `?2 n rec`": a lambda checked against an unknown applied to variables fails rather than
  making it a function type or waiting. The second run checks the list after the second lambda
  has said the element type, and the file gets its intended `E-DECREASING`. Without the retry its
  error would be that `E-TYPE-MISMATCH`, printing `?2 n rec`.
- The other two firings change nothing: `accept/lambda-propagated-alias.sw`'s `summed` fails both
  runs with the same `E-UNKNOWN-FIELD`, and the file checks anyway (an attempt around the
  application succeeds; which one wasn't traced), and the reject
  example above's constructor firings are gone with `98d768a6`.

**Kept: the group leaf's "infer the other side"** (`numbers::speculate`) [run]. `leaf uninferred`
is 4 in every run: the core's `Bool.symThenSelf` and `DecEq.symThenSelf`, `rfl = Eq.trans (Eq.sym
q) q` (`core/Decidable.sw:130`, `core/DecEq.sw:57`, each elaborated twice). `rfl` alone can't be
inferred; the other side gives the equation's type. Addition 1 makes `rfl` wait only when it is
*checked* against a type whose shape is pending. Fix in kind: `rfl` inferred as `?x = ?x` at a new
unknown type, or the leaf waiting; not done here.

**Not in the list, left as it is**: `explain_default`'s "this literal made it a `Nat`" note with
`Defaulted`'s literal list (step 4.3 listed it as deletable); and the after-expected path, kept by
design (§5.11).

**The attempt site SW-981 added** (`effects.rs`, `plain_value`, `performs_nothing`, used for an
argument run first, a `let`'s value and an `if`'s condition in a computation's row) [read]. It
keeps T1: two fixed alternatives (as plain calls through `check::pure_first`, then, undone, run
with `bind` as before), and its only loop is `pure_first`'s row retry, which repeats only on
progress. It shouldn't become a queued item waiting on the row. The enclosing callback's row,
the unknown one, isn't what decides: whether the expression performs is decided by its own
callbacks, which its own elaboration settles (`retry_rows_from`), so waiting on the enclosing row
would wait for nothing that helps. And the choice changes the shape of the term around the rest of
the block (a transparent `let` or a `bind`), which a placeholder fill can't stand for. Two things
to note: a bare row of the expression still unknown after it is elaborated is set to the empty row
at once (`settle_empty`, from stage 3 of effect polymorphism, D1123): a choice made from an
unknown, the one place a wait could matter, but older than SW-981 and with no repro of a later
argument making that row effectful. And `performs_nothing` elaborates an `if`'s condition as plain
calls, undoes it, and `check_if` then elaborates it again the same way (`check` reaches
`pure_first` for it): a same-state rerun, bounded (once per condition), so T1 holds, but wasted
work that doubles per nested condition of this kind.

**Gates, per removal** [run]: lane tiers `elab` and `examples`; `check --no-cache` over aoc (std
included) and rogue; `task audit` (std 2,397, aoc 2,124, rogue 190, all passed); and every
example's `check` output and exit code compared with the counters build's (`1c863e6c`, whose
output is main's). No outcome or message changed. One run differed, once:
`reject/rfl-long-computed.sw` lost its counterexample note during the last gate, which ran beside
a hash dump at load 35-40; three more runs each of the counters build and the last build all
show the note, so it is the counterexample search's time limit, not this stage.

**Hashes** [run]: `HASH_DUMP` std + aoc (13,809 lines) and std + rogue (5,366), main and this
lane: byte-identical. `hash_stability`'s examples, projects and prelude (lane tier): pass.

**Counters after** (aoc): `retried` 1 (Day17), `leaf uninferred` 4; the queue's own counters
exactly main's (1,071 queued, 983 resumed, 63 defaulted, 0 stuck). Rogue: `retried` 0, `leaf
uninferred` 4.

**Time**: aoc `check --no-cache`, one pair at load 35 to 40: main 66.9 s user (103 s wall), this
lane 65.6 s user (89 s wall). No slowdown.

**Open**: the two gaps above (tuples checked against an unknown; a lambda checked against an
unknown applied to variables), after which `retrying` and `late_literals` can go; `rfl` as a
comparison leaf, after which the leaf catch can go; `explain_default`'s literal note.
## Stage 7: design (expected type first, proof searches last)

Written in the SW-988 design lane, 1 November 2026, on main `0602e074` (step 4.3 merged).
Labels as in the stage 4 design: **[run]** run on 1 November; **[read]** read in source
(Stitchwort at `0602e074`; Lean 4, Agda and Idris 2 at the commits of [Sources](#sources)); **[inferred]**
my reasoning, not tested. The repros, the other systems' versions of them and their output, and
the scratch prototype's patch (**PROTOTYPE, not for merge**: everything behind `SCRATCH_*`
switches) are in [postponement/stage7/](postponement/stage7/).

### In short

- **The problem.** AoC 2021 met, on six days, a call whose proof argument was checked before
  what fixes its goal: the call's `_`s, the expected type, a later argument, a dictionary. The
  proof search then fails, or worse, succeeds by guessing (`cases` proving `?a.x = ?b.x` by making
  `?b` be `?a`, SW-969).
- **What main already does.** Some forms of the cases check on main: cases 2 and 4 as a theorem's
  body (the after-expected path catches the failure), case 6 where its goal is known, case 7 over
  a list that doesn't compute. `examples/accept/argument-order-expected.sw` keeps them. In the
  forms AoC met, eight of the nine cases fail on main and one couldn't be reproduced (the table
  below).
- **Rule 1, proof searches last** (the prototype): an `omega`, `cases`, `ring`, `rewrite` or `rfl`
  argument is checked after the call's other arguments, its own waiting checks, its comparison
  with the expected type and the instances now findable. It fixes SW-969 and both SW-971 shapes,
  and `rfl` under a hole (SW-963), and every aoc namespace still checks **[run]**.
- **Rule 2, a failed search waits on any unknown**: today `rewrite` and `cases` wait only on the
  queue's unknowns. Widened to any unsolved unknown, and to `omega` and `ring`, as D2090 widened
  the `match` rule. It is for proofs inside lambdas, which rule 1 can't reach [inferred].
- **Not recommended now: Lean's expected type before every argument.** Built in the prototype, it
  fixed none of the cases and broke nine accepted examples (the `Float` builtins, an alias) and
  changed twelve reject messages [run].
  Today's `propagate` before the first argument and the after-expected path stay.
- **D2118: inferred literals can wait**, with two fixes beyond the plain change: the
  literal's type unknown and its placeholder made with no variables, and a resume point inside
  `calc`. With these, `calc.sw`, `let-patterns.sw`, Day 17's list and every aoc namespace check
  [run]. Five messages and two warnings change; each has its own small fix, listed below.
- **Two cases are not about order**: a `_` against an expected type that reached the call already
  computed (SW-771 item 2, SW-976 (3)), and a congruence lemma inside a `rewrite` rule, where
  nothing says its functions (SW-967 (3)). They need folded expected types and stage 6's waiting
  for flex-flex pairs; separate tickets.

### The cases

Each repro is in [postponement/stage7/](postponement/stage7/); "main" is `0602e074`'s binary.

| # | ticket, AoC | repro | main | why it fails | fixed by |
|---|---|---|---|---|---|
| 1 | SW-969 (2), 2021 day 13 | `ext-cases.sw`: `P.ext _ _ cases cases` | `E-TYPE-MISMATCH` "expected `q = shift b p`, but this has type `q = q`" | `P.ext`'s result `x = y` mentions its explicit `_`s, so `propagate` doesn't run (`written_result` gives `None`, `check.rs`). The first `cases` is checked in place against `?a.x = ?b.x` and succeeds by solving `?b := ?a` [inferred from the message]; it didn't fail, so the after-expected path never runs [read] | rule 1 [run] |
| 2 | SW-971 (1), 2021 day 14 | `omega-before-later.sw`, `lambdaFirst` | `E-OMEGA`, its goal holding `?2 counts pair given x` (the waiting `entry.snd`) | the call is a `match` scrutinee, so nothing is expected of it and there is no after-expected path; `omega` runs before W1 resumes the lambda's `.snd` and `==`. As a theorem's body it checks [run] | rule 1 [run] |
| 3 | SW-971 (1), 2021 day 14 | `omega-before-later.sw`, `autoFirst` | `E-OMEGA`, `DecEq.%decide ?1 first c` in the goal, `Char.decEq first c` in the fact | the `[auto eq: DecEq a]` dictionary is found in the obligations loop (W3), after the call. Even the after-expected retry sees `?1` [run] | rule 1's step "instances now findable" [run] |
| 4 | SW-963 (2), 2021 day 10 | `lambda-before-later.sw`, `lambdaFirst` | `E-OMEGA` "needs to know the goal" | the lambda's domain `f x = Some y` is not headed by an unknown, so it isn't postponed (`unknown_domain`); it is checked in place, and its `omega` meets `?f a`. In a `let`, nothing is expected, so no retry. As a theorem's body it checks [run] | rule 2 [inferred]; rule 1 alone doesn't [run] |
| 5 | SW-963 (2), 2021 day 10 | `lambda-before-later.sw`, `rflUnderHole` | `E-REFL` "`firstOf [3, 4]` and `Some 3` aren't equal" | a bug on main, apart from order: `rfl` fails in place and is retried after the expected type, but against its goal *as computed before* the `_` was solved, so `List.head ?xs`, stuck, stays stuck. With the goal evaluated afresh (`quote`, then `eval`) it checks [run, scratch]. This is day 10's "the message printed the solved hole" | rule 1, which reads the goal afresh [run]; or a one-line fix in the after-expected loop now |
| 6 | SW-967 (3), 2021 day 12 | `congruence-holes.sw` | `sums` (a theorem's body) checks; `viaRewrite`: "expected `?4 xs (Succ k) = ?4 xs (Succ k)`"; `viaTrans`: "`1` and `?8 xs 0` aren't equal" | a `rewrite` rule is elaborated with nothing expected (D2087), so nothing says `f1` and `f2`; the callback's `rfl` compares `?f1 0` with `?f2 0` and the unifier makes them one unknown, a guess [inferred: the message shows one unknown on both sides]. In `Eq.trans` the goal's right side is itself unknown | not order: stage 6 would keep the flex-flex pair waiting instead of guessing [inferred]; meanwhile, write the functions |
| 7 | SW-771 item 2 (2024 day 16), SW-976 (3) (2021 day 16) | `predicate-hole-literal-list.sw` | `E-TYPE-MISMATCH` "expected `?1 x member found x`, but this has type `lookup x = Some 2`" | the expected type reaches the call already computed, `lookup 1 = Some 2 ∨ …` (a scratch trace at the call) [run], so `?p` is met applied to numbers, not a pattern. Comparing before each argument (Lean's rule, prototyped) doesn't help: both sides are disjunctions by then [run]. With a list that doesn't compute it checks | not order: keep the statement folded where it is the body's expected type (folded-calls.md), so `List.Any ?p xs` meets `List.Any f xs` by arguments first, as Lean seems to [unconfirmed in source]. Lean accepts it [run] |
| 8 | D2118, SW-978 (4), 2021 day 17 | `literal-tuples.sw`: `[(7, 2), (6, 3), (17, -4)].map (((dx, dy)) => { dx, dy })` | `E-TYPE-MISMATCH` "a `Nat` can't be negative" at `-4` | a tuple checked against an unknown infers its parts, and an inferred literal is `Nat` at once (`infer_inner`, `Expr::Num`); the first tuple makes the list `(Nat, Nat)`, then `-4` is checked against `Nat` | K4 widened to inferred literals (below) [run] |
| 9 | SW-976 (3), 2021 day 16 | none | | `E-RESOURCE` with no location: **not reproduced**. AoC's code no longer has the shape; three reconstructions in a scratch copy of aoc (`appendCong3 _ _ _ _ _ _`, `soundStep _ after left _ …`, `fieldsCong False _ _ _ _ _ _ _` in `Day16/Proofs/Sound.sw`) all check on main [run] | probably case 7's family [inferred] |

SW-771's first item (a lambda before the argument that fixes its type, 2024 day 16) was fixed
before stage 7 (`lambda-postponed-dependent-argument.sw`).

### D2118: inferred literals waiting

**The experiment.** `infer` of a number literal makes a fresh unknown type and checks the literal
against it, so it waits (K4) like a checked one (`SCRATCH_INFER_WAIT`, the step 4.3 lane's
change) [run]. Day 17's list checks and its test passes. Two accepted examples fail, and seven
example outputs change: five reject messages (the step 4.3 lane counted four; its `?0 a b h` is
`ring-coefficient-after.sw`'s) and the warnings of two accepted examples. One by one:

**`calc.sw`, `zeroLe`** (`calc 0` / `_ ≤ n` / `_ ≤ m := h`), "`0 ≤ n` doesn't hold by
computation" [run]. `calc` infers its first expression, so `0` is a waiting literal of type `?T`.
The first step's `≤` unifies `?T` with `Nat` (`elaborate_tried`, `calc.rs`), but nothing resumes
the literal: `calc` is not an application, so it has no W1. `by_computation` then compares
`Nat.leq ?p n` with `True` by plain `unify`, which can't wait, and fails. (The message prints `0`
for the placeholder, as D2091 asks, which hides the cause.) Making `by_computation` wait (stage 6's
`compare_waiting`) moves the failure to `check_calc`'s own last comparison, `E-CALC-GOAL`, which
can't wait either [run]. **What works**: a resume point in `calc` after each step's type is fixed,
scoped to the items made since the `calc` began (`resume_application(queued_from)`, a W1 for
`calc`) [run: `SCRATCH_CALC_RESUME`]. This is close to Lean, which defaults after each `calc`
step (`Calc.lean:123`, `:128`, as the stage 4 design notes), except that a resume point applies no default.

**`let-patterns.sw`, `sumTreeLifted`** (`let one := 1` / `let Node x kids := t` / `x * one + …`),
"expected `Nat`, but this has type `?0 (Node x kids)`" [run]. The literal's type unknown is made
by `fresh_meta`, which applies it to every variable in scope, so `one: ?0 t`. Matching on the
variable `t` substitutes `Node x kids` for `t` in the types in scope, so `one: ?0 (Node x kids)`,
and `?0 (Node x kids) = Nat` is not a pattern: the unifier can't solve it. On main `one` is a
`Nat`, closed. It isn't the step 4.0 `match` rule: the `match` doesn't wait (`match waited` 0
[run]), since a match on a variable refines the context rather than generalising. Agda shows the
same shape, `Number (_B_55 7)`, for a pair's second type (other-runs.txt). **What works**: make the
type unknown with no variables (`Term::Meta(new_meta)`) [run: `SCRATCH_CLOSED`]. A numeral's type
is `Nat`, `Int`, `Float`, `SafeNat`, `SafeInt` or `Fin n`, and only `Fin n` can mention a
variable; a closed unknown can't become `Fin n` for a local `n`, which main can't do for an
inferred literal either (it is `Nat`). Lean's fresh type is a metavariable of the local context,
not applied to its variables, so a `match` doesn't touch it (`lateInt` in lean-s7.lean, a literal
typed `Int` by a use inside a later `match`, checks [run]).

**The same, for the placeholder.** With only the type closed, aoc fails at 2024
`Day16/Proofs/Part2.sw:203` [run]: `(way => (way, 0))`'s `0` is a placeholder applied to `way`, and
after β it meets `(…, 0)` applied to a record, not a variable, so the seeing-through rule (D2110)
can't solve it. A literal's value at a closed type mentions no variable either, so its placeholder
is made closed too (in `queue`, for a literal whose type quotes with no variable). Then Day16
checks [run].

**With the three changes** (inferred literals wait; type and placeholder closed; a resume point in
`calc`): `literal-tuples.sw` checks and its test passes; `check --no-cache` checks all 207 aoc
namespaces; every accepted example checks [run]. Hashes, `stitchwort test`, rogue and the debug
build were not run. What changes, against main, in the whole output of every accept, reject and
soundness example [run]:

| example | change | why | what a correct version does |
|---|---|---|---|
| `accept/sequence-expression.sw`, `accept/abilities-edge.sw` | the `W-NO-EFFECT` warnings for a dropped literal (`(1; 2)`, a `3` line) are gone | the no-effect check sees a placeholder, not a literal | count a waiting literal as pure, as `bind::operand` does already (`queue::waiting_literal`) |
| `reject/ring-coefficient-after.sw` (`ring [h * 2]`) | "this is `?0`" (unclosed: "`?0 a b h`") where main says "this is `Nat`" | `ring` reads its fact's type while the `2` waits: a type unknown printed, against D2091's rule 3 | a `ring` or `omega` fact list is a closed pattern, settled as a `rewrite` rule is (D2087): its `2` defaults to `Nat` first, main's message |
| `reject/append-numbers.sw` (`1 ++ 2`) | label "this is a `?0`" | `++` chooses its instance from the left operand's type at once | `++` waits like a number group's operator (an obligation), so the message is made after the default: main's |
| `reject/tuple-value-for-type.sw` (`(1, 2) → Nat`) | `E-TYPE-MISMATCH` "expected `Type`" where main says `E-NOT-A-TYPE` | `check_type` makes an unknown type of types `Type` (§5.10's allowed class), and the literal resumes against `Type` | a numeral where a type is expected is decided by its syntax: `E-NOT-A-TYPE` at once |
| `reject/unfold-of-failed-definition.sw` (`2 [decreasing := …]`) | "the parameter names of this function aren't known here" where main says "this function has no parameter named `decreasing`" | named arguments read the head's type, an unknown | a numeral as a function head is decided by its syntax: never a function |
| `reject/sequence-in-let-value.sw` (`let x := 1; 2; x` as `Text`) | the error moves from `x` to the `1`, with "a numeral can only be the prelude's `Nat` or `Int`"; the `W-NO-EFFECT` for `2` is gone | `x`'s type is fixed by `Text` before the literal resumes | the new place is right (the literal is what can't be `Text`), as D2091's re-blamed messages; the warning as above |

So a correct version is the three changes plus the four small rules of the last column. Each is a
consumer that reads a literal's type or shape at once, the kind step 4.0 listed: the same method
(find every consumer, give each wait, a closed-pattern default or a syntactic decision) covers them.

**What the other systems do** with D2118's case [run, other-runs.txt and lean-runs.txt]:
- **Lean 4**: a numeral with nothing expected is `@OfNat.ofNat ?α n ?inst` with `?α` a fresh
  type metavariable (`mkLitTypeFor`, `BuiltinTerm.lean:208-226` [L8]); `?α` is decided by
  unification or, at quiescence, by default instances in priority order (`synthesizeUsingDefault`,
  [L1] `:237-243`). `-4` adds `Neg ?β`, whose default `instNegInt` is `mid`, above `instOfNatNat`'s
  `low` (`Int/Basic.lean:120-135` [L9], `Prelude.lean:1411` [L7]). So `[(7, 2), (17, -4)]` alone is
  `List (Nat × Int)`, and mapped to a record of `Int`s it is all `Int` [run].
- **Idris 2**: with the prelude, a literal is `fromInteger n` (`Desugar.idr:434-442` [I5]), its
  `Num ty` found by search; where nothing fixes `ty`, the `%defaulthint defaultInteger : Num
  Integer` does (`Prelude/Num.idr:99-104` [I6]). All three forms check [run].
- **Haskell**: numerals are `fromInteger n :: Num a => a`; an ambiguous type variable with a
  numeric class constraint is defaulted by the module's `default (Integer, Double)` declaration
  (Haskell 2010 Report §4.3.4 [unconfirmed: cited from memory]). GHC reports each default under
  `-Wtype-defaults` [run].
- **Agda**: literals are overloaded through `Number` and `Negative` instances
  (`Agda.Builtin.FromNat`, `FromNeg`), which wait until their type is known; there is no
  defaulting, so the unannotated list is "unsolved metas" while the mapped one checks [run].

So every system with overloaded numerals makes them wait for their type, also with nothing
expected; Lean, Idris and Haskell then default, Agda reports. Stitchwort's K4 does this for checked
literals; D2118 extends it to inferred ones, which is where Lean starts (it has no checked/inferred
split for numerals).

### What the other systems do with argument order

- **Lean 4** [L10, `Elab/App.lean`]:
  - *The expected type first.* Before each explicit argument that isn't `_`, `?_` or `by …`
    (`shouldPropagateExpectedTypeFor`, `:516-523`), until it once succeeds, `propagateExpectedType`
    (`:525-608`) computes the result type after the remaining arguments (`getResultingTypeCore?`,
    `:449-502`) and, unless it depends on them (`hasLooseBVars`) or has optional or auto
    parameters, unifies it with the expected type; a failure is ignored. It is skipped when the
    expected type is `Prop` itself (`:577-596`) and when eta arguments are pending (`:567`).
    `finalize` (`:610-657`) compares again at the end, after trying the instances
    (`trySynthesizeAppInstMVars`).
  - *`etaArgs`*: named arguments that leave an explicit parameter out make the call a lambda over
    it (`:199-206`, `:731-738`); propagation is skipped while there are any (`:567`).
  - *First-order unification*: `?m a₁ … aₙ =?= f b₁ … bₖ` with a non-variable `aᵢ` is solved as
    `?m a₁ … aᵢ =?= f` and the rest pairwise, when the `foApprox` setting is on
    (`Meta/ExprDefEq.lean:900-925`, `:1366-1395` [L11]); whether the application elaborator turns
    it on is [unconfirmed].
  - *`by` blocks last.* `by tac` against a known type is a synthetic-opaque metavariable of kind
    `.tactic` (`elabByTactic`, `BuiltinTerm.lean:178-187` [L8]; `mkTacticMVar`,
    `TermElabM.lean:1474-1482` [L2]); `synthesizeSyntheticMVars` runs tactics only after resuming,
    defaults and the postponing-off retries have all stopped making progress
    ([L1] `:661-667`, `runTactics` at `:590-598`). With nothing expected, `by` postpones
    (`tryPostpone`).
  - Our cases in Lean (lean-s7.lean, lean-runs.txt) [run]: `holesTac` (`ext' _ _ (by first | rfl |
    exact sameX) …`) checks: the blocks see `q.x = (shift b p).x`; so does `holesNoExpected`, a
    `have` with no type, since blocks wait to the end of the declaration. `holesTerm`
    (`ext' _ _ rfl rfl`) shows the propagation: the error's application is `ext' q (shift b p) ?m.8
    rfl`, the `_`s solved from the expected type before `rfl` was checked. `anyHole` (case 7),
    `autoFirst` (case 3, `by omega` after `[DecidableEq α]`), `sumTreeLifted`, `lateInt` and
    `zeroLe` check.
- **Agda** [A5, `Rules/Application.hs`]: before each visible argument, "check the target type if
  we can get away with it" (`:710-800`): if the type after the remaining visible Πs is rigid and
  doesn't mention them, it is compared with the expected type, constraints allowed. Lean's rule,
  with "rigid" for Lean's "not a metavariable". A lambda whose expected type isn't yet a Π is
  postponed (`CheckExpr` on its blocker, `Rules/Term.hs:575-606`, [A4]; `checkPostponedLambda`,
  `:795-810`). Agda has no built-in tactics; a reflected tactic argument runs at once and, if it
  is blocked on a metavariable, becomes an `UnquoteTactic` constraint woken when that is solved
  (`unquoteTactic`, `Rules/Term.hs:1539-1557`): "try, then wait", step 4.2's rule.
- **Idris 2** [I7, `TTImp/Elab/App.idr`]: `checkRestApp` (`:411-455`) "choose[s] elaboration order
  depending on whether we know the return type now": where it is known (concrete) and the argument
  "needs delay" (a lambda, `case`, a local definition, a record update, an ambiguous name,
  `%search` or `rewrite`, `needsDelayExpr`, `:297-316`), the rest of the application is elaborated
  first, the result unified with the expected type at its end (`checkExp`), and the argument after.
  That is rule 1 with lambdas included. With the return type unknown it goes left to right.
- **Haskell**: no proof arguments; GHC's bidirectional checking pushes a known result type into
  arguments, which doesn't bear on our cases [not read].

What each would do with our cases [inferred from the above unless run]: Lean checks 1, 3, 7 and
D2118 [run]; 2 and 4 as `by omega` blocks (run last) [inferred]; 5 as `by rfl` [inferred]; 6 would
need its functions (Lean postpones `?f1 0 =?= ?f2 0` rather than guess, but in a `rw` rule nothing
fixes them later either) [inferred]. Idris would check 1, 2, 4, 5 by elaborating the `rewrite`,
lambda and searches after the rest when the return type is concrete [inferred, not run]. Agda would
take case 7's target check by arguments first if the target is rigid [inferred].

### The rules

**Rule 1: proof searches last.** In an application, an explicit argument that is `omega`, `cases`,
`ring`, `rewrite … [in …]` or `rfl` (bracketed or not) is not checked where it stands, if no
later parameter's type depends on it (`only_lambdas_depend_on_it`). Its place holds a placeholder,
and it is checked once all of this has happened, in this order:
1. the other arguments, and the lambdas the call already postpones;
2. W1, the application's own waiting checks (D2014);
3. where something is expected of the call and no implicit parameter is left to insert, the
   call's type compared with it (`unify`, then `unify_solving_arguments`, as the after-expected
   path does); a failure is left for the call's own last comparison to report;
4. the instances whose types are now known (`solve_ready_instances`), then W1 again;
5. the searches, in written order, each against its goal read afresh (`quote_folded`, then
   `eval`, so a call stuck on an unknown solved since computes, case 5).

This is Lean's "`by` last" scoped to one application, and Idris's order for searches. It is not
a queue item: it runs inside the application, as the after-expected path does, and never crosses
W1 (invariant 3 holds trivially). The `auto` arguments need nothing new: they are obligations,
and step 4 finds those that are ready before a search reads them.

*Why `rfl` with the searches*: `rfl` is a comparison, not a search, but it chooses as a search
does: proving `?a.x = ?b.x` by `?b := ?a` is SW-969's harm, and `reject/partial-constructor-mismatch.sw`
is the same with `rfl` (`Eq.cong (Call o) rfl` against `Call o f = Call o g` today reports
"`Call o f = Call o f`"; with rule 1, "`f` and `g` aren't equal" at the `rfl`, a better message)
[run]. But with `rfl` included the prototype broke `std/Float/Theory.sw:1215` (an `rfl` inside
`magnitudeExact (Succ k) rfl hm`, whose result type is an unknown) [run, cause not established];
hence question Q2.

*Why not lambdas* (Idris does them): stage 7 keeps §5.2's end state, a lambda checked in place with
its stuck pieces waiting; Lean and Agda do the same. A lambda that holds a search is rule 2's.

**Rule 2: a failed proof search waits on any unsolved unknown.** Step 4.2's `tactic_or_wait`
(`queue.rs`) runs `rewrite` and `cases` at once and waits, whole, only if the goal holds an unknown
of `search_pending`. Widen it: (a) to `omega` and `ring`; (b) to any unsolved, unfrozen unknown in
the goal, as D2090 widened the `match` rule. A search inside a lambda (case 4) then waits for
`?f`, which the later argument solves, and is resumed at W1. An unknown still unsolved at the end is
an error anyway; the search reports the error it first gave (as built). Step 4.3 counted `omega on
pending` 1 in aoc, failing 0, so (a) changes nothing in the corpus [run, step 4.3's counters];
(b) is not measured.

**Rule 3 (not recommended now): the expected type before every argument.** Lean's and Agda's rule
in full: before each explicit argument but `_` and searches, until it once holds. The prototype
(`SCRATCH_PROPAGATE_EACH`) fixed none of the nine cases: 1 to 5 by rule 1 alone, 7 because the
expected type is already computed [run]. And it broke nine accepted examples: eight through
`std/Float/Float.sw` (`E-BUILTIN`, "the library's `Float.neg` isn't the declaration the
compiler's `Float` support was written for": a pinned native's term changed, and the same error
replaced the messages of eight `float-*` reject examples and `counterexample-library-types.sw`), and
`lambda-propagated-alias.sw` ("`List` has no field or function `total`"). Two effect reject
examples lost their `E-ABILITY` (`map-callback-effectful-later.sw`, `map-effectful-callback-pure.sw`):
`propagate` keeps a result's bare row for the arguments (`effects::unknown_bare_value`, D1124) and
the prototype didn't [run]. Each could be handled as `propagate` handles it, but with
no case wanting it, today's `propagate` before the first argument plus the after-expected path
stay.

**Rule 4: inferred literals wait** (D2118). An inferred number literal has a fresh type unknown
and is checked against it (K4). For every number literal whose type mentions no variable, the type
unknown and the placeholder are made with no variables. `calc` gets a resume point after each
step's type is fixed, for the items made inside it. The four consumers of the table above get
their rules: a waiting literal is pure for `W-NO-EFFECT`; `ring` and `omega` facts are closed
patterns (D2087's settle); `++` waits as an operator does; a numeral as a type or as a function
head is decided by its syntax.

**When the expected type is compared first, and when that is unsafe.** As today: before the
arguments only if the result type mentions none of them (`written_result`); after the arguments
(the after-expected path, and rule 1's step 3) in all other cases. Unsafe, and so not done:
- a result type that mentions an argument not yet checked: the comparison would solve the
  argument's unknown from the goal, a guess when the argument is a lambda or a term the goal
  only partly determines (Lean's `hasLooseBVars`, Agda's `freeInTgt`);
- an auto parameter in the rest (`written_result` returns `None`): its proposition may mention
  an argument, and finding it early fixes a dictionary from a guess;
- an expected type that is a bare unknown: nothing to learn, and the comparison would fix the
  call's type before its arguments;
- an effect row left bare in the result (D1124): compared by value type only, as `propagate`
  does;
- an expected type already computed (case 7): the comparison happens, but on unfolded sides; this
  is for folded expected types, not for order.

**What the queue's invariants need.**
- Invariant 3 (isolation): rule 1 runs inside the application; nothing it checks outlives it, and
  what its searches queue is resumed by the same W1.
- Invariant 4 (no re-entry): unchanged; a search checked last is not a queue item.
- Invariant 7 (defaults at quiescence): rule 1's step 4 finds instances, which is not a default
  (only instances whose types are fully known). Rule 4's closed patterns for `ring`/`omega` facts
  are a fourth place where a default runs early, beside W4, W2 and a `rewrite` rule: the restated
  invariant 7 (D2087) names "a closed pattern", so it is an instance, not a change, but the text
  should list it. The `calc` resume point applies no default.
- Invariant 8 (opaque placeholders): a search reads its goal only at step 5, after W1 has filled
  the application's placeholders; what is still a placeholder then falls under rule 2.
- Termination (§5.7, T1): rule 1 adds no attempt site; rule 2's waiting search is an existing kind
  of item (`WaitingTactic`).

### Expected changes

- **Examples** [run, prototype]: rules 1 (with `rfl`) and 4 together are not measured; separately:
  - rule 1 without `rfl`: one accepted example fails, `scan-layout.sw` (an `omega` argument of a
    `rewrite` rule, `List.getOrZipWithScanLeft … k omega`; the closing `rfl` then compares
    `List.getOr items k blank` with its unfolding and fails) [run, cause not established: the
    prototype unifies the placeholder with the checked term, where the queue would fill it and
    zonk the term, which may be the difference [inferred]];
  - rule 1 with `rfl`: also `float-playlist.sw` (through `std/Float/Theory.sw:1215`) and the better
    message of `partial-constructor-mismatch.sw`;
  - rule 4: the seven outputs of the D2118 table, each to be brought back by its rule.
- **AoC**: all 207 namespaces check with rule 1 (with `rfl`) and with rule 4 [run]; `stitchwort
  test` and `task audit` not run.
- **Hashes** [inferred, not measured]: rule 1 changes the term only where a search's proof differs
  once its goal is known (the cases above were failures); rule 4 changes a literal's type where an
  inferred literal was `Nat` and a later use says otherwise (only programs main rejects, N1), and
  terms where a waiting literal's placeholder is filled (an `Ann`, as in step 4.3's list). Expect a
  hash list of step 4.3's size, every statement identical.
- **Messages**: rule 1 moves a search's error to its goal as known (better); rule 4's seven.

### Risks

- **Rule 1 changes which proof a search finds.** A search that succeeded early with a guess now
  sees the real goal; where the guess happened to be what the proof needed, the search may now fail
  (no case found). Every accepted example and aoc checked [run]; `scan-layout.sw` is the one
  failure, not understood yet.
- **Rule 2 waits longer.** A search failing on an unknown that only a default settles is resumed
  after the default, so its error comes later, against the type now known: better, but a
  different message where today's shows `?N`.
- **Rule 4's closed unknowns** can't become `Fin n` for a local `n`; main can't either.
- **The `calc` resume point** is a new scope boundary, like W1; an item made in a step and resumed
  there sees only what the `calc` learnt (invariant 3 kept) [inferred].
- **Stage 5 is removing the retry paths at the same time.** Rule 1 assumes the after-expected path
  stays (§5.11, "kept"); if stage 5 changes it, rule 1's step 3 is where it moves.

### Step plan

Each step stops if an example's outcome or message changes beyond its list, or a hash beyond its
classified list (as stage 4's).
- **7.0, on main: the stale goal.** In the after-expected loop, read each argument's goal afresh
  (case 5). Test: `rflUnderHole` as an accept example (from `stage7/lambda-before-later.sw`).
- **7.1: rule 1** without `rfl`, as a step in `apply_args_postponing`; the placeholder filled
  through the queue's fill (invariant 2), not by unification; find `scan-layout.sw`'s cause first.
  Tests: `ext-cases.sw`, both `omega-before-later.sw` shapes as accept examples; a reject example
  whose search still fails, with the goal as known in its message.
- **7.2: `rfl` joins** (Q2), after `std/Float/Theory.sw:1215` is understood;
  `partial-constructor-mismatch.sw`'s message re-baselined.
- **7.3: rule 2** (Q3): `omega` and `ring` through `tactic_or_wait`, and any unsolved unknown;
  `lambda-before-later.sw`'s `lambdaFirst` as an accept example; counters as step 4.2's.
- **7.4: rule 4** (Q1): the three changes, then the four consumers, one commit each with its
  example's message back to main's (or the new one, for `sequence-in-let-value.sw`); `literal-tuples.sw`
  as an accept example; hashes classified; aoc tests, rogue and `task audit`.
- **Separately** (new tickets): folded expected types for case 7; stage 6's flex-flex pairs for
  case 6.

### Questions for Matt

**Q1 (D2118). Make inferred number literals wait, with their type and placeholder closed, a resume
point in `calc`, and the four consumer rules?** **[Recommend yes.]** The assumptions, in full:
- **(L1)** A numeral's possible types are `Nat`, `Int`, `Float`, `SafeNat`, `SafeInt` and `Fin n`;
  only `Fin n` can mention a variable, and an inferred literal can't be `Fin n` on main, so a
  closed type unknown loses nothing main has.
- **(L2)** A literal's value at a closed type is closed, so a closed placeholder is a faithful
  stand-in (invariant 2: its fill compares the same term).
- **(L3)** Nothing in `calc` between steps relies on a waiting literal staying unresolved; resuming
  the calc's own items there is a W1 for a construct that isn't an application.
- **(L4)** Main's behaviour is kept where nothing types the literal: the default is `Nat` (D2013),
  as main gives at once.
Alternative: leave inferred literals as they are and annotate (Day 17's workaround); Lean, Idris,
Haskell and Agda all make such numerals wait.

**Q2. Include `rfl` in rule 1?** **[Recommend yes, in its own step (7.2), once
`std/Float/Theory.sw:1215` is understood.]** It has SW-969's harm in the same form
(`partial-constructor-mismatch.sw`), and its message improves. Assumption: **(R1)** `rfl` against a
goal whose unknowns the call will fix is never better checked early: checked early it can only
solve them by equating its sides, which is the expected type's job. The alternative is to leave
`rfl` in place, where step 7.0 already fixes case 5.

**Q3. Widen the failed-search wait (rule 2) to `omega` and `ring`, and to any unsolved unknown?**
**[Recommend yes.]** It is what reaches searches inside lambdas (case 4), which rule 1 can't.
Assumptions: **(W1)** an unknown still unsolved at the end is an error anyway, so waiting on it
can't turn an accepted program into a stuck one, except where the search itself would have solved
it (step 4.0's M3 caveat: here that is exactly a search solving its goal's unknowns, the guess rule 1
removes); **(W2)** a search that succeeds at once is unchanged (only failure waits).

**Q4. Keep today's expected-type propagation (before the first argument, and after the arguments
on the after-expected path), rather than Lean's and Agda's comparison before every argument?**
**[Recommend yes.]** The prototype of Lean's rule fixed none of the cases and broke nine accepted
examples [run]. Revisit if a case needs the expected type between two non-search arguments.

**Q5. Open two tickets for what isn't order: (a) the body's expected type kept folded, so a `_`
meets `List.Any ?p xs` against `List.Any f xs` by arguments (case 7, SW-771 item 2, likely SW-976
(3)); (b) stage 6's waiting for a flex-flex pair instead of equating the unknowns (case 6,
SW-967 (3))?** **[Recommend yes, both to backlog.]**

## As built (stage 7)

Built on main (`5889a19d`) in the SW-1010 lane, 1 November 2026, after Matt's decisions: D2126
(inferred literals wait, with the design's three changes and its message rules), D2127 (rule 1,
`rfl` in its own step once `float-playlist.sw`'s break is understood), D2128 (a failed `omega` or
`ring` waits, on any unsolved unknown), D2129 (today's expected-type propagation stays), D2130 (case
6 and case 7 to backlog: SW-1009, SW-1008). Labels as in the design section above; "main" is
`5889a19d`'s binary.

| commit | step |
|---|---|
| `22eb08b4` | rule 1 without `rfl`; `scan-layout.sw`'s cause found and fixed |
| `a257d946` | rule 1's instance step scoped to the call's own obligations (`float-playlist.sw`'s cause) |
| `8aa6b9bd` | `rfl` joins rule 1 (SW-1007) |
| `07fcfaaf` | rule 2, part (a): `omega` and `ring` wait as `rewrite` and `cases` do; part (b) stopped |
| `c0598541` | rule 4: inferred literals wait (D2126), with the consumer rules |
| this commit | hash snapshots, this section |

**Rule 1** (`check::check_searches_last`) [run]. As designed: an explicit argument that is `omega`,
`cases`, `ring`, `rewrite` or the builtin `rfl` (not a local named `rfl`), bracketed or not, with
no later parameter's type depending on it, holds a placeholder (`hold_argument`, now also used by
the two older paths that held one), and after W1 the call's type is compared with the expected
type (`unify`, then `unify_solving_arguments`, a failure left for the call's own comparison), the
call's own ready instances are found, W1 runs again, and each search runs in written order against
its goal read afresh (`quote_folded`, then `eval`). The search's term fills its place as the
after-expected path's does (unification with the placeholder, then `fill_placeholder` in the
term), not through the queue's fill: the design's guess that the fill was `scan-layout.sw`'s cause
was wrong (below), and nothing needed the queue's. Two things the design didn't have, each found
from a break:
- **`scan-layout.sw`** (the prototype's break). The `+` of `(offset item => offset + item.size)`,
  inside the `rewrite` rule `List.foldLeftTakeSucc … k omega`, was found by rule 1's instance step,
  inside the application. The rule's own settle (`settle_rule`) then found nothing, returned
  `false`, and `rewrite.rs` read the rule's type afresh only when it returns `true`: the type,
  computed while the dictionary was unknown, stayed `Add.%add [Nat] Nat.instAdd …` as a stuck value
  (quoted, it printed as solved), and the closing `rfl` failed on two sides that print the same.
  Evidence: the `rfl` error's two terms, dumped, differ only in `Add.%add [Nat] Nat.instAdd x y`
  against `Nat.add x y`; with the instance step switched off the file checks. Fix: the
  application's type is read afresh when the instance step found any.
- **`float-playlist.sw`**, through `std/Float/Theory.sw:1215` (`unitsRoundNonpos`, the prototype's
  break with `rfl`): not about `rfl`. The prototype's instance step found every ready obligation of
  the declaration, so in `Eq.cong (x => x + 9223372036854775808) (magnitudeExact (Succ k) rfl hm)`
  it found the `+` of the *outer* call's lambda while that lambda's literal still waited for the
  outer call's W1. The outer call's type `f a = f b` then computed through `Nat.add` to a value
  stuck on the literal's placeholder (`Succ (k + ?5)`), which isn't computed again once the literal
  is filled, and no longer matched the expected type. Reduced: `Eq.trans (…) (Eq.cong (x => x + 5)
  (cappedExact (Succ k) (omega) hm))` fails the same way with `omega` held ("this has type `capped
  (Succ k) + 5 = k + 5 + 1`": the `5` not computed into the `+ 1`), so the first rule-1 commit had
  the bug too. Fix: the step finds only the obligations made since the application began, as W1
  resumes only its own checks (invariant 3). The design named `solve_ready_instances`; scoped is
  what its own invariant-3 paragraph says rule 1 keeps.

`rfl` then joins with no other change. SW-1007 (`startsOf _ 3 rfl` against `Starts [3, 4] 3`,
"`firstOf [3, 4]` and `Some 3` aren't equal" on main) checks, so step 7.0's separate fix to the
after-expected loop wasn't made; an argument kept for after the expected type that isn't a search
(a lambda) is still checked against its goal as computed when it was put off.

**Rule 2** [run]. Part (a) is built: `omega` and `ring` go through `queue::tactic_or_wait`, so one
that fails while its goal holds an unknown of `search_pending` waits for it, whole, and runs again
on the goal now known (`WaitingTactic` shows them as `(omega …)`, `(ring …)`). Inside a split of a
`cases` they run as before, as `cases` does there: the split goes on splitting only where an
alternative fails, so a wait there would stop it. In aoc this changes nothing (`tactic waited` 1,
`omega failed on pending` 0); `omega-waits.sw` shows it.

**Part (b), "any unsolved unknown", is not built (D2140, Matt, 1 November 2026: stage 7 keeps
part (a) only; part (b) is SW-1014, a rework so that the after-expected comparison doesn't depend
on a failure).** Built (every unsolved
unknown in the zonked goal, any of which wakes the item), it fixes case 4 (`lambdaFirst`) and turns
`reject/lambda-after-expected-unfolded.sw` into an accepted program, but breaks the library and
aoc: `std/List/Grid.sw:52` (`E-UNSOLVED`), `std/Parse/Reads.sw` (4 sites, `E-TYPE-MISMATCH`), so
every namespace using them, and 9 sites in 7 aoc proof files (2021 days 8, 12, 16, 18; 2024 days 4
(two files) and 7). The cause, traced at `Grid.sw:52` (`Both (rewrite <- rowSame in …) …` inside
two lambdas given to `List.anyElim`): the `rewrite`'s goal is a bare unknown `?48 …`, an ordinary
one, not the queue's. On main the `rewrite` fails, the failure makes both lambdas fail in place,
and the after-expected path checks them again once the call's type is compared with its goal,
which is what solves `?48` (trace: two "after-expected" lambdas at the spans of the two lambdas,
and the `rewrite` failing with no blocker, then succeeding). With (b) the `rewrite` waits on `?48`
instead, the lambdas succeed in place, the after-expected path never runs, and nothing solves
`?48`. So the design's assumption W1 ("an unknown still unsolved at the end is an error anyway, so
waiting on it can't turn an accepted program into a stuck one") doesn't hold: the failure itself is
what makes the call compare its type with the goal by `unify_solving_arguments`. The options
that were put to Matt (D2140 chose (i) now, and (iii) as SW-1014):
- **(i) keep (a) only** (built): case 4 stays open (it is in a `let`, where nothing is expected and
  there is no after-expected path);
- **(ii) (b) only where no after-expected attempt encloses the search**: a flag set while an
  argument is checked in place with an after-expected retry possible; there a search waits only on
  the queue's unknowns, as now. Case 4 would check; the lambda-after-expected example would stay
  rejected. One more piece of state the queue has to restore [inferred];
- **(iii) make the after-expected path not depend on failure**: an argument whose check queued a
  search waiting on an ordinary unknown counts as failed in place. Larger, and it re-runs the
  argument [inferred].

**Rule 4: inferred literals wait** (D2126) [run]. `infer` of a number literal checks it against a
new type unknown made with no variables (`new_meta`), so it waits (K4). With the design's other
two changes, a literal whose type mentions no variable has a closed placeholder (`queue`), and
`calc` resumes its own checks after each step's right side (`resume_from`, no defaults). The
consumer rules, each bringing its output back to main's:
- `W-NO-EFFECT`: a waiting literal is pure (`no_effect::check_value`, through
  `queue::waiting_literal`): `sequence-expression.sw`, `abilities-edge.sw` and
  `sequence-in-let-value.sw` keep their warnings;
- an `omega` or `ring` fact is a closed pattern, settled as a `rewrite` rule is
  (`Elaborator::settled_fact`; invariant 7's list in `queue.rs` names it):
  `ring-coefficient-after.sw` says "this is `Nat`" again;
- `++` on an unknown type is a queued check (`check::Append`), resumed when the type is known and
  reported, if still unknown at the end, with main's message: `append-numbers.sw` again says "this
  is a `Nat`", after the `1`'s default;
- a numeral where a type is expected is `E-NOT-A-TYPE` at once (`check_type`), and a numeral given
  arguments is a `Nat` head (`infer_app_with`): `tuple-value-for-type.sw` and
  `unfold-of-failed-definition.sw` as on main.

One more, not in the design's table: a `calc` step's message printed the start term as the
literal's placeholder, filled but not written in ("the line says `?1 = List.sum xs`",
`calc-pipe-step-proof.sw`). `calc.rs`'s `written` now zonks the term first.

**Examples** [run: every accept, reject, soundness, goals and extract file and every project,
`check` output and exit code, against main's]:

| example | change | why |
|---|---|---|
| `reject/partial-constructor-mismatch.sw` | `Eq.cong (Call o) rfl` against `Call o f = Call o g`: "`f` and `g` aren't equal" at the `rfl` (`E-REFL`), where main said "expected `Call o f = Call o g`, but this has type `Call o f = Call o f`" | `rfl` checked early made `g` be `f` (the design's expected change). The file gains `callCongSame`, a proof of the wrong equation, which keeps SW-410's mismatch of two partly applied constructor calls (`E-TYPE-MISMATCH`, main's message) |
| `reject/sequence-in-let-value.sw` | error at the `1` (8:30), "expected `Text`, but this has type `Nat`", note "a numeral can only be the prelude's `Nat` or `Int`"; main blamed `x` (8:36) | `x`'s type is fixed by `Text` before the literal resumes: the design's accepted new place. Its comment now says so |
| `accept/searches-after-call.sw` (new) | checks; main rejects | cases 1, 2, 3 (SW-969, SW-971), and `outerLambda`, the reduced `Theory.sw:1215` shape |
| `accept/rfl-after-call.sw` (new) | checks; main rejects | case 5, SW-1007 |
| `accept/omega-waits.sw` (new) | checks; main rejects ("unsupported structure") | rule 2 (a) |
| `accept/literal-tuples.sw` (new) | checks, its test passes; main rejects `-4` | case 8 (D2118), with the let-pattern and `calc` shapes the two fixes are for |
| `reject/search-after-call-false.sw` (new) | `omega`'s message shows `x.snd`; main's shows `?2 counts given x` | a search still failing, with the goal as known |

Every other output is byte-identical to main's. `accept/argument-order-expected.sw` is kept (its
forms are the theorem-body ones, which still go through the after-expected path); its header now
says which twins check.

**The cases** [run]: 1, 2, 3, 5 and 8 check; 4 is open until SW-1014 (rule 2 (b)); 6 and 7 are
SW-1009 and SW-1008; 9 was not reproduced.

**Hashes** [run]: `hash_stability`'s prelude snapshot (std and the core) is unchanged. Three
example snapshots change, each with the statement unchanged:
- `project-trip-journal`: `Trip.Proofs.inCombined` (and its four `%match` helpers),
  `keptFromCombined` (and its helper), and `photoIdsKept`, which uses both. Cause: rule 1 on their
  `rewrite` arguments (`(rewrite e in keptWhereOwned …)`, `(rewrite found in …)`): checked last,
  their proofs are built against the goal as the call fixed it. Evidence: with `rewrite` taken out
  of rule 1, `inCombined`'s hashes are main's again;
- `let-patterns` (`test "in a test"`, `let (a, b) := (1, 2); a + b == 3`) and
  `shared-field-update` (`test "pair"`, `{ (1, "x") | fst = 2 } == (2, "x")`): literals inferred
  inside tuples now wait. Dumped terms: main's `Nat.add a b` (the pattern's variables) is
  `Nat.add 1 2`, and the update applied to its `let` variable is applied to `2`: the uses are
  written as the waiting literals' values, filled in, where main had the variables; the values are
  the same. Which code writes the value rather than the variable was not traced [inferred: the
  checks that waited for the literals' type are completed from values];
- four new snapshots for the new accept examples.

**Counters** (aoc, `check --no-cache`) [run]: 1,244 queued, 1,079 resumed, 64 defaulted, 0 stuck;
`retried` 0 (stage 5 counted 1, 2021 Day17's tuple list, which waits now); `tactic waited` 1;
`leaf uninferred` 4. `check::retrying` still fires once each in `reject/decreasing-lambda-in-data.sw`
(where its second run gives the intended `E-DECREASING`) and `accept/lambda-propagated-alias.sw`
(no effect), so `retrying` and `late_literals` stay: the lambda gap of stage 5 remains.

**Time**: aoc `check --no-cache`, one pair: this lane 61.3 s user (63.3 s wall, load 7), main
67.5 s user (86.0 s wall, load 16). No slowdown.

**Gates** [run]: lane tiers `elab` and `examples` after each step; `task test:one` on `no_effect`
and `guide`; `check --no-cache` over aoc (207 namespaces) and rogue (3); `task audit` (std 2,487,
aoc 2,113, rogue 190: all passed, no warnings); the `hashes` lane tier, snapshots regenerated
(`task snap:hashes`); `cargo clippy --workspace --all-targets -D warnings`; `cargo fmt`.

**Search patterns and `rewrite` rules** (after the first merge attempt, which the merge tier
stopped) [run]. With `++` waiting, the search pattern `_ ++ _ = _` as written elaborated, its `++`
a placeholder no default fills, and was searched as a third reading beside the list and text ones
(`search_match`'s `an_append_of_holes_is_tried_as_lists_and_as_texts`, `search`'s
`the_query_log_gets_a_line_per_search`). Now a pattern whose own checks still wait once settled
doesn't elaborate (`Elaborator::pattern_stuck`, in `search.rs`), as on main, where the `++` failed
at once. One more change from it: `_.length = _`, whose `.length` waits on a receiver nothing
types, is now that check's `E-CANNOT-INFER`; main searched it with the placeholder as a hole and
listed `Eq.sym` first. And `List.length (_ ++ _) = _` as written now elaborates (its `++` waits
until `List.length` says lists), giving the same pattern as the list reading up to how its holes
are numbered; readings are now compared with their holes renumbered, so it is searched once, and
the test's elaborated pattern is `… = ?5` where it was `… = ?4` (the waiting `++` made an unknown
first). A `rewrite` rule whose side is headed by a waiting check's placeholder reports that check's
error rather than "starts with an unknown function" (`rewrite.rs`, `waiting_head`; new
`reject/rewrite-rule-append-holes.sw`), and a `++` whose operands' type stays unknown now says
"nothing here says whether this joins texts or lists" where main printed `?0 xs` (D2091). Waiting
literals in patterns are settled to their defaults as before (`settle_pattern`); `search --at`'s
goal benchmarks (`search_at_on_aoc_goals`) pass.

**Open**: rule 2 (b), SW-1014; step 7.0's afresh read for after-expected arguments that aren't
searches; the stage 5 lambda gap (a lambda checked against an unknown applied to variables), after
which `retrying` can go.

## Review 1 and how it was addressed

The review is [postponement/review-1.md](postponement/review-1.md): "approve with revisions".

| point | the review | what changed, and where |
|---|---|---|
| R1 kept receivers | make it a design invariant: keep an elaborated subterm only if it is stable under later information, else keep syntax and environment and re-elaborate | Invariant 6 (§5.1). §2 now describes how a dot call is elaborated: the prefix form already undoes the receiver and re-elaborates it from syntax. §5.5 gives the rule: syntax when the blocker predates the receiver (131 of 159), the term when the receiver made the blocker (28), with why each is stable. Measured: identical outcomes and hashes (§6.7). Must-hold tests in §9 |
| R2 termination | "per surviving attempt" isn't a global bound; item states; no nested resume of a running item; finite-choice attempts; a lexicographic measure; keep the budget | Item states (§5.2), invariant 4. §5.7 rewritten: T1 classifies every attempt site, with file:line; T2 names the three sites that rerun the same alternative in the same state (bounded, two removed by stage 5); T3 no re-entry; T4 the measure (occurrences unfinished, K2 view steps, obligations and rows, inside a finite attempt tree). The budget stays, as a resource limit on condition T1 holds for new sites. Draft 2's "the ladder takes no snapshot" corrected |
| R3 scoped W1 | non-negotiable; an isolation rule | Invariant 3 in the review's words (§5.1); §5.6 "Isolation" with the evidence; D2014 records the reviewer's agreement |
| R4 W1 and delayed unification | W1 is not a complete substitute; plan tri-state unification; don't block the queue on it | §5.13 rewritten; stage 6 is now the expected follow-up with a trigger counted from stage 1 (§8); D2014's S4 |
| R5 default order | field-name first, then `Nat`; revisit only if record inference checks fields against candidates | §5.8 and D2013 record the agreement and the condition |
| R6 errors | a resumed item's new error against the known type at its span; several stuck items by independent root, about 3, downstream suppressed | §5.9 rewritten: dependency, roots, groups, at most 3, through `branch_errors`; stage 1; tests in §9. The resumed-item rule was already draft 2's, now with the review's reasoning |
| R7 opaque placeholders | no irreversible elaboration choice from an unfilled placeholder's shape (the `==` regression); compare Lean's synthetic opaque | Invariant 8. §5.10: the 15 consumers that choose from a type's shape, each classified as wait, decided at `finish` (the `==` fix: the known-instance projection at `finish`) or allowed (a wrong guess can only be a type error, a stated weakening). For unification, freezing was measured and breaks 1 example and 4 AoC proofs, so placeholders stay solvable until stage 6: D2016 |
| R8 queue invariants | a short section of eight | §5.1, the review's eight with 2 and 8 made precise; §9 lists the tests of each |
| agreement: K3 | `x : ?D => x.f` is the right normalisation | Recorded in §5.4 |
| agreement: path 3 | keep the after-expected path separate | Recorded in §5.11 |
| agreement: staged rollout | sensible, each old path removed after its counter is 0 | Recorded in §8 |
| bottom line | do not ship on the termination claim as argued; settle the kept-receiver rule before K2 becomes infrastructure | §5.7 and §5.5; both are settled before stage 2, where K2 lands |

## Alternatives considered

**A second pass over failing declarations** (draft 1's D2010). A declaration that failed after a
queueable `E-CANNOT-INFER` was elaborated again with the queue on; if that failed too, the first
pass's error was reported. It guaranteed that no accepted program's terms changed. **Rejected**
under D2012:
- **The end-state criterion.** Its only advantage was identity of accepted programs, which is no
  longer a requirement. It left today's catch-and-retry paths in place, so it was a second
  mechanism beside them, not one.
- **Two code paths.** Every queueable site would have two behaviours, chosen by a flag, and
  every postponement bug would have to be looked for in both.
- **Double elaboration.** A failing declaration was elaborated twice, which costs most in the
  language server, where code is often broken.
- The prototype also shows its premise was pessimistic: the single pass changes 2 files' outcome
  and 26 hashes, not the 1,073 routes the raise count suggested.

**Only the end of the declaration as a resume point** (Lean's definition-level ladder alone):
std doesn't load ([§6.5](#65-variants)), because the unifier can't wait (D2014's S1).

**The field-name rule at the literal** (Agda's order): breaks `held`'s tests unless `held` stays
(§5.8, D2013).

**A body-first `let`** for SW-847 (Lean's `let_delayed`): rejected in draft 1 (D2011) because it
hides the whole value from the body. The queued field access does what SW-847 needs.

**Queueing whole lambdas** (Agda's `CheckLambda`): unnecessary once their pieces wait, and it
would keep a lambda's body from being checked in place, which is where most of its information
is. The prototype's 9 remaining lambda postponements are 6 sections and 3 reject examples.

**Always keeping a `.field`'s receiver as a term** (Agda; draft 2): see §5.5. **Always keeping it
as syntax** (Lean's restore): leaves 28 of 159 items with no blocker to wait on.

**Frozen placeholders now** (Lean's synthetic opaque, without its waiting unifier): breaks 1
example and 4 AoC proofs (D2016).

## Sources

Fetched 30 October 2026 with `gh api` into the lane's scratch directory, read as text. Line
numbers are of those copies. WebSearch was not used. Draft 3 made one more `gh api` call, for
[L2] at line 1458.

**Lean 4**, `leanprover/lean4` at `0f852cc822d54d32c5cb0ef158562796088ce4dc` (as in
docs/research/elaboration.md):
- [L1] `src/Lean/Elab/SyntheticMVars.lean`, whole file (743 lines); draft 2 also cites
  `synthesizeUsingDefault` (237-243) and `withSynthesizeImp` / `withSynthesizeLightImp`
  (689-720);
- [L2] `src/Lean/Elab/Term/TermElabM.lean`: `SavedContext`, `SyntheticMVarKind`, `Context`,
  `tryPostpone*`, `saveContext`, `postponeElabTermCore` (the `syntheticOpaque` placeholder at
  1458, re-fetched for draft 3), `postponeElabTerm`, `elabUsingElabFnsAux`, `elabTermAux`
  (lines 40-120, 300-315, 860-875, 1365-1470, 1650-1710, 1940-1970);
- [L3] `src/Lean/Elab/App.lean`: `synthesizePendingAndNormalizeFunType` (360-380), `ElabElim`
  argument loop (1290-1320), `resolveLValLoop` (1670-1700), overload filtering (2170-2210);
- [L4] `src/Lean/Elab/Binders.lean`: `elabFun` (678), `elabLetDeclAux` (735-860),
  `let_delayed` (951-952);
- [L5] `src/Lean/Elab/MutualDef.lean`: lines 262-275, 1395-1406;
- [L6] `src/Lean/Elab/StructInst.lean`: lines 1355-1366 (by grep for `postpone`);
- [L7] `src/Init/Prelude.lean`: `instOfNatNat` and its `@[default_instance 100]` (1400-1413).

Fetched 1 November 2026 for stage 7, at the same commit:
- [L8] `src/Lean/Elab/BuiltinTerm.lean`: `elabByTactic` (178-187), `mkLitTypeFor` and
  `elabNumLit` (208-232);
- [L9] `src/Init/Data/Int/Basic.lean`: `instNegInt` and its `@[default_instance mid]` (120-135);
- [L10] `src/Lean/Elab/App.lean`, whole file (2,332 lines): `etaArgs` (199-206, 731-738),
  `getResultingTypeCore?` (449-502), `shouldPropagateExpectedTypeFor` (516-523),
  `propagateExpectedType` (525-608), `finalize` (610-657);
- [L11] `src/Lean/Meta/ExprDefEq.lean`: first-order approximation (900-925, 1366-1395);
- [L1] and [L2] again for `synthesizeSyntheticMVars`' tactic step (590-598, 661-667) and
  `mkTacticMVar` (1474-1482).

**Agda**, `agda/agda` at `df8c38856ecce561ef8fd0834755c46a6d397a0a`:
- [A1] `src/full/Agda/TypeChecking/Monad/Base.hs`: `ProblemConstraint`, `Constraint`
  (1655-1712), `MetaInstantiation` (1990-1994), `TypeCheckingProblem` (2058-2086);
- [A2] `src/full/Agda/TypeChecking/MetaVars.hs`: `postponeTypeCheckingProblem_`,
  `postponeTypeCheckingProblem`, `problemType` (614-671);
- [A3] `src/full/Agda/TypeChecking/Constraints.hs`, whole file (389 lines), re-fetched for
  draft 2 (`wakeupConstraints`, 246-251);
- [A4] `src/full/Agda/TypeChecking/Rules/Term.hs`: every `postponeTypeCheckingProblem` site
  with its function (565-640, 790-880, 940-960, 1111-1275, 1425-1446, 1528);
- [A5] `src/full/Agda/TypeChecking/Rules/Application.hs`: 1000-1012, 1385-1476;
- [A6] `src/full/Agda/TypeChecking/Rules/Decl.hs`: `checkDecl`'s tail (146, 205-250);
- [A7] `src/full/Agda/TypeChecking/Records.hs`: `findPossibleRecords` (214-236);
- [A8] `src/full/Agda/TypeChecking/Pretty/Warning.hs` (100-116, 925-1005) and
  `Pretty/Constraint.hs` (40-120);
- for stage 7, fetched 1 November 2026 at the same commit: [A5] again, whole file (the target
  check, 700-800), and [A4] again (`checkLambda`'s postponement and its "hazardous" comment,
  575-606; `checkPostponedLambda`, 795-810; `unquoteTactic`, 1539-1557).

**Idris 2**, `idris-lang/Idris2` at `c35a6bd16ca2adea9484c64507bfc2041ceec75a`:
- [I1] `src/TTImp/Elab/Delayed.idr`, whole file (319 lines);
- [I2] `src/Core/UnifyState.idr`: `DelayReason`, `UState` (45-110);
- [I3] `src/TTImp/Elab.idr`: `elabTermSub` (85-175);
- [I4] `src/TTImp/Elab/Record.idr`: `checkUpdate` (240-260);
- [I5] `src/Idris/Desugar.idr`: integer literals (434-442), fetched 1 November 2026 for stage 7,
  as [I6] and [I7];
- [I6] `libs/prelude/Prelude/Num.idr`: `%defaulthint defaultInteger` (99-104);
- [I7] `src/TTImp/Elab/App.idr`, whole file (881 lines): `needsDelayExpr` (297-316),
  `checkRestApp` (411-455).

**Runs** for stage 7 (1 November 2026, nixpkgs builds): Lean 4.34.1, Idris 2 0.8.0, GHC 9.10.3,
Agda 2.8.0 (`--no-libraries`); files and output in [postponement/stage7/](postponement/stage7/).

**Rocq**, `rocq-prover/rocq` at `3fb9a904fc271e9fbe15f3bdcfdc13e008ed8794`:
- [R1] `pretyping/pretyping.ml`: bidirectionality hints (56-70), `solve_remaining_evars_from`
  and the checks (300-462), application pretyping (1050-1215);
- [R2] `pretyping/evarconv.ml`: `flex_rigid`'s comment (900-920), 985-1015, 2040-2165;
- [R3] `engine/evd.ml`: `conv_pbs`, `add_conv_pb` (496, 924-928, 971-983);
- [R4] `interp/constrintern.ml`: `sort_fields` (1563-1600).

**OmniML**:
- [O1] O'Brien, Rémy, Scherer, *Omnidirectional type inference for ML: principality any way*,
  arXiv 2511.10343v2, PDF via `pdftotext`. Read: §2.1, §2.4, §2.5, §3.2, §4.1 opening, §6, §7.

**Not verified**: which unification problems Rocq's `evarsolve.ml` and `cases.ml` postpone; the
Idris `delayOnFailure` users other than records; Lean's anonymous-constructor elaborator; that
Lean's `isDefEq` never assigns a synthetic-opaque metavariable (from its documentation, not read
in source).

**Stitchwort**, at `3d0036f8` (crates unchanged since `fcb12746`): `crates/elab/src/check.rs`
(`Ctx`, `apply_args_postponing`, `retrying`, `fill_placeholder`, `append_tried`, `insert`,
`compare`, `function_parts`, `check_type`), `records.rs` (`FieldNames`, `held`, `last_resort`,
`infer_literal`, `check_record`), `dot.rs` (`infer_dot`, `infer_receiver`, `find_in_view`,
`prefix_form`, `infer_call`, `receiver_type`, `mark_failed`), `calc.rs`, `numbers.rs`
(`Defaulted`, `check_literal`, `group_in`, `operator`, `equation`), `interfaces.rs`
(`method_call`, `decide_eq_of`, `solve_tree`, `find_ready_dictionaries`), `bind.rs`
(`decide`), `logic.rs` (`condition`), `membership.rs` (`container_kind`), `effects.rs`
(`receiver_passed`, `is_comp_type`, `may_perform_at`), `auto.rs`, `lib.rs` (`finish`,
`clear_metas`, `with_local_retries`, `branch_errors`, the total-row retype, zonk errors),
`lift.rs` (`lift`, `lifted_calls`), `goals.rs`, `undo.rs`, `rewind.rs`, `unify.rs` (header,
`run`, frozen metavariables, `lifted_call`), every `Snapshot::take`, `transaction`, `attempt`
and `undo::unify` site, `crates/core/src/globals.rs` (`frozen_metas`, `lifted_calls`),
`crates/cli/src/lsp.rs`, `crates/driver/tests/hash_stability.rs`; docs/testing.md (the
elaborator fuzzer); docs/research/elaboration.md §8; docs/syntax.md (records, method sections).
