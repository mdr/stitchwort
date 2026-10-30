# Proposal: one postponement queue in the elaborator

**Status:** draft 3, 30 October 2026; **stages 1 and 2 are built** ([As built (stage
1)](#as-built-stage-1), [As built (stage 2)](#as-built-stage-2)). Tickets SW-817 (anchor), SW-847 and SW-885; context
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
   elaboration can't change with what is learnt later; otherwise it keeps the syntax and its
   context and elaborates it again when resumed. For a queued `.field`, the receiver is kept as
   syntax unless the blocker was made inside it ([§5.5](#55-the-receiver-of-a-queued-field-r1)).
7. **Defaults at quiescence only.** A default is applied only when resuming, obligations and row
   comparisons have all stopped making progress (ladder step 3, at W4). Effect rows are among
   the row comparisons.
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
  literals (`Nat` at once, `numbers.rs:290-312`), operator dictionaries (specialised only if
  found at once, `interfaces.rs:1490-1521`, `:1705-1738`), the `if` condition's reading
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
    assertion checks that no such choice was made inside a receiver kept as a term (the
    counters above are 0 today);
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
- **allowed** (the `if` reading, `in`'s container, `Type`, a function's shape): these are
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
  definition stays generic, as before.

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
  release.
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
   record; that moves to the ladder with K4.
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
  `Pretty/Constraint.hs` (40-120).

**Idris 2**, `idris-lang/Idris2` at `c35a6bd16ca2adea9484c64507bfc2041ceec75a`:
- [I1] `src/TTImp/Elab/Delayed.idr`, whole file (319 lines);
- [I2] `src/Core/UnifyState.idr`: `DelayReason`, `UState` (45-110);
- [I3] `src/TTImp/Elab.idr`: `elabTermSub` (85-175);
- [I4] `src/TTImp/Elab/Record.idr`: `checkUpdate` (240-260).

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
