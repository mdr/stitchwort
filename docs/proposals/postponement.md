# Proposal: one postponement queue in the elaborator

**Status:** draft 2, 30 October 2026. Tickets SW-817 (anchor), SW-847 and SW-885; context
SW-509, SW-805, SW-896. Follows D1990 (one queue, agreed in principle), D1991 (SW-805's
field-name rule stays, as name resolution) and D2012 (Matt: design for the best end state; the
cost of churn is not a criterion). Repros, measurements and the prototype's outputs are in
[postponement/](postponement/). Two decisions for Matt are in [§10](#10-decisions-for-matt). An
external reviewer's brief, self-contained, is [postponement/review-brief.md](postponement/review-brief.md).

**What changed from draft 1.** Draft 1 proposed the queue only as a second pass over
declarations that fail (its D2010), because a single pass would change how accepted code
elaborates. D2012 makes that churn acceptable, so the target is now **one queue, used in the one
elaboration pass**, as in Lean, Agda and Idris. Today's lambda and method-section postponement,
record literals, `.field` on an unknown type and effectful parts all become instances of it, and
today's catch-and-retry paths go away. The second pass is now under
[alternatives considered](#alternatives-considered). A prototype of the single queue, behind an
environment variable, was run over std, every example, aoc and rogue
([§6](#6-what-the-single-queue-changes-today)); its findings drive the design and the stage plan.
D2011 (SW-847 by a queued field access, not a body-first `let`) still fits and is kept
([§5.10](#510-let-and-sw-847-d2011-kept)).

Labels, as in the other notes:

- **[checked: file:line]**: read in the Stitchwort source at `fcb12746` (main, 30 October);
- **[run]**: run on 30 October with `target/release/stitchwort` built from `fcb12746` plus the
  prototype, with the switch off (today's behaviour) unless the line says it was on;
- **[measured]**: the prototype's measurement harness of [§6](#6-what-the-single-queue-changes-today)
  or draft 1's counters ([§4](#4-p1-how-often-postponement-is-needed));
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
  raises today ([§5](#5-the-design)).
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
- **Two design facts the prototype found**, which draft 1 didn't have:
  - the queue must be drained at the end of each application, not only at the end of the
    declaration, or std fails at `Map/Spec.sw:1862`. The reason is that Stitchwort's unifier
    can't wait on a placeholder. Scoped to the application's own items, as Lean's
    `withSynthesize` is, it changes no reject example (D2014);
  - it must also be drained before lifting, or a queued literal holding a `match` breaks aoc.
- **SW-805's rule becomes a default** in the ladder. It still looks only at the field names and
  the names in scope (D1991's R1 holds). That subsumes its `held`/`last_resort` machinery
  (its 5 reruns fall to 0), and it means number literals must be defaulted in the same ladder
  at a lower priority, as Lean's `OfNat Nat` default instance is (D2013).
- **The catch-and-retry paths shrink at once**: the lambda try-then-postpone fires 9 times
  instead of 100. The 6 left in accepted code are method sections, the next kind to queue.
- **Stage plan** ([§8](#8-stage-plan)): the queue and its resume points; record literals and
  `.field`; sections; numbers and the defaults ladder; then removing the retry paths, each
  stage gated on every test, example, AoC answer and rogue test staying right. Hashes may
  change.

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
and all four SW-885 functions run under `Parse.run` to the number they parse **[run]**.

## 2. Stitchwort today

**Argument postponement** (`check.rs:1970-2250`) **[checked]**:
- A lambda argument whose domain is unknown, with a later explicit argument, is tried in place
  under a `Snapshot`. If that fails, it is restored and checked after the later arguments.
- A method section is postponed without a try, unless a later parameter's type depends on it.
- A lambda that fails where the application's expected type is known (`late_able`), and a
  non-lambda argument that fails while its type has unknowns, are checked again after the
  application's type is compared with the expected type (`after_expected`).
- Under `retrying` (`check.rs:1941`), a failed application is elaborated a second time with
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
| `retrying` with `late_literals` | `check.rs:1941` | any non-fatal error | 19 |
| SW-805's `held` / `last_resort` | `records.rs:690-745`, used by `==` and comparisons (`numbers.rs:754`, `:1125`), `++` (`check.rs:3599`), `calc` (`calc.rs:95`, `:113`) | `E-CANNOT-INFER` after a held literal | 5 reruns |
| infer one side, on `E-CANNOT-INFER` infer the other | `append_tried` (`check.rs:3603-3611`), `calc` (`calc.rs:117-121`), `numbers.rs:1135` | `E-CANNOT-INFER` | (inside the above) |

The counts are firings of each path with the switch off, from counters the prototype adds
([§11](#11-the-prototype)). Only the first and last two rows are about `E-CANNOT-INFER`; the
after-expected rows are mostly `E-OMEGA`, `E-REWRITE-NOTHING` and `E-TYPE-MISMATCH`, proofs
found from a goal that only the expected type fixes.

**Where `E-CANNOT-INFER` is raised for the constructs in the tickets** **[checked]**:
- a record literal inferred, or checked against an unknown after SW-805's rule finds no single
  type (`records.rs`, `infer_literal` and `check_record`);
- `.field` on a receiver whose type is unknown (`dot.rs`, `find_in_view`, `Step::Unknown`);
- a method section whose argument type is unknown (`dot.rs`, `section_unknown_name`).

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

**Other declaration-level waiting** **[checked]**:
- obligations (instances) wait and are retried in rounds (`solve_obligations_until_stuck`,
  `auto.rs:100`);
- row comparisons that can't be decided are kept with their context and retried in that loop
  (`rows.rs`, `retry_rows`);
- `finish` (`lib.rs:1092`) compares awaited helpers, runs that loop, settles rows and zonks;
- `Snapshot` (`undo.rs`) records the length of each per-declaration table, and `restore`
  truncates them;
- `with_local_retries` (`lib.rs:2270`) re-runs a failing declaration body after admitting
  local definitions.

## 3. How other systems do it

Every row comes from source files fetched with `gh api` on 30 October 2026, or from the
OmniML paper's full text. Commits and URLs are under [Sources](#sources).

| | What is postponed | Where it lives | When resumed, in what order, how it stops | Still stuck at the end | Errors |
|---|---|---|---|---|---|
| **Lean 4** | Any term elaborator that calls `tryPostpone…`: structure instances, `.field` on an unknown type, anonymous constructors, `elab_as_elim` minor premises. Not `fun`. | A synthetic metavariable of kind `.postponed (SavedContext)`, listed in `pendingMVars`. The local context is the metavariable's own. | `synthesizeSyntheticMVars`: steps in creation order while one makes progress. Then, in order, retry with postponing off (errors postponed), default instances (by priority, numerals' `OfNat Nat` at low priority), retry with postponing off (errors reported), tactics. Runs at the end of each definition and at nested `withSynthesize` points, which handle only what was created inside them. | Can't stay stuck. The last retry runs with postponing off, so the elaborator commits or fails. For `.postponed`, `reportStuckSyntheticMVar` is `unreachable!`. | Logged at the postponed syntax (`withRef stx`), against the metavariable's type as now known. The term becomes `sorry` and elaboration goes on. |
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
   ([§5.3](#53-resume-points-order-and-termination)). The prototype shows this is enough.
4. **From Agda: keep what was elaborated.** A queued `.field` keeps its receiver's term and
   type (`CheckProjAppToKnownPrincipalArg`), and a queued literal waits before checking any
   field, so neither needs Lean's restore when it is queued.
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

### 5.1 What is queued

A **queued check** has:
- what to elaborate, one of the kinds below, with what it already elaborated;
- its **blocker**: the unknown at the head of the type it needs;
- the saved context: the whole `Ctx` except the elaborator, cloned (the prototype's
  `Ctx::save`, `check.rs`);
- a **placeholder** unknown standing for its result in the term built so far;
- the error its site raises today, for when it stays stuck;
- its span.

| kind | created where today raises or retries | blocker | resumed as | prototype |
|---|---|---|---|---|
| K1 record literal | `check_record` at an unknown, and `infer_literal` (with a fresh type unknown) | the expected type's head | `check_record` at the type now known | yes |
| K2 `.field` or dot call | `find_in_view` meets `Step::Unknown`; the receiver's term and type are kept | the unknown that step met (a later step may block again) | the lookup and call from there, with the kept receiver | yes |
| K3 method section | `section_unknown_name`; and today's section postponed without a try | the section's parameter type | a lambda over `x : ?D` whose body is K2 on `?D` | no |
| K4 number literal | a literal checked against an unknown, today defaulted to `Nat` at once | the expected type | the literal at the type now known; default `Nat` | no |

Not queued:
- **a lambda as a whole.** A lambda is always checked in place; what inside it needs its
  parameter's type is queued (K1-K4). This is what removes the lambda try-then-postpone
  ([§5.7](#57-removing-the-catch-and-retry-paths)). Lean does the same (`fun` is never
  postponed); Agda postpones some lambdas, and calls committing early "hazardous" for implicit
  lambdas, which Stitchwort doesn't have.
- **an effectful part (SW-885).** None is needed: the effect pass already binds the part and
  infers a pure literal, which is a K1 ([§2](#2-stitchwort-today)). Draft 1's stage 0 and Q4 are
  dropped.
- **a unification pair** ([§5.9](#59-the-unifiers-put-aside-pairs)).
- other `E-CANNOT-INFER` sites (`rfl`, `J`, quotients). They don't need a type's shape from
  later; they need an annotation.

### 5.2 Where the queue lives, and how items wait

**Per declaration**, as a table on the `Elaborator` beside `obligations` and
`row_constraints`, **indexed by blocker**:
- `clear_metas` clears it, `rewind` clears it;
- `Snapshot` records two lengths, of the items and of the **resumption log** (which items have
  been resumed, in order), and `restore` truncates both. So an attempt undone takes back both
  the items it queued and the resumptions it made: an item resumed inside an attempt that fails
  is waiting again afterwards. The prototype needed this (an item resumed and then undone was
  otherwise lost) **[run]**;
- a map from blocker to items lets a resume point look only at items whose blocker was solved
  since the last point (`Globals::meta_trail` lists solved unknowns in order, as
  `Snapshot::solved_since` already reads it). The prototype scans the whole queue instead.

**Why per declaration and not per unknown alone.** Metavariables, obligations, rows and
snapshots are all per declaration in Stitchwort, and a declaration's unknowns never outlive it
(`finish` zonks them). Agda's and OmniML's wait lists hang off each unknown in a store that
outlives declarations; here that store is the declaration. So items live in the declaration's
table and wait on an unknown, which is OmniML's wait list with Stitchwort's lifetime.

**Why not wake inside the unifier**, as Agda's `wakeupConstraints` does after an assignment:
`unify` is a function of `Globals` with no `Ctx` (`unify.rs:30`), called inside many of the 44 snapshot
sites that branch on its answer, and resuming an item elaborates syntax. Waking from inside it
would run elaboration in the middle of a comparison. Waking at the resume points below gives
the same order at fixed, safe places.

### 5.3 Resume points, order and termination

**Resume points.** The ladder below runs, scoped as in Lean's `withSynthesize`, at:
- **W1, the end of each application**, after its arguments and before its type is compared with
  the expected type, for the items created while the application was elaborated;
- **W2, before lifting** (`lift` and `lift_signature`): a queued literal may hold a `match`,
  which must be drafted before helpers are lifted;
- **W3, every round of the obligations loop** (`solve_obligations_until_stuck`), so any
  `solve_obligations` call (there are several mid-declaration) resumes too;
- **W4, `finish`**, for the whole declaration, with defaults and the stuck report.

The prototype found W1 and W2 necessary **[run]**:
- with only W3 and W4, std doesn't load. `Map/Spec.sw:1862` has
  `Eq.cong (xs => List.last (List.filter xs (e => Map.Spec.isLess e.fst key))) h`. The
  queued `e.fst` is still a placeholder when `Eq.trans` compares the `Eq.cong` with its
  expected type, the comparison fails, and nothing can wait. With W1, `e.fst` is resumed when
  `h` has fixed `e`'s type, at the end of the `Eq.cong` application;
- with W1 and without W2, aoc fails with `E-MATCH-MOTIVE` at
  `Day08/Proofs/Part2.sw:148`: a record literal `{ forward = …, backward = … }` holding a
  `match` is resumed after its declaration's helpers were lifted.

**Scope.** At W1, only items created during the application are resumed (Lean's
`withSynthesize`). An item created outside is resumed at the outer application's W1 or at W4.
This keeps an outer item's failure from being blamed on an inner attempt. The prototype
measured both versions ([§6.5](#65-variants)).

**The ladder** (one function; W1-W3 run steps 1-2, W4 runs all):
1. Resume, in creation order, every item in scope whose blocker is solved (its type's head is
   no longer an unknown). Fill its placeholder with the checked term
   ([§5.6](#56-filling-a-placeholder)). Resuming may queue new items; they go at the end. If
   anything was resumed, repeat step 1.
2. Run a round of obligations and row constraints. If anything was solved, go to 1.
3. (W4 only) Apply **one default**, the first by priority, then by creation order: priority 1,
   SW-805's field-name rule for a waiting record literal; priority 2, `Nat` for a waiting number
   literal ([§5.4](#54-defaults-and-sw-805s-rule)). If one applied, go to 1.
4. (W4 only) If items are still waiting, report ([§5.5](#55-stuck-items-and-errors)).

**Why it terminates** [inferred]:
- Each repeat of step 1 resumes at least one item, and an item is resumed once in each
  surviving elaboration (the resumption log). A resumed K1 is checked at a known type, so it
  never queues itself again; a resumed K2 can queue a new K2 only at a *later* step of the
  receiver's type-head view, which is finite.
- New items come only from elaborating syntax nodes of the declaration, at most once per node
  per surviving elaboration, so there are finitely many.
- Each return from step 2 follows a solved unknown or a settled row. Unknowns are solved once,
  except where a snapshot restores them, and the ladder takes no snapshot.
- Each default (step 3) resolves one waiting item, and defaults never un-solve anything.
- Snapshots inside resumed items are ordinary attempts, each finite as today.
- The elaborator's budget (`budget.step`) remains the backstop, as for unification.

### 5.4 Defaults, and SW-805's rule

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

**`held` and `last_resort` are subsumed.** They exist so that a literal in one part of `==`,
`++`, `calc` or a comparison group waits for another part to say its type. With K1, every
literal waits, so the other part always gets the chance, and the field-name rule applies only
where nothing else said. With the prototype on, `last_resort` reran 0 times, against 5 with it
off **[measured]**. The `FieldNames` counters, `held`, `last_resort`, and the three "infer one
side, on `E-CANNOT-INFER` infer the other" catches can go once K1 is in (stage 5). D1991's R1
still holds: the default looks at names only. What changes is *when* it runs, which D1991
doesn't fix.

### 5.5 Stuck items and errors

**Stuck at the end.** Each item carries the error its site raises today (code, message, span,
notes). At W4, the first item still waiting, in creation order, gives the declaration's error,
as today's first `E-CANNOT-INFER` does. With the prototype on, **no reject example's error
changed** (687 files), and the 4 items left stuck were in those files **[measured]**.

**Resumed and failing.** A resumed item that fails gives its own error, at its own span, against
the type now known: `Ctx::save` keeps the span, and `cx.mismatch` prints today's solutions. This
is Lean's `withRef stx` plus `instantiateMVars` (`SyntheticMVars.lean:33-39`). It is usually the
more useful error. In the prototype this arose once, in `postponed-lambda-second-error.sw`
([§6.2](#62-acceptance-changes)).

**Several stuck items.** Lean and Idris report every one. Stitchwort reports one error per
declaration today. Whether to report all stuck items is left open (question 5 of the brief); it
matters most in the language server.

### 5.6 Filling a placeholder

A placeholder must be filled with the **checked term**, as `fill_placeholder` does today, not by
unifying it with the term's value. The prototype unified, and in `Day06.offRouteFree` that wrote
`Map.Spec.sameKey.%match1 (Position.%compare blocker other)` where the source and today's term
have `Map.Spec.sameKey blocker other` **[run]**: reading a value back unfolds calls. The fix is
to solve the placeholder to the term abstracted over the item's context, since a placeholder is
a fresh unknown applied to the variables in scope (`Ctx::fresh_meta`), and zonking then puts the
term itself in place [inferred]. Wherever the placeholder has been copied into types, those see
the same solution.

### 5.7 Removing the catch-and-retry paths

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
information a proof search sees. A queue item would need a blocker ("the goal has no unknowns
left"), which isn't one unknown. It stays, and it can be re-expressed later as a queue item
with an application-scope blocker if that helps [inferred].

### 5.8 The existing postponements as instances

- **Record literals (SW-817, SW-885).** K1 at the literal, field-name default at W4.
- **`.field` on an unknown type (SW-847).** K2.
- **Method sections.** K3: the section becomes `x => x.f …` at once, with `x : ?D`, and its body
  waits on `?D`. Today's special case "postponed without a try unless a later parameter
  depends on it" goes, and so does `section_unknown_name`'s separate error path (the K2 inside
  carries the section's message).
- **Lambda arguments.** No longer postponed as a whole. Their stuck pieces are K1-K4, resumed at
  the application's W1, which is where today's postponed lambdas are checked.
- **`late_literals`.** K4.
- **`after_expected`.** Kept as is ([§5.7](#57-removing-the-catch-and-retry-paths)).

### 5.9 The unifier's put-aside pairs

Two levels, kept apart, as in draft 1:
- **The unifier's pairs (SW-896)** live inside one `unify` call. One still stuck when the call
  ends makes the call return `false`.
- **The queue** holds *checks* (syntax plus context) across the declaration. A resumed item runs
  ordinary `check`, whose own `unify` calls put pairs aside as usual.

The single pass makes their relation sharper. A placeholder is an unknown that a later resume
will solve, so a comparison that meets one may fail where it would have succeeded a little
later: that is the `Map/Spec.sw:1862` failure. Today's design answers this by resuming early
(W1). The larger lever, a comparison that *waits* (a put-aside pair kept as a declaration-level
constraint, as `rows::postpone` does for rows and as Agda's `ValueCmp` constraints do), would let
the queue resume later and less often. Draft 1 measured that 91-94% of put-aside pairs fail with
nothing solved since. It is a separate change with its own decision; the queue doesn't depend
on it (question 3 of the brief).

### 5.10 `let`, and SW-847 (D2011 kept)

`pure_let` still infers the value first. When `item.value` is reached with `item : ?B`
unknown, it is a K2 item and the lambda's body type is the placeholder's type. The body
`List.sumBy pairs counted` unifies the parameter with `(Nat, Item)`, and the next resume point
resumes `.value` with `?B = Item`. The prototype accepts sw847.sw this way, and the test
`total [(0, {value = 5}), (7, {value = 9})] == 5` passes **[run]**. So D2011 still fits the
single queue and is kept: no body-first `let` (Lean's `let_delayed`), and the `let` stays
transparent for the body.

A let-bound method section (`let g := .drop 1; g xs`) works the same way once K3 exists, which
moves `examples/reject/section-unknown-receiver.sw` to accept [inferred; the prototype doesn't
queue sections, and that example is unchanged with it on].

### 5.11 The language server

The language server elaborates a file's declarations with the same elaborator
(`crates/cli/src/lsp.rs`), so the queue's behaviour there is the batch behaviour. What differs:
- **Broken code.** A stuck item reports the error its site reports today, so diagnostics while
  typing `p.` are unchanged. A resumed item that fails reports at its own span, which is where
  the user is typing.
- **Hover and goals** see more: a `?` goal or a hovered variable inside a queued check is noted
  when the check resumes, with its type known, where today the whole declaration stopped at the
  first `E-CANNOT-INFER` [inferred].
- **Cost.** The queue is per declaration and is cleared with it, so incremental re-checking is
  unaffected. A resume point with nothing in scope costs a length comparison. CPU time over the
  corpus didn't rise ([§6.4](#64-cpu-time)).
- **Several errors.** If stuck items are all reported (question 5), the editor shows each.

### 5.12 Snapshots (P3 revisited)

D1990's P3 says queued items need no snapshot because they try nothing before waiting. That
still holds for queueing: K1 waits before checking any field, and K2 keeps the receiver it
elaborated. It holds for resuming too: an item is resumed only when its blocker is solved, so
the head test that queued it now passes. What the prototype added is that the *queue itself* is
part of the state that snapshots around items record (items and resumption log,
[§5.2](#52-where-the-queue-lives-and-how-items-wait)).

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
| `Day05.noRuleBroken` | `rule.before == laterPage`: `Decidable.toBool (DecEq.decide …)` instead of `Decidable.toBool (Nat.decEq …)` | **needed fix**: the same value, but the generic dictionary call where today's term has the specialised one; extraction and evaluation take the slower route | `==` must choose its specialised form after the operand's type is known: make that choice a K-item or redo it at W1 |
| `Day06.offRouteFree` | `Map.Spec.sameKey.%match1 (Position.%compare blocker other)` instead of `Map.Spec.sameKey blocker other` | **needed fix**: the placeholder is filled by reading back a value, which unfolds the call ([§5.6](#56-filling-a-placeholder)) | fill placeholders with the checked term |
| `Day06.part2Correct` | inside `Eq.cong (patrolled => Option.map patrolled (visited => (visited.filter …).size))`, where `.filter` and `.size` are on a lambda parameter whose type `patrolRoute …` fixes later: the lambda's term is the one checked in place (shorter: 10,936 against 11,762 characters of `{:?}`) | harmless [inferred: the same kind as `carriesMentioned`; the kernel re-checked it against the same statement] | none |
| `Day08.harmonicsCorrect` | `stepFacts`'s motive `_` is solved to the folded goal `point ∈ City.harmonics city first second ↔ …` instead of its unfolding `point ∈ List.flatMap … ↔ …` | harmless, arguably better: definitionally equal, and as written | none |
| `Day24.carriesMentioned` | `List.memFlatMapIntro (each => [each.left, …])`: the lambda as written appears where today's term has the unifier's copy from `device.wires`'s definition (a different library call, its lambda named `gate`) | harmless, arguably better: today the in-place try fails, and the postponed lambda's own term is not what ends up in that argument [inferred] | none |
| 19 others in days 5, 6, 8, 24 (for example `Day05.part1Correct`, `Day24.shapeAdds.%match3`) | identical terms | harmless: they refer to a changed declaration | none |

All 24 aoc declarations are in `Proofs` namespaces: proof terms, re-checked by the kernel against
statements whose types are compared in [§6.3.1](#631-statements). None of the 26 is a sign that
the design is wrong. Two are bugs of the prototype that the design already rules out (§5.6) or
must add (the `==` specialisation).

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
| W1-W4, field-name rule at the literal (`…_NAMES_FIRST=1`) | "in a list" passes; "the other side says" and "appended" fail (§5.4) |
| W1-W4, W1 scoped (`…_SCOPED=1`): **the recommended form** (D2014) | one acceptance change, `record-literal-inferred.sw` as above; `postponed-lambda-second-error.sw` stays rejected with today's error, because `c.size` is resumed only at the end of the `twice` application, outside the attempts inside it; the same 26 hash changes; no error message changed; 179 items queued, 136 resumptions (149 unscoped); aoc 36.7 s against 38.0 s off (one run) |

### 6.6 The work this implies

From §6.2-6.5, for the end state:
1. **Fill placeholders with the term** (§5.6).
2. **Resume points W1 and W2**, scoped (§5.3).
3. **K4 and the defaults ladder** (D2013), which fixes `record-literal-inferred.sw`.
4. **`==` specialisation after the type is known** (`Day05.noRuleBroken`).
5. **K3** for sections, which removes the last 6 lambda postponements in accepted code.
6. **Examples**: rewrite `record-literal-inferred.sw`'s "in a list" with an annotation until K4
   (stage 2), unannotated after; move `section-unknown-receiver.sw` to accept after K3.
7. **The retry paths of §5.7**, removed once 3 and 5 are in.

## 7. Risks

- **Order-dependence through defaults and `true`/`false` unification.** The ladder is
  deterministic (creation order, priorities), not order-free as OmniML is. The two acceptance
  changes of §6.2 are both order effects. The defaults' priorities are a design choice (D2013).
- **Resumption inside attempts.** An item resumed inside an attempt that then fails is undone
  and resumed again later. That is correct but can change routes: one reject example's outcome
  moved this way. Scoped resume points limit it (§5.3).
- **Placeholders seen by comparisons.** Anything that compares a type with a placeholder before
  its resume point may fail where today's order succeeded. W1 covers the corpus; new code may
  find more. The fallback is waiting comparisons (§5.9).
- **Lifted helpers.** A placeholder must not reach `lift`. W2 handles `lift` and
  `lift_signature`; other places that zonk mid-declaration (`settle_let_lambda`, `decreasing`'s
  and `partial`'s callers of `finish`) must each be checked [inferred].
- **Saved contexts.** `Ctx::save` clones the context's vectors. Fine for 178 items; a
  declaration with thousands would want persistent vectors [inferred].
- **K2's kept receiver** was elaborated under assumptions that may change, for example implicit
  arguments inserted for dot-call placement before the type is known. Agda's
  `CheckProjAppToKnownPrincipalArg` carries metavariables for this (`Application.hs:1470-1474`).
  No case arose in the corpus.
- **Interaction with SW-805.** The rule must stay a name rule (D1991's R1). Running it as a
  default doesn't change what it looks at.

## 8. Stage plan

Accepted-program identity is no longer a requirement. Each stage must keep every test, every
example's expectation (accept, reject with its code, extract output), every AoC answer and
every rogue test right. A changed hash is fine; each changed hash is listed in the stage's
commit with its kind from §6.3, and the snapshots are re-baselined.

**Stage 1: the queue and its resume points, nothing queued yet.** The table, `Ctx::save`, the
resumption log, `Snapshot` and `rewind` handling, the ladder at W1-W4 (scoped), placeholders
filled with the term (§5.6), the stuck report, and a counter in `STITCHWORT_TIMINGS`.
*Shown right by:* every hash and every error unchanged (nothing is queued yet); unit tests that
a snapshot's restore drops items and resumptions made after it, that `rewind` empties the
queue, and that a placeholder is filled with the term (a call stays folded).

**Stage 2: K1 and K2, with the field-name rule as the default.** As in the prototype.
*Changes:* the 26 hashes of §6.3, minus `Day06.offRouteFree`'s unfolding (stage 1's fill) and
minus `Day05.noRuleBroken`'s if the `==` fix lands here (work item 4); `record-literal-inferred.sw`
"in a list" fails until stage 4, so stage 2 rewrites that one test with an annotation
(`(p: Position) => p.row`) and stage 4 removes it. With W1 scoped, no reject example changes.
The ticket repros become accept examples:
`postpone-record-literal-argument.sw` (sw817), `postpone-let-lambda-field.sw` (sw847),
`postpone-effectful-record.sw` (sw885's four cases, with the run-time tests of §1).
*Shown right by:* the merge tier; `task test:aoc` and rogue's tests with every answer unchanged;
`task snap:examples` writing no changed error message; the hash diff matching the stage's list.

**Stage 3: K3, method sections.** Remove the section-without-a-try path and
`section_unknown_name`'s special case. *Changes:* `section-unknown-receiver.sw` moves to accept
(D2011), with a new reject example for a section that nothing ever fixes; the 6 aoc lambda
postponements become section items, so their declarations may change hash.
*Shown right by:* as stage 2, and the lambda try-then-postpone counter at 0 in accepted code.

**Stage 4: K4 and the defaults ladder** (D2013). Number literals wait; defaults by priority.
*Changes:* `record-literal-inferred.sw`'s "in a list" passes unannotated again; hashes wherever a
literal's type is now decided later (to be measured with the prototype extended first, as here).
*Shown right by:* as stage 2, plus the numbers examples (`examples/accept/*number*`,
`*literal*`) unchanged in outcome, and `retrying`'s counter at 0.

**Stage 5: remove the retry paths** of §5.7: the lambda try-then-postpone, `retrying` and
`late_literals` with `defers_literal`, `else_first` and `check_items`' reordering, `held`,
`last_resort` and `FieldNames`, the three "infer the other side" catches.
*Shown right by:* as stage 2; each removal is its own commit with the counters at 0 first.

**Stage 6 (later, each its own decision):** report all stuck items (question 5); waiting
comparisons in the unifier (§5.9); queueing the after-expected path if useful.

## 9. Tests

- **Repros become accept examples** (stage 2), with run-time tests as in §1.
- **Reject examples** pinning the stuck report: `record-literal-without-type.sw` unchanged; a
  literal whose type is fixed to a non-record (`E-NOT-A-RECORD` at the literal, its own error
  at resume); a `.field` whose receiver's type becomes a record without that field
  (`E-UNKNOWN-FIELD` at the field, against the type now known).
- **Order examples**: "in a list" from `record-literal-inferred.sw`, unannotated (stage 4); two
  literals in one application where only the second's type is fixed by a later argument;
  `((f.x a1).x a2).x a3` with `f`'s type known only later (Lean's own example of chained
  postponement).
- **Unit tests in `crates/elab`** (stage 1): snapshot restore and the resumption log; `rewind`;
  placeholder filled by the term; a K2 re-queued at a later view step.
- **Counters** in `STITCHWORT_TIMINGS`: items queued, resumed, defaulted, stuck, and each retry
  path's firings until stage 5 removes it.
- Lane tier for each stage, the merge tier at merge; AoC and rogue tests at each stage.

## 10. Decisions for Matt

**D2013. Run SW-805's field-name rule as a default in the queue's ladder, and default number
literals in the same ladder after it, instead of at the literal?** In the end state a record
literal or a number literal whose type is unknown waits. When nothing else makes progress at the
end of the declaration, the ladder applies one default, the field-name rule first, then `Nat` for
a number, and goes round again. **[Recommend yes.]** The assumptions, in full:
- **(R1, from D1991)** The field-name rule looks only at the literal's field names and the names
  in scope at the literal, never at types learned later; running it later doesn't change what it
  looks at, only whether something else decided first.
- **(N1)** A number literal that waits ends with the type the rest of the declaration fixes, and
  `Nat` where nothing does. So in a program accepted today, where each such literal was made
  `Nat` and everything else agreed with that, it still ends as `Nat`; the change only accepts
  programs that fail today because a literal was made `Nat` too early. Stage 4 tests this over
  the corpus [inferred, not yet measured: K4 is not in the prototype].
- **(N2)** The field-name rule has priority over the number default because a record's field
  types say what its numbers are, never the reverse (§5.4's "in a list").
- **(N3)** Lean's numeral default is the precedent: low priority, in the ladder
  (`Prelude.lean:1411`, `SyntheticMVars.lean:237-243`).

The alternative is Agda's order, the rule at the literal when it finds one type. The prototype
shows it breaks `held`'s two tests unless `held` and `last_resort` stay, which keeps a second
mechanism.

**D2014. Resume queued checks at the end of every application, scoped to the items made inside
it, as well as before lifting and at the end of the declaration?** This is instead of only at
the end of the declaration (Lean's definition-level ladder, Agda's freeze) or inside the unifier
when the blocker is solved (Agda's wake-up). **[Recommend yes.]** The assumptions, in full:
- **(S1)** Stitchwort's unifier can't wait: a comparison that meets an unfilled placeholder
  answers `false` at once, and its caller takes another route. So a placeholder must be filled
  before the comparisons that would need it. The end of the application that created it is the
  first fixed point after the later arguments that may solve its blocker, and before the
  application's type is compared with what is expected of it. The prototype shows the end of
  the declaration is too late for std (`Map/Spec.sw:1862`), and the end of each application is
  enough for the whole corpus.
- **(S2)** Scoping to the application's own items keeps a failing item from being blamed on, and
  undone with, an attempt it doesn't belong to, as Lean's `withSynthesize` does; items from
  outside are resumed at their own application's end or at the declaration's.
- **(S3)** Waking inside the unifier would elaborate syntax in the middle of a comparison that
  callers inside many of the 44 `Snapshot::take` sites branch on; resume points give the same order at fixed places.
- **(S4)** If waiting comparisons (§5.9) are ever added, W1 can become less frequent; this
  decision doesn't preclude that.

## 11. The prototype

**Where.** Scratch commit `8204158e` on `worktree-agent-a90adb251a628a470`, **dropped** before
this note was committed: it was built to measure, not to keep (it scans the queue, unifies to
fill placeholders, and counts retry paths with the switch off too). Its whole diff, with the
measurement test (`crates/driver/tests/queue_scratch.rs`) and scripts (`dev/queue-prototype/`), is
[postponement/prototype/queue-prototype.patch](postponement/prototype/queue-prototype.patch);
it applies to `fcb12746` with `git apply` (checked).
It adds `crates/elab/src/queue.rs` and touches `check.rs` (`Ctx::save`, the W1 point, retry
counters), `records.rs` (K1 sites, `infer_literal_by_names`), `dot.rs` (K2, `resume_dot`),
`lift.rs` (W2), `auto.rs` (W3), `lib.rs` (W4, the table), `undo.rs` and `rewind.rs`.

**Switches** (all off by default):
- `STITCHWORT_QUEUE=1`: K1 and K2, W3, W4, the field-name default;
- `STITCHWORT_QUEUE_APP=1`: W1 (unscoped); `STITCHWORT_QUEUE_SCOPED=1`: W1 scoped;
- `STITCHWORT_QUEUE_LIFT=1`: W2;
- `STITCHWORT_QUEUE_NAMES_FIRST=1`: the field-name rule at the literal when it finds one type;
- `STITCHWORT_QUEUE_TRACE=1`: each item queued and resumed, on standard error.

**Not in it:** K3, K4, the blocker index (it scans), filling with the term (it unifies), the
`==` specialisation, scoping by default.

**Outputs** kept in [postponement/prototype/](postponement/prototype/): the comparison of the
off and on runs, with the exact-term and type comparison of the changed declarations
(`changes.txt`); the queue and retry-path counters per file (`counts.txt`); and the three
repros with run-time tests (`sw817run.sw`, `sw847run.sw`, `sw885run.sw`).

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
(§5.4, D2013).

**A body-first `let`** for SW-847 (Lean's `let_delayed`): rejected in draft 1 (D2011) because it
hides the whole value from the body. The queued field access does what SW-847 needs.

**Queueing whole lambdas** (Agda's `CheckLambda`): unnecessary once their pieces wait, and it
would keep a lambda's body from being checked in place, which is where most of its information
is. The prototype's 9 remaining lambda postponements are 6 sections and 3 reject examples.

## Sources

Fetched 30 October 2026 with `gh api` into the lane's scratch directory, read as text. Line
numbers are of those copies. WebSearch was not used.

**Lean 4**, `leanprover/lean4` at `0f852cc822d54d32c5cb0ef158562796088ce4dc` (as in
docs/research/elaboration.md):
- [L1] `src/Lean/Elab/SyntheticMVars.lean`, whole file (743 lines); draft 2 also cites
  `synthesizeUsingDefault` (237-243) and `withSynthesizeImp` / `withSynthesizeLightImp`
  (689-720);
- [L2] `src/Lean/Elab/Term/TermElabM.lean`: `SavedContext`, `SyntheticMVarKind`, `Context`,
  `tryPostpone*`, `saveContext`, `postponeElabTermCore`, `postponeElabTerm`,
  `elabUsingElabFnsAux`, `elabTermAux` (lines 40-120, 300-315, 860-875, 1365-1470,
  1650-1710, 1940-1970);
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
Idris `delayOnFailure` users other than records; Lean's anonymous-constructor elaborator.

**Stitchwort**, at `fcb12746`: `crates/elab/src/check.rs` (`Ctx`, `apply_args_postponing`,
`retrying`, `fill_placeholder`, `append_tried`), `records.rs` (`FieldNames`, `held`,
`last_resort`, `infer_literal`, `check_record`), `dot.rs` (`infer_dot`, `find_in_view`),
`calc.rs`, `numbers.rs` (`Defaulted`, the comparison group), `auto.rs`, `lib.rs` (`finish`,
`clear_metas`, `with_local_retries`, zonk errors), `lift.rs` (`lift`), `undo.rs`, `rewind.rs`,
`unify.rs` (header, `run`), `crates/cli/src/lsp.rs`, `crates/driver/tests/hash_stability.rs`;
docs/research/elaboration.md §8; docs/syntax.md (records, method sections).
