# Proposal: one postponement queue in the elaborator

**Status:** draft 1, 30 October 2026. Design only: nothing in the compiler changes. Tickets
SW-817 (anchor), SW-847 and SW-885; context SW-509, SW-805, SW-896. Follows D1990 (agreed in
principle) and D1991 (SW-805's field-name rule stays, as name resolution), both in
docs/research/elaboration.md §8. Repros, the P1 counts and the scratch counter patch are in
[postponement/](postponement/). Two decisions for Matt are in [§9](#9-decisions-for-matt).

**Since this draft** (orchestrator, 30 October): SW-805 (record literals typed from their field
names when nothing else says) was merged after the note was written, at `bc0802eb`. With only one
record type having fields `x` and `y`, all four of sw885.sw's literals now check on main, so
the repro now declares a second such type (`Size`); with it, all four are `E-CANNOT-INFER` again
**[run]**. SW-885's problem and stage 0 stand for literals whose field names don't pick one type.
The P1 counts were taken before SW-805 too.

Labels, as in the other notes:

- **[checked: file:line]**: read in the Stitchwort source at `bc0802eb` (main, 30 October);
- **[run]**: run on 30 October with `target/release/stitchwort` built from `bc0802eb`;
- **[measured]**: the scratch counter of [§4](#4-p1-how-often-postponement-is-needed), dropped
  before commit;
- **[cited: S]**: read in source S under [Sources](#sources), at the commit given there;
- **[inferred]**: my reasoning from checked or cited facts, not tested;
- **[unverified]**: believed, not confirmed in a full source.

## The short answer

- **What other systems do.** Lean postpones any term elaborator that needs an unknown expected
  type, and resumes them through a fixed ladder at the end of the declaration. Agda attaches a
  postponed check to a metavariable and wakes it when a blocking metavariable is solved. Idris
  2 keeps a per-term list of delayed elaborators, sorted by reason. Rocq postpones no syntax.
  It postpones unification problems, plus the arguments after a user-written bidirectionality
  hint within one application. OmniML suspends a constraint on the *shape* of one type
  variable, and a constraint never discharged is an error ([§3](#3-how-other-systems-do-it)).
- **P1 holds only for a second pass.** Today the sites that a queue would replace (a record
  literal at an unknown type, `.field` or a method section on an unknown type) raise
  `E-CANNOT-INFER` **1,073 times while elaborating code that is accepted**: std, the accepted
  examples, aoc and rogue. Every one is caught and recovered, mostly by the existing
  try-then-postpone of lambda arguments **[measured]**. A queue that replaced those errors in a
  single pass would change how accepted programs elaborate. Only **7 of 686** reject examples
  fail with `E-CANNOT-INFER`, and no accepted file does **[measured]**.
- **Design.** There is one queue of postponed checks per top-level declaration, used only in a
  **second pass**. That pass re-elaborates a declaration that failed after raising a queueable
  `E-CANNOT-INFER`, as `with_local_retries` already re-elaborates failing bodies
  (`lib.rs:2267`). A queued item waits on one unknown. It is resumed when that unknown is
  solved, inside the loop that already retries obligations and row constraints. If the second
  pass fails, the first pass's error is reported. So every program accepted today is
  elaborated identically, and every program still rejected gets the same diagnostic. This
  holds by construction ([§5](#5-the-design)).
- **Tickets.**
  - SW-817's remaining case (two record types with the same fields) becomes a queued literal.
  - SW-847 becomes a queued field access inside the let-bound lambda. The use in the body
    fixes the type, as Lean's `resolveLValLoop` and Agda's `CheckProjAppToKnownPrincipalArg`
    would. No new `let` syntax is needed (D2011).
  - SW-885 is mostly not a postponement problem. In three of its four cases the parameter or
    field type is already known, but the effect pass runs the literal first with `infer`
    (`effects.rs:3671-3675`). Passing the known type fixes them. Only the generic case needs
    the queue.
- **Stage 1** leaves every accepted program's content hashes unchanged and every
  still-rejected example's error unchanged. It newly accepts the ticket repros and, as
  predicted, one reject example (`section-unknown-receiver.sw`, [§7](#7-stage-plan)).

## 1. The problem

`E-CANNOT-INFER` stops the declaration whenever a construct needs a type that a *later* part
of the declaration would fix. Postponement exists today only for lambda and method-section
arguments within one application ([§2](#2-stitchwort-today)). Each repro below is in
[postponement/](postponement/). The output is from `stitchwort check` **[run]**.

**SW-817**, [sw817.sw](postponement/sw817.sw): a record literal as an argument whose type only
a later argument fixes.

```
type Tally = { enabled: Bool, total: Nat }
type Score = { enabled: Bool, total: Nat }
def step (tally: Tally) (n: Nat): Tally := …
def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total
```
```
[E-CANNOT-INFER] Error: can't tell which record type this record literal is
    ╭─[ docs/proposals/postponement/sw817.sw:22:47 ]
 22 │ def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total
    │                                               ──────────────┬──────────────
    │                                                             ╰──────────────── its type isn't known here
    │ Note: add a type annotation, as in `(p: Person)`
```

AoC 2024 day 3's literal has a single record type with those fields, so SW-805's field-name
rule (being merged separately) accepts it without a queue. `Score` is there to show what the
rule leaves over: two types with the same fields, where only `step` can choose.

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
says what type it should have", at the literal (lines 22, 24, 26, 31) **[run]**. The same
literal as the whole body, or annotated, is accepted.

## 2. Stitchwort today

**Argument postponement** (`check.rs:1894-2165`, documented at `:1785-1803`) **[checked]**:
- A lambda argument whose domain is unknown, with a later explicit argument, is tried in place
  under a `Snapshot`. If that fails, it is restored and checked after the later arguments
  (`:1956-1971`, pushed at `:1990`).
- A method section is postponed without a try, unless a later parameter's type depends on it
  (`:1958-1959`).
- A lambda that fails where the application's expected type is known (`late_able`, `:1939`),
  and a non-lambda argument that fails while its type has unknowns (`:2068-2091`), are checked
  again after the application's type is compared with the expected type (`after_expected`,
  resumed at `:2155`).
- With `late_literals`, a constructor or list of number literals is checked last (`:2034-2055`),
  under `retrying` (`:1865`), which runs the whole application twice.
- Postponed items are resumed at the end of the same `apply_args_postponing`. If one fails,
  the error from the in-place try is kept when both are `E-CANNOT-INFER` (`first_error`,
  `:2107-2124`). The checked term replaces the placeholder in the application
  (`fill_placeholder`, `:2134`), so that zonking doesn't write out an unfolded value.

**Where `E-CANNOT-INFER` is raised for the constructs in the tickets** **[checked]**:
- a record literal inferred (`check.rs:1354-1360`), or checked against an unknown
  (`records.rs:648-660`, `record_type`);
- `.field` on a receiver whose type is unknown (`dot.rs:458-470`, `find_in_view`);
- a method section whose argument type is unknown (`dot.rs:690-700`).

**Let.** `pure_let` (`effects.rs:4155-4203`) infers an unannotated value first, then checks the
body with the name as a transparent `let`. A let-bound lambda's parameter types are unknowns
that the body's uses can solve (SW-509, `settle_let_lambda` at `effects.rs:1449`; reported as
`E-CANNOT-INFER` from `parameter_metas` at zonk, `lib.rs:1185-1196`). SW-847 fails before that
point: `.value` is looked up while the value is inferred.

**Effects (SW-885).** In a computation, a call's effectful arguments run first, each bound to a
fresh variable (`comp_app`, `effects.rs:3098-3170`). `run_argument` receives the parameter's
type when the signature gives it (`call_param_types`, `:1952-1977`). It passes that type on
only for a decided proposition (`:3687-3709`); everything else goes to `run_first`, which
calls `comp_infer` (`:3671-3675`). `comp_compound` runs a tuple's, record's or list's parts the
same way (`part`, `:3804-3809`), although `expected` is known there.

**The unifier's put-aside pairs (SW-896).** `unify::run` (`unify.rs:30-80`) puts aside a pair
that fails while one side is blocked on an unknown. It compares the pair again after the rest
of the same call, and only if the rest solved something. Nothing outlives the call: the result
is `true` or `false`.

**Other declaration-level waiting** **[checked]**:
- obligations (instances) wait and are retried in rounds (`auto.rs:100-126`);
- row comparisons that can't be decided are kept with their context (`env`, `types`, `names`,
  `span`) and retried in that same loop (`rows.rs:223-244`, `auto.rs:106-110`).

  This is the one place today where a check outlives its call site, and the queue copies its
  representation.
- `finish` (`lib.rs:1085-1090`) compares awaited helpers, runs that loop, settles rows and
  zonks.
- `Snapshot` (`undo.rs:35-52`) records the length of each per-declaration table, and
  `restore` truncates them.
- `with_local_retries` (`lib.rs:2267-2292`) re-runs a failing declaration body after admitting
  local definitions.

## 3. How other systems do it

Every row below comes from source files fetched with `gh api` on 30 October 2026, or from the
OmniML paper's full text. Commits and URLs are under [Sources](#sources).

| | What is postponed | Where it lives | When resumed, in what order, how it stops | Still stuck at the end | Errors |
|---|---|---|---|---|---|
| **Lean 4** | Any term elaborator that calls `tryPostpone…`: structure instances, `.field` on an unknown type, anonymous constructors, `elab_as_elim` minor premises. Not `fun`. | A synthetic metavariable of kind `.postponed (SavedContext)`, listed in `pendingMVars`. The local context is the metavariable's own. | `synthesizeSyntheticMVars`: steps in creation order while one makes progress. Then, in order, retry with postponing off (errors postponed), default instances, retry with postponing off (errors reported), tactics. Runs at the end of each definition and at nested `withSynthesize` points. | Can't stay stuck. The last retry runs with postponing off, so the elaborator commits or fails. For `.postponed`, `reportStuckSyntheticMVar` is `unreachable!`. | Logged at the postponed syntax (`withRef stx`), against the metavariable's type as now known. The term becomes `sorry` and elaboration goes on. |
| **Agda** | A `TypeCheckingProblem`: `CheckExpr`, `CheckArgs` (the remaining arguments), `CheckProjAppToKnownPrincipalArg`, `CheckLambda`, `DisambiguateConstructor`, `DoQuoteTerm`. Sites include a record expression with several candidate types, a record update, a check blocked on a pattern, and some lambdas. | A metavariable instantiated as `PostponedTypeCheckingProblem (Closure …)`, plus an `UnBlock` constraint with a `Blocker`, in the type checker's constraint lists. Unification constraints sit in the same lists. | Woken when a blocking metavariable is solved, then solved one at a time from the awake list. At a declaration's end: wake all, solve sizes, wake again, freeze the metavariables. | Left as constraints. At the end of the module they become the warning `UnsolvedConstraints`, an error in batch mode. There is no defaulting. | Each constraint is printed with its range. Postponed type-checking problems are filtered out as "not interesting", except constructor disambiguation. |
| **Idris 2** | Elaborators wrapped in `delayOnFailure` (try first, postpone on a matching error) or `delayElab`, with reasons `CaseBlock`, `Ambiguity`, `LazyDelay`, `RecordUpdate`, `Rewrite`. | `delayedElab` in the unifier state: a closed elaborator per hole, with the local hints. It is saved and restored around each `elabTermSub`. | At the end of `elabTermSub`, sorted by reason. Retries keeping recoverable errors repeat while some succeed, with constraint solving in between. Then a pass that reports all errors. Then default and last-chance constraint solving. | Errors. | The delayed elaborator's own error, at its own location. In the last pass it tries the later ones too, and prefers a non-generic error. |
| **Rocq** | No syntax, except within one application: the arguments after a user-written bidirectionality hint `&`, when an expected type is given, plus `Program`'s constructor parameters. Unification problems are postponed. | `conv_pbs` in the evar map. | `solve_unif_constraints_with_heuristics` retries stuck problems while one makes progress. It is called from `solve_remaining_evars_from` after type classes and hooks. | `error_cannot_unify` or `error_unsolvable_implicit`. | At the problem's or evar's recorded location. |
| **OmniML** | Any construct that needs a type's shape, as a suspended `match` constraint: record labels, polytypes. | A wait list on each unification variable, flushed into a global scheduler when that variable is unified. | Any order: the meaning doesn't depend on it. | "A match constraint that is never discharged is considered unsatisfiable". Defaults aren't formalised; the prototype can attach one. | The prototype has basic reporting only, "attaching source locations to constraints". |

**Lean 4** [cited: L1-L6].
- **Postponement is an exception.** When `mayPostpone` is set, an elaborator throws
  `Exception.postpone` (`tryPostpone`, `TermElabM.lean:1374-1415`). `elabUsingElabFnsAux`
  catches it, **restores the state saved before the elaborator ran**, and registers the syntax
  (`:1678-1701`, `postponeElabTermCore` at `:1456-1460`).
- **Restoring state.** The comment explains why it restores: in `((f.x a1).x a2).x a3`,
  each `.x` postpones in turn. Without the restore, "dead" metavariables would stay on the
  pending list, and resuming "start[s] it from scratch".
- **Resuming.** `resumePostponed` (`SyntheticMVars.lean:32-77`) takes `saveState` again,
  re-elaborates under `withRef stx` against `instantiateMVars mvarDecl.type`, and on
  postpone or error (when `postponeOnError`) restores and reports no progress.
- **The ladder** is `synthesizeSyntheticMVars` (`:638-672`): `filterRevM` keeps creation order
  (`:609-611`). The definition-level call is `synthesizeSyntheticMVarsNoPostponing`
  (`MutualDef.lean:1403`); `withSynthesize` also runs it inside an elaboration (for example
  `App.lean:375`).
- **Postponing sites**: structure instances (`StructInst.lean:1357-1365`); dot notation
  (`resolveLValLoop`, `App.lean:1678-1694`, which tries default instances before failing);
  `elab_as_elim` minor premises (`App.lean:1314`). `fun` elaborates its body at once
  (`Binders.lean:678`).
- **Body-first `let`.** `let_delayed` (`Binders.lean:951-952`) sets `postponeValue`. The value
  is a fresh metavariable while the body is elaborated, then the value is elaborated and
  unified with it (`:779-782`, `:848-856`).
- **Pitfalls named in the code:**
  - the order-dependence of the step that turns postponing off ("we are essentially giving up
    the opportunity of learning `x`s type", `SyntheticMVars.lean:646-659`);
  - long unfolding against synthetic-opaque metavariables left in a `let`'s type, issue #4051
    (`Binders.lean:754-773`).

**Agda** [cited: A1-A8].
- **Postponing.** `postponeTypeCheckingProblem` (`MetaVars.hs:629-661`) creates a metavariable
  whose instantiation is the closure of the problem. It also creates an alias metavariable that
  it returns, and adds `UnBlock m` under the blocker.
- **Waking.** `solveConstraint_ (UnBlock m)` enters the closure, runs
  `checkTypeCheckingProblem`, and assigns the result (`Constraints.hs:300-326`, `:344-352`).
  `wakeupConstraints` wakes what was blocked on a solved metavariable (`:249-253`).
- **At a declaration's end**: `Decl.hs:226-240`.
- **Record literals.** `checkRecordExpression` at a blocked type calls `guessRecordType`
  (`Term.hs:1118-1123`). It finds every record type in scope with *at least* the given fields
  (`findPossibleRecords`, `Records.hs:219-235`):
  - none: error;
  - one: commit;
  - more than one: postpone (`Term.hs:1177-1215`).

  This is SW-805's rule followed by a queue, in that order.
- **Projections.** `CheckProjAppToKnownPrincipalArg` keeps the principal argument's value and
  type, so that argument isn't checked again (`Application.hs:1440-1476`).
- **Stuck at the end.** These become `UnsolvedConstraints` (`Pretty/Warning.hs:988-1004`), but
  `interestingConstraint` drops postponed type-checking problems other than constructor
  disambiguation (`Pretty/Constraint.hs:42-51`). So a stuck postponed check is reported only
  through the unsolved metavariables it leaves **[inferred]**.
- **Pitfall.** A comment calls committing to a function type for an untyped lambda "hazardous"
  (implicit lambdas, modalities; `Term.hs:591-606`).

**Idris 2** [cited: I1-I4].
- **The queue.** `delayOnFailure` and `delayElab` (`TTImp/Elab/Delayed.idr`) push a closed
  elaborator, built by `mkClosedElab` over the environment, onto `delayedElab`
  (`Core/UnifyState.idr:102-107`).
- **The order** of the reasons was "chosen to give the most likely useful error messages
  first" (`UnifyState.idr:65-77`).
- **Resuming.** `retryDelayed` repeats while there is progress, then reruns with `AllErrors`
  (`Delayed.idr`, `retryDelayed'` and `retryDelayed`). It is called from `elabTermSub`, sorted
  by reason (`TTImp/Elab.idr:110-148`).
- **No restore.** `delayOnFailure` runs the elaborator first and postpones on a matching error.
  The handler doesn't restore state **[inferred]**: there is no restore in `Delayed.idr`, and
  `Core` references are mutable.
- **Record updates** are delayed this way (`TTImp/Elab/Record.idr:244-259`). Which errors may
  be retried is a heuristic (`recoverable`: a `CantConvert` unless the heads clash).

**Rocq** [cited: R1-R4].
- **Bidirectionality hints** (`pretyping.ml:1057-1120`, `:1181-1201`): when an expected type is
  given, the arguments after the hint are evars. The application is coerced to the expected
  type, then those arguments are pretyped against their refined types (`refine_arg`). This is
  Stitchwort's `after_expected` with the cut point written by the user.
- **Unification problems.** `solve_unif_constraints_with_heuristics` (`evarconv.ml:2087-2121`)
  and `check_problems_are_solved` (`:2044-2047`) handle the postponed problems.
  `apply_heuristics` "Resolve[s] eagerly, potentially making wrong choices"
  (`pretyping.ml:375-379`).
- **Record syntax** `{| f := … |}` is resolved by its first field's name during
  internalisation (`sort_fields`, `constrintern.ml:1576-1581`), so a record literal never waits
  on a type.
- **Where problems are added:** `add_conv_pb` is in `engine/evd.ml:924-926`. Code search shows
  `evarsolve.ml` and `cases.ml` calling it. Which cases they postpone is **[unverified]**.

**OmniML** [cited: O1].
- **Suspension** is introduced in §2.4. Suspended match constraints are formalised in §4.1, and
  the implementation's wait lists and scheduler are in §6.
- **Records.** §3.2 gives the closed-world rule for record literals: the literal's labels
  "exactly match" one record type's labels. It "depend[s] only on the global label
  environment". That is SW-805's rule.
- **Defaults** are left out ("No defaults, by default", §2.5).
- **Errors** (§7): suspended constraints "do not fundamentally complicate error reporting".
- **Cost.** The implementation's main cost is the interaction with let-generalisation
  (partial generalisation, a tree of regions, §6). Stitchwort doesn't generalise `let`, so it
  doesn't have that cost **[inferred]**.

**What this says for Stitchwort** [inferred]:
1. Every system attaches a postponed item to the unknown it waits on (Agda's blocker, OmniML's
   wait list) or retries everything while there is progress (Lean, Idris, Rocq). Waiting on
   one unknown is cheaper and gives the order for free.
2. Lean and Idris resume by running the syntax again, so they need a snapshot on every resume.
   Agda keeps what was already checked (`CheckProjAppToKnownPrincipalArg`, `CheckArgs`). A
   queued item that decides to wait *before* doing anything, or keeps what it did, needs no
   snapshot (P3, [§5.6](#56-p3-no-snapshot-for-a-queued-item)).
3. The name rule goes before the queue: Agda's `guessRecordType`, OmniML's closed-world rule,
   Rocq's first-field rule. This is the order D1991 already gives.

## 4. P1: how often postponement is needed

**Method.** A scratch commit added a counter at each postponement site and at each queueable
`E-CANNOT-INFER` site, plus a nesting depth of `Snapshot`s. It also added an ignored test that
loads the library eagerly, then each example (rewinding between them), aoc and rogue. The
patch is [postponement/p1-counters.patch](postponement/p1-counters.patch), the output is
[postponement/p1-counts.txt](postponement/p1-counts.txt), and the commit was dropped. Two runs
gave identical output. (A first version counted per thread and lost the library's
parallel-loaded hits; the version kept counts globally.) **[measured]**

**Existing postponement** (how often it fires, against the lambda arguments and all explicit
arguments elaborated):

| | std | examples/accept (318) | aoc | rogue |
|---|---|---|---|---|
| lambda arguments reached | 2,362 | 1,857 (186 files) | 3,179 | 275 |
| explicit non-lambda arguments | 55,527 | 59,153 | 86,380 | 11,067 |
| lambda postponed after a failed try | 45 | 19 (9 files) | 73 | 3 |
| section postponed without a try | 33 | 1 | 12 | 0 |
| literal checked last (`late_literals`) | 0 | 10 (4 files) | 0 | 0 |
| lambda checked after the expected type | 5 | 5 | 52 | 3 |
| other argument checked after the expected type | 3 | 13 | 136 | 9 |
| postponed lambdas that then checked | 45 | 29 | 73 | 3 |

So postponement already fires in about 1 in 1,000 arguments in std (86 of 57,889) and 3 in
1,000 in aoc (273 of 89,559). About 2% of lambda arguments are postponed.

**The sites the queue would replace, in code that is accepted**: each count is an
`E-CANNOT-INFER` that was raised and then caught by some try.

| site | std | examples/accept | aoc | rogue |
|---|---|---|---|---|
| `.field` on an unknown type (`dot.rs:458`) | 248 | 183 (8 files) | 514 | 77 |
| record literal at an unknown type (`records.rs:654`) | 0 | 3 (1 file) | 2 | 0 |
| method section, unknown receiver (`dot.rs:690`) | 0 | 0 | 46 | 0 |
| record literal inferred (`check.rs:1356`) | 0 | 0 | 0 | 0 |

That is 1,073 raises, all inside at least one `Snapshot`. Being inside a snapshot doesn't
separate the cases well, because 83% of all arguments are elaborated inside one (std: 46,099
of 55,527). The decisive fact is that these programs are accepted. Each of these errors steered
a try to fail and another route to be taken, and a queue that swallowed them would take the
first route instead.

**In the reject examples**, 7 of 686 fail with `E-CANNOT-INFER`:
- `dot-cannot-infer`, `lambda-dependent-never-fixed`, `record-field-of-unknown`,
  `section-underscore`: `.field` on an unknown;
- `record-literal-without-type`: a record literal;
- `section-unknown-receiver`: a method section;
- `lambda-parameter-cannot-infer`: none of these sites (it fails at zonk).

**The unifier's put-aside pairs** fire often, and mostly don't help: 1,674 put aside in std, of
which 1,566 (94%) fail again with nothing solved since. In aoc it is 5,854 and 5,300 (91%).

**Conclusion on P1.** As D1990 stated it ("queued checks are needed rarely enough that the
cost is small"), P1 is true for a second pass and false for a single pass:
- A second pass runs only on declarations that fail after a queueable raise. In this corpus
  that is 6 reject files and none of the accepted code.
- A single pass would have changed the route at 1,073 points in accepted code.

The 2% of lambda arguments postponed today is the closest measure of how often a single pass
would *use* the queue in new code **[inferred]**.

## 5. The design

### 5.1 What goes in the queue

A **queued check** is the following [inferred; all of it new]:
- what to elaborate: one of the kinds below;
- the **blocker**: the one metavariable it waits on;
- the saved context: `Ctx` without `e`, cloned, which is every field of `check.rs:38-95`;
- a **placeholder** metavariable standing for its result in the term built so far;
- its span.

Stage 1 has four kinds. Each is created exactly where today's `E-CANNOT-INFER` is raised, and
only in the second pass ([§5.2](#52-where-the-queue-lives-and-when-it-is-used)):

| kind | created at | blocker | resumed as |
|---|---|---|---|
| Q1 record literal | `records.rs:654` (checked) and `check.rs:1356` (inferred, with a fresh type unknown), only after SW-805's field-name rule has found no unique type | the expected type's head unknown | `check(literal, expected)` |
| Q2 field access or dot call | `dot.rs:458`, with the receiver's term and type kept (as Agda's `CheckProjAppToKnownPrincipalArg`) | the receiver type's head unknown | the lookup and call from `find_in_view` on, with the kept receiver |
| Q3 method section | `dot.rs:690`: the section is `x => x.f …` (`dot.rs:703`), so a lambda over a fresh `x : ?D` whose body is a Q2 on `?D` | `?D` | as Q2 |
| Q4 effectful part of unknown type (SW-885 `generic`) | `run_first` (`effects.rs:3671`) when `comp_infer` would raise Q1's error: the part is bound to `%n : ?T` and its computation is a placeholder | `?T` | `comp_check(part, row, ?T)`, filling the computation's placeholder |

Not in stage 1: let-bound lambdas as a whole (D2011 explains why), other `E-CANNOT-INFER` sites
(`rfl`, `J`, numbers, quotients), and unification pairs ([§5.3](#53-relation-to-the-unifiers-put-aside-pairs)).

### 5.2 Where the queue lives, and when it is used

**Where.** It is a per-declaration table on the `Elaborator`, beside `obligations` and
`row_constraints`:
- `clear_metas` clears it (`lib.rs:1066-1081`);
- `Snapshot` records its length and `restore` truncates it (`undo.rs`), so an item queued
  inside an attempt that is undone goes with the attempt;
- `rewind` empties it with the other per-declaration state (`rewind.rs`, header).

This is per top-level declaration, as in Lean and Idris. Agda's constraint lists are global
but solved per declaration.

**When: the second pass.** A flag `queueing` is off in the first pass, so every site raises
exactly as today and a counter notes that a queueable site raised. If the first pass fails
with a non-fatal error and the counter is non-zero, the declaration is elaborated once more
with `queueing` on. If that succeeds, its result is used. If it fails, **the first pass's
error is returned**. This goes in `with_local_retries` (`lib.rs:2267-2292`), the loop that
already re-elaborates a failing body. Its callers are:
- definitions, through `lifted_body` (`lib.rs:2256`);
- tests (`lib.rs:1257`);
- defaults (`defaults.rs:262`);
- recursion on a measure (`decreasing.rs:1236`);
- partial definitions (`partial.rs:483`).

In stage 1 only the first two turn the second pass on. The other three, and the callers of
`finish` that don't go through this loop (instances, families, records, standalone inputs),
don't get a second pass until each one's lifting order has been checked
([§6](#6-risks)).

Why two passes and not Lean's one: the measurement in [§4](#4-p1-how-often-postponement-is-needed).
Today's accepted programs depend on these errors being raised and caught. The codebase already
uses "as written first, and only if that fails, the other way" for literals (`retrying`,
`check.rs:1857-1891`) and for local definitions (`with_local_retries`).

### 5.3 Relation to the unifier's put-aside pairs

These are two levels, and this proposal keeps them apart:

- **The unifier's pairs (SW-896)** live inside one `unify` call. One that is still stuck when
  the call ends makes the call return `false`. Callers branch on that `false`: 41 `Snapshot`
  sites try another route on it. A "not yet" answer would change every caller.
- **The queue** holds *checks* (syntax plus context) across the whole declaration. A resumed
  item runs ordinary `check`, so its own `unify` calls put aside pairs as usual. A queued item
  can solve the unknown a put-aside pair needed. That pair's call has already returned
  `false` by then, though, and the route it chose stands.

Agda keeps both in one constraint store (`ValueCmp` beside `UnBlock`, `Base.hs:1686-1705`), and
Rocq keeps unification problems in the evar map until the end. Turning a stuck pair into a
declaration-level constraint is the larger lever. It is what `rows::postpone` already does for
row comparisons (`rows.rs:223-244`). But it is a separate change. The 91-94% of put-aside pairs
that fail with nothing solved ([§4](#4-p1-how-often-postponement-is-needed)) are where to
measure it **[inferred]**.

### 5.4 Resume order, and why it stops

The ladder runs at the start of `finish`, and also before `lift` where lifting comes first
(`lib.rs:2256-2260` lifts a body's `match`es before `finish`). Lifted helpers must not carry
placeholders. It extends the loop of `solve_obligations_until_stuck` (`auto.rs:100-126`), so
checks, obligations and rows share one notion of progress, as Lean's ladder does (C1):

1. Take every queued item whose blocker is now solved, in creation order. That is the forced
   type's head isn't a metavariable; a solved chain counts. Resume each in its saved context.
   - If it checks, unify the result with its placeholder, and replace the placeholder in the
     declaration's term with the checked term (as `fill_placeholder` does today, `check.rs:2134`).
   - Resuming may queue new items, which go at the end.

   If anything was resumed, go back to step 1.
2. Run one round of obligations and row constraints, as today. If anything was solved or
   settled, go back to step 1.
3. Run today's settling (`settle_rows`) and zonk.
   - If queued items remain, the second pass has failed, and the first pass's error is
     reported ([§5.5](#55-how-a-late-failure-is-reported-p2)).
   - There is no defaulting step for queued checks. SW-805's rule is name resolution and runs
     at the site, before an item is queued (D1991), not as a default at the end.

**Why it stops** [inferred]:
- Each return to step 1 from step 1 removes at least one item from the queue.
- Each return from step 2 follows a solved metavariable or a settled row. Metavariables are
  solved once, except where a snapshot restores them, and step 2 restores nothing.
- New items come only from elaborating kept syntax. Elaborating a declaration is finite (it
  terminates today), and an item is created at most once per kept elaboration of its node.
  So the total number of items is finite.
- The elaborator's budget (`budget.step`) remains the backstop, as for unification.

### 5.5 How a late failure is reported (P2)

**Stage 1.** A second pass that fails reports the first pass's diagnostic, unchanged: same
code, message, span and notes. This holds whether the failure is a stuck item or something
else. It is the existing `first_error` rule (`check.rs:2107-2124`) lifted to the declaration,
and it is what makes reject examples unchanged by construction.

**Later (not stage 1).** When a resumed item fails for a reason other than being stuck (a
field of the wrong type once the record type is known), its own error is more useful than the
first pass's `E-CANNOT-INFER`. P2 says it can be reported at the item's span, with the type it
was finally checked against:
- the saved `Ctx` carries `span`, and `cx.error` labels it (`check.rs:94`);
- `cx.mismatch` prints the expected type with today's solutions.

That is how Lean reports a resumed term (`withRef stx`, `instantiateMVars`,
`SyntheticMVars.lean:33-39`). Doing it changes reject examples' messages, so it waits for its
own decision once stage 1 has run.

### 5.6 P3: no snapshot for a queued item

A queued item doesn't need a `Snapshot`: not when it is queued, and not when it is resumed. It
does need its context, as Lean's `SavedContext` plus the metavariable's local context, Agda's
`Closure`, or Idris's `mkClosedElab` do. Three facts make the snapshot unnecessary
[inferred, from the code read]:

1. **Queueing happens before the item does anything.** Q1 is decided at the literal's head,
   before any field is checked. Q2 is decided after the receiver is elaborated, and the item
   *keeps* the receiver's term and type rather than redoing it. Lean needs `s.restore` when
   postponing (`TermElabM.lean:1678-1700`) because its elaborators may throw after doing work,
   and because it re-elaborates from the syntax. This design does neither.
2. **Resuming happens only when the blocker is solved.** So the head test that queued the item
   passes, and nothing is tried and rolled back. A sub-piece that is still stuck becomes a new
   item, not a failure to undo. Lean's `resumePostponed` saves state because it resumes items
   that may postpone again at the same point (`SyntheticMVars.lean:34`, `:62-71`).
3. **A failure at resume is final for the pass** ([§5.5](#55-how-a-late-failure-is-reported-p2)).
   There is nothing to restore, because the pass is discarded.

Attempts *around* an item still use snapshots, and those now truncate the queue too
([§5.2](#52-where-the-queue-lives-and-when-it-is-used)). Today's in-place lambda try keeps its
snapshot (`check.rs:1945`, `:1960`), since it tries first. That is why it isn't a queued item
in stage 1.

### 5.7 `let`: body first, for what is stuck (SW-847)

In the second pass, `pure_let` still infers the value first. When `item.value` is reached with
`item : ?B` unknown, it becomes a Q2 item and the lambda's body type is the placeholder's type.
The lambda's type `(?A, ?B) → ?R` is defined as `counted`, the body `List.sumBy pairs counted`
unifies the parameter with `(Nat, Item)`, and the ladder then resumes `.value` with `?B =
Item` [inferred]. So the part of the value that needs the body is elaborated after the body,
which is the body-first order SW-847 needs, and the rest keeps today's order. The let stays
transparent: the body sees `counted`'s value, with the placeholder in it.

The alternative is Lean's `let_delayed`: elaborate the whole value after the body, with the
value an unknown while the body is checked (`Binders.lean:779-782`, `:848-856`). That loses
transparency for the body. A proof in the body that unfolds `counted`, as day 3's
`enabledResultsByIndex` does (`aoc/src/Aoc/Year2024/Day03/Proofs/Proofs.sw:64-68`), would meet
an unknown where today it meets a lambda. D2011 recommends the queued field access.

Method sections bound by `let` (`let g := .drop 1; g xs`) work the same way through Q3. That
accepts `examples/reject/section-unknown-receiver.sw`, whose comment says "A `let` gives it
nothing to go on" [inferred]. D2011 covers that change.

### 5.8 Record literals, and today's argument postponement, as instances

- **SW-817.** A literal at `?b` (foldLeft's accumulator):
  1. SW-805's rule runs first (D1991). If exactly one record type in scope has exactly these
     fields, that type is used, with no queue. This covers AoC day 3.
  2. Otherwise, in the second pass, it is Q1 on `?b`. `step : Tally → Nat → Tally` solves `?b`
     and the ladder checks the literal against `Tally`.

  This is Agda's `guessRecordType` order: none, one, several (`Term.hs:1177-1215`).
- **SW-885.** This has two parts:
  - **Stage 0, no queue.** Pass the known type on. `run_argument` gives `param` to the literal
    (`comp_check` instead of `comp_infer`), and `comp_compound`'s `part` gives each field's or
    component's type from `expected` when that is known. That fixes `inArgument`, `inTuple`
    and `nested` [inferred; `param` is computed at `effects.rs:3161` from `call_param_types`].
    To keep stage-1 identity, only a part that today goes to `infer` and would raise
    `check.rs:1356` is given the type: a record literal without a base, directly or as a
    tuple's, list's or record's part.
  - **`generic`** (the parameter type is `a`) is Q4.
- **Today's argument postponement** is the same item at a smaller scope: a placeholder, a
  saved check, and a resume point at the end of `apply_args_postponing` instead of the end of
  the declaration. Stage 2 re-expresses it with the shared item type and resume function, and
  keeps its scope, order and in-place try, so its hashes are unchanged. It doesn't move it to
  the declaration queue. In the second pass a lambda's stuck `.field` is already a Q2 item, so
  the lambda checks in place and the application-level postponement is rarely reached
  [inferred].

## 6. Risks

- **Identity in stage 1 rests on one property.** The first pass must be today's elaborator,
  bit for bit: `queueing` off must mean no queued item is ever created and no new code runs on
  the success path. The hash snapshots test this ([§8](#8-tests)). The cost of the counter
  that decides whether to run pass 2 is one increment per raise.
- **The second pass doubles the work on failing declarations.** That matters most in the
  language server, where code is often broken. The pass runs only after a queueable raise
  (6 of 686 reject examples), and `with_local_retries` already pays this for local
  definitions.
- **Placeholders in lifted helpers.** A queued item inside a `match` arm or local definition
  that is drafted for lifting must be resumed and filled before `lift`
  ([§5.4](#54-resume-order-and-why-it-stops)). The one place this is ordered by hand
  (`lifted_body`, `lib.rs:2256-2260`) is in stage 1. Others stay without a second pass until
  they are checked.
- **Order-dependence returns in the second pass.** Which unknown a resumed item solves first
  depends on queue order. Creation order is deterministic but not principled, unlike OmniML.
  SW-859 showed the argument-order version of this.
- **Errors at the end of a declaration.** Not in stage 1, which reports the first pass's
  error. The later P2 step must keep the span and type of each item.
- **A Q2 item keeps a receiver elaborated under assumptions that may change.** For example,
  implicit arguments inserted for dot-call placement are inserted before the type is known.
  Agda's `CheckProjAppToKnownPrincipalArg` carries metavariables for this (`patm`,
  `Application.hs:1470-1474`). This needs care in the Q2 resume code [inferred].
- **Interaction with SW-805.** SW-805 must stay a name rule (D1991's assumption R1). If it
  started to look at inferred types, it would need to run in the ladder, and its result would
  depend on order.

## 7. Stage plan

**Stage 0: SW-885's known types** (small, no queue). Pass the known parameter, field or
component type to a record-literal part in `run_argument` and `comp_compound`
([§5.8](#58-record-literals-and-todays-argument-postponement-as-instances)). Accepts sw885's
`inArgument`, `inTuple` and `nested`.

**Stage 1: the queue, second pass only.**
1. First commit: no behaviour change. Add rogue to the hash `dump` (`hash_stability.rs:337-350`
   loads only aoc after the library), and take `HASH_DUMP` of std, aoc and rogue on main.
2. Add the queue table, its `Snapshot`, `clear_metas` and `rewind` handling, the `queueing`
   flag, the raise counter, and the second pass in `with_local_retries`.
3. Add Q1-Q4 at their four sites, under `queueing`. Add the ladder step in the
   obligations loop and before `lift`.

The newly accepted programs are the four repros and one reject example,
`section-unknown-receiver.sw`, predicted by reading [inferred]. Any other change is a bug to
look at. The other five `E-CANNOT-INFER` reject examples on queue sites never get the unknown
fixed, so they stay rejected with the same diagnostic.

**How stage 1 is shown to elaborate every accepted program identically:**
- `task snap:hashes` leaves the `prelude`, every `examples/accept` and `examples/extract`
  file, and every `project-*` snapshot unchanged (`hash_stability.rs`, `prelude`, `examples`,
  `projects`).
- `HASH_DUMP` for std plus aoc, and the new rogue dump, are byte-identical before and after
  (`diff` empty).
- Every `examples/reject` file other than `section-unknown-receiver.sw` gives the same error
  code. Since the first pass's diagnostic is returned, the error-message snapshots are
  unchanged too (`task snap:examples` writes no new snapshot).
- AoC answers are unchanged (`task test:aoc`).
- The argument for why it holds is in [§5.2](#52-where-the-queue-lives-and-when-it-is-used)
  and the first risk in [§6](#6-risks). The tests are what show it.

**Stage 2: one mechanism.** Re-express the lambda, section, literal and after-expected
postponement of `apply_args_postponing` as queue items with application scope. This is a pure
refactor, gated on the same hash and error checks.

**Stage 3 (each needs its own decision later):**
- report a resumed item's own error at its span (P2, [§5.5](#55-how-a-late-failure-is-reported-p2));
- add the remaining `finish` callers to the second pass;
- measure whether a single pass is ever acceptable. That needs the hash corpus to stay
  unchanged with `queueing` on in pass 1, which today's 1,073 caught raises make unlikely.

## 8. Tests

- **Repros become examples.**
  - `examples/accept/postpone-record-literal-argument.sw` (sw817 with `Tally` and `Score`);
  - `postpone-let-lambda-field.sw` (sw847);
  - `postpone-effectful-record.sw` (sw885's four cases, the first three from stage 0);
  - `postpone-section-let.sw` (`section-unknown-receiver.sw`, moved).
- **Reject examples that pin stage 1's error rule:**
  - a queued literal never fixed: `record-literal-without-type.sw`, unchanged;
  - a queued literal whose type is fixed to a non-record, reporting the first pass's
    `E-CANNOT-INFER` (not `E-NOT-A-RECORD`);
  - a queued `.field` whose type becomes a record without that field, again reporting the
    first pass's error.
- **Unit tests in `crates/elab`:**
  - `Snapshot::restore` drops items queued after it;
  - `rewind` empties the queue;
  - with `queueing` off, no item is created;
  - a declaration that pass 1 accepts never enters pass 2.
- **The hash and error checks of [§7](#7-stage-plan)** for stages 1 and 2.
- **AoC.** Remove day 3's annotation at `Proofs.sw:64` as a check, and the `: Position`
  annotations SW-885 mentions in day 14's grammar.
- **A pass-2 counter.** Report it in `STITCHWORT_TIMINGS`, beside `instance_waits`, so P1
  stays measured.
- Lane tier for the stage work, then the merge tier at merge.

## 9. Decisions for Matt

**D2010. Build stage 1 as a second pass?** In stage 1, a declaration that fails after raising
a queueable `E-CANNOT-INFER` is elaborated once more with the queue on. If that fails too, the
first pass's diagnostic is reported. This is instead of Lean's single pass, where the queue
replaces the errors directly. **[Recommend yes.]** The assumptions, in full:
- **(A1)** A declaration that the first pass accepts never enters the second pass, and the
  first pass with `queueing` off runs exactly today's code. So no accepted program's terms or
  hashes can change. The hash snapshots, the aoc/std dump and the new rogue dump test this.
- **(A2)** The second pass is needed rarely. It runs only for declarations that fail after a
  queueable raise: in this corpus, 6 of 686 reject examples and nothing accepted
  ([§4](#4-p1-how-often-postponement-is-needed)).
- **(A3)** Elaborating a failing declaration twice is affordable, including in the language
  server, as `with_local_retries` already does for local definitions.
- **(P3)** A queued item decides to wait before it elaborates anything, or keeps what it
  elaborated (Q2's receiver). It is resumed only once its blocker is solved. A failure at
  resume ends the pass. So queued items need no snapshot, and the snapshots of attempts around
  them truncate the queue.

The alternative, a single pass, changes the route at the 1,073 raises that accepted code
depends on today. It would need every hash re-examined.

**D2011. Fix SW-847 by queueing the stuck field access inside the let-bound value?** The value
stays elaborated first, as today, and the queued `.value` is resumed after the body has fixed
the lambda's parameter type. This is instead of a body-first `let` (Lean's `let_delayed`,
where the whole value waits for the body). It also accepts a let-bound method section
(`section-unknown-receiver.sw` moves to accept). **[Recommend yes.]** The assumptions, in
full:
- **(B1)** The body's use of the let-bound name fixes the lambda's parameter types by
  unification, as it does today for let-bound lambdas (SW-509, `parameter_metas`).
- **(B2)** The body seldom needs to compute with the part of the value that is queued. Where it
  does (a proof that unfolds the name before the queued piece is resumed), the comparison
  fails as it would today, and the first pass's error is reported. So nothing accepted or
  reported gets worse, by D2010's A1.
- **(B3)** A `let` stays transparent for the body. A body-first `let` would hide the whole
  value from the body while the body is checked, as `let_delayed` does.

## Sources

Fetched 30 October 2026 with `gh api` into the lane's scratch directory, read as text. Line
numbers are of those copies. WebSearch was not used.

**Lean 4**, `leanprover/lean4` at `0f852cc822d54d32c5cb0ef158562796088ce4dc` (as in
docs/research/elaboration.md):
- [L1] `src/Lean/Elab/SyntheticMVars.lean`, whole file (743 lines);
- [L2] `src/Lean/Elab/Term/TermElabM.lean`: `SavedContext`, `SyntheticMVarKind`, `Context`,
  `tryPostpone*`, `saveContext`, `postponeElabTermCore`, `postponeElabTerm`,
  `elabUsingElabFnsAux`, `elabTermAux` (lines 40-120, 300-315, 860-875, 1365-1470,
  1650-1710, 1940-1970);
- [L3] `src/Lean/Elab/App.lean`: `synthesizePendingAndNormalizeFunType` (360-380), `ElabElim`
  argument loop (1290-1320), `resolveLValLoop` (1670-1700), overload filtering (2170-2210);
- [L4] `src/Lean/Elab/Binders.lean`: `elabFun` (678), `elabLetDeclAux` (735-860),
  `let_delayed` (951-952);
- [L5] `src/Lean/Elab/MutualDef.lean`: lines 262-275, 1395-1406;
- [L6] `src/Lean/Elab/StructInst.lean`: lines 1355-1366 (by grep for `postpone`).

**Agda**, `agda/agda` at `df8c38856ecce561ef8fd0834755c46a6d397a0a`:
- [A1] `src/full/Agda/TypeChecking/Monad/Base.hs`: `ProblemConstraint`, `Constraint`
  (1655-1712), `MetaInstantiation` (1990-1994), `TypeCheckingProblem` (2058-2086);
- [A2] `src/full/Agda/TypeChecking/MetaVars.hs`: `postponeTypeCheckingProblem_`,
  `postponeTypeCheckingProblem`, `problemType` (614-671);
- [A3] `src/full/Agda/TypeChecking/Constraints.hs`, whole file (389 lines);
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
- [I4] `src/TTImp/Elab/Record.idr`: `checkUpdate` (240-260). Users of
  `delayOnFailure`/`delayElab` (`Ambiguity.idr`, `Case.idr`, `Lazy.idr`, `Rewrite.idr`) were
  found by code search, not read.

**Rocq**, `rocq-prover/rocq` at `3fb9a904fc271e9fbe15f3bdcfdc13e008ed8794`:
- [R1] `pretyping/pretyping.ml`: bidirectionality hints (56-70), `solve_remaining_evars_from`
  and the checks (300-462), application pretyping (1050-1215);
- [R2] `pretyping/evarconv.ml`: `flex_rigid`'s comment (900-920), 985-1015, 2040-2165;
- [R3] `engine/evd.ml`: `conv_pbs`, `add_conv_pb` (496, 924-928, 971-983);
- [R4] `interp/constrintern.ml`: `sort_fields` (1563-1600).

**OmniML**:
- [O1] O'Brien, Rémy, Scherer, *Omnidirectional type inference for ML: principality any way*,
  arXiv 2511.10343v2, PDF via `pdftotext`. Read: §2.1, §2.4, §2.5, §3.2 (closed-world
  records), §4.1 opening, §6, §7. Not read: the rest of §3-§5 and the appendices.

**Not verified**: which unification problems Rocq's `evarsolve.ml` and `cases.ml` postpone;
the Idris `delayOnFailure` users other than records; Lean's anonymous-constructor elaborator
(only the ladder's comment about `⟨1, 2⟩` was read, `SyntheticMVars.lean:646-659`).

**Stitchwort**, at `bc0802eb`:
- docs/research/elaboration.md §1, §4 (C1, C7, C8, C15), §5.1, §8;
- `crates/elab/src/check.rs`: `Ctx`, `apply_args_with`, `retrying`, `apply_args_postponing`,
  the record and `rfl` arms of `infer`, `append`;
- `unify.rs` (header, `run`);
- `effects.rs`: `pure_let`, `settle_let_lambda`, `comp_app`, `run_first`, `run_argument`,
  `call_param_types`, `passed_parts`, `comp_compound`;
- `records.rs` (`record_type`, the pattern error); `dot.rs` (`find_in_view`,
  `section_unknown`);
- `lib.rs` (`finish`, `clear_metas`, `with_local_retries`, `lifted_body`, the zonk errors);
- `auto.rs` (`solve_obligations_until_stuck`); `rows.rs` (`postpone`); `undo.rs`
  (`Snapshot`); `rewind.rs` (header);
- `crates/driver/tests/hash_stability.rs`;
- the board tickets SW-509, SW-805, SW-817, SW-847 and SW-885;
- docs/proposals/direct-style-grammars/gaps.sw.
