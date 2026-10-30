# Review brief: one postponement queue for Stitchwort's elaborator

*For an outside reviewer. Everything needed is on this page; no access to the code is assumed.
Written 30 October 2026. Every Stitchwort example below was run, and its output is shown as
printed; anything not run or not checked is marked **[unverified]**.*

We would like an expert opinion on a design for postponing checks in a bidirectional
elaborator for a dependently typed language. The questions we most want answered are in
[the last section](#what-we-would-like-you-to-answer). The rest gives what is needed to answer
them: the language, the problem, what four other systems do, the proposed design, a
prototype's measurements, and the plan.

## Stitchwort in brief

### What it is

Stitchwort is a dependently typed functional language implemented in Rust. Programs use
algebraic data types, natural numbers and lists, records, algebraic effects (called
*abilities*) with handlers, and proofs about all of these. It is used for Advent of Code
solutions with machine-checked proofs of their correctness, and for a small roguelike game.

Two parts of the implementation matter here:

- **The kernel** (`crates/core`) is a small type checker for the core language (dependent
  functions, inductive types, equality, universes). It checks finished terms and does no
  inference.
- **The elaborator** (`crates/elab`) turns surface syntax into kernel terms: it fills in
  implicit arguments and types, resolves dot notation, compiles pattern matching, translates
  effects into ordinary data, and so on. **Everything the elaborator produces is re-checked by
  the kernel.** So an elaborator mistake can produce a confusing error or reject a good
  program, but it can't make the system accept a false theorem. The design under review is
  entirely inside the elaborator.

### What the elaborator does

- **Bidirectional checking.** Each expression is either *checked* against a known type or has
  its type *inferred*. A function application infers the function's type, then checks the
  arguments against the parameter types, left to right.
- **Unification with metavariables.** An unknown type or term is a metavariable, called an
  *unknown* in the code and messages. Unknowns are solved by higher-order pattern unification
  (an unknown applied to distinct variables). The unifier answers *yes* or *no* at once: inside
  one call it may put a pair aside and look at it again after the rest of the call, but nothing
  outlives the call. Callers branch on the answer.
- **Implicit arguments.** A lowercase name used only as a type in a signature is bound as an
  implicit parameter, filled in by unification at each call.
- **Records and dot notation.** `p.x` looks `x` up in the namespace of `p`'s type: a record's
  field, or any function `T.x` whose first explicit parameter is a `T`. So `.x` needs the head
  of `p`'s type to be known when `p.x` is reached.
- **Per declaration.** Unknowns, pending instance searches and other waiting work are kept per
  top-level declaration, and all must be solved when the declaration ends. Attempts that may
  fail run inside a *snapshot*: on failure, every unknown solved and every table entry added
  since the snapshot is undone.

### Enough syntax to read the examples

```
import Std (Bool, List, Nat)

-- A record type, a record literal, and `.field`.
type Point = { x: Nat, y: Nat }

def origin: Point := { x = 0, y = 0 }

def shift (p: Point) (dx: Nat): Point := { x = p.x + dx, y = p.y }

-- `a` is used only as a type, so it is an implicit parameter, filled in
-- at each call by unification: here `a` is `Point`.
def twice (f: a -> a) (v: a): a := f (f v)

def moved: Point := twice (p => shift p 1) origin

-- `let`: the value is inferred, then the body is checked.
def area (p: Point): Nat :=
  let w := p.x
  w * p.y

def apply (f: a -> b) (v: a): b := f v

-- `.field` on a parameter whose type is unknown where it is reached: the
-- lambda is tried in place, fails, and is checked again after `p`.
def xOf (p: Point): Nat := apply (q => q.x) p

test "moved twice" := moved.x == 2

test "area" := area { x = 3, y = 4 } == 12

test "xOf" := xOf moved == 2
```

`stitchwort test` on this file prints:

```
  ✓ moved twice  ran
  ✓ area         ran
  ✓ xOf          ran
3 test(s): 3 passed, 0 failed (0 from the cache)
```

- `def name (param: Type): Result := body` defines a function; `type` declares a data type or,
  with braces, a record.
- `{ x = 1, y = 2 }` is a record literal. It has no type name in it: its type comes from where
  it is used. When nothing says, a rule from another ticket (SW-805) picks the one record type
  in scope whose fields are exactly the literal's, if there is exactly one.
- `x => body` and `(x, y) => body` are lambdas; `(x: T) => body` annotates the parameter.
- `.f` on its own (`xs.map .name`) is a *method section*, short for `x => x.f`.
- `test "…" := expr` is a check run by `stitchwort test`.

### What `E-CANNOT-INFER` means

It is the elaborator's error for "I need to know a type here, and nothing has said it yet". It
names the construct and suggests an annotation:

```
import Std (Nat)

type Point = { x: Nat, y: Nat }

def getX: Nat :=
  let g := p => p.x
  g { x = 1, y = 2 }
```
```
[E-CANNOT-INFER] Error: can't tell what `p` is, so can't look up `.x`
    ╭─[ docs/proposals/postponement/brief-cannot-infer.sw:12:17 ]
    │
 12 │   let g := p => p.x
    │                 ─┬─
    │                  ╰─── its type isn't known yet here
    │
    │ Note: `.x` is looked up in the namespace of the value's type, so that type must be known where it's used: annotate it, as in `(p: Person) => p.x`, or write the function's full name
────╯
```

The use `g { x = 1, y = 2 }` on the next line would say what `p` is, but `.x` is looked up while
the `let`'s value is inferred, before the body is reached.

### The postponement Stitchwort has today

All of it is local to one function application, and all of it works by *catching an error and
trying again*:

1. **Lambda arguments.** A lambda argument whose parameter type is still unknown, with explicit
   arguments after it, is tried in place inside a snapshot. If that fails (with any error), the
   snapshot is restored and the lambda is checked after the later arguments, which may have
   fixed its parameter type. This is how `apply (q => q.x) p` above works.
2. **Method sections** in that position are put after the later arguments without a try.
3. **After the expected type.** Where the application's own expected type is known, a lambda or
   argument that fails in place is checked again after the application's result type has been
   compared with it. In practice this serves proofs found by search from a goal (linear
   arithmetic, rewriting) that only the expected type fixes, much as Rocq's bidirectionality
   hints do.
4. **Number literals.** A literal checked against an unknown type becomes `Nat` at once. If the
   application then fails, it is elaborated a second time with constructors holding number
   literals checked last (`retrying`).
5. **Record literals in comparisons.** In `a == b`, `a ++ b` and `calc`, the first part is
   inferred with SW-805's field-name rule *held back*, so a literal there fails with
   `E-CANNOT-INFER` and the other part is inferred instead and gives the type. If the whole
   construct still fails, it is elaborated again with the rule released (`last_resort`).

Measured over the whole corpus (the standard library, 374 accepted and 687 rejected examples,
the Advent of Code project and the roguelike), these paths fire 100, 46, 233, 19 and 5 times
respectively. The sites that a queue would replace raise and recover `E-CANNOT-INFER` 1,073
times while elaborating code that is finally accepted.

## The problem

`E-CANNOT-INFER` stops a declaration whenever a construct needs a type that a *later* part of
the declaration would fix, unless the construct happens to be a lambda argument (path 1). Three
tickets show it. Each output below is today's.

**A record literal as an argument, typed only by a later argument** (SW-817):

```
type Tally = { enabled: Bool, total: Nat }

type Score = { enabled: Bool, total: Nat }

def step (tally: Tally) (n: Nat): Tally := { enabled = tally.enabled, total = tally.total + n }

def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total
```
```
[E-CANNOT-INFER] Error: can't tell which record type this literal is
    ╭─[ docs/proposals/postponement/sw817.sw:22:47 ]
    │
 22 │ def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total
    │                                               ──────────────┬──────────────
    │                                                             ╰──────────────── nothing here says what type it should have
    │
    │ Note 1: add a type annotation, as in `({ x = 0, y = 0 }: Point)`
    │
    │ Note 2: more than one record type has exactly these fields: `Tally`, `Score`
────╯
```

`foldLeft`'s accumulator type is an implicit parameter, unknown when the literal is reached;
`step`, the next argument, says it is `Tally`.

**`.field` inside a let-bound lambda** (SW-847):

```
type Item = { value: Nat }

def total (pairs: List (Nat, Item)): Nat :=
  let counted := ((index, item)) => if index < 3 then item.value else 0
  List.sumBy pairs counted
```
```
[E-CANNOT-INFER] Error: can't tell what `item` is, so can't look up `.value`
    ╭─[ docs/proposals/postponement/sw847.sw:15:55 ]
    │
 15 │   let counted := ((index, item)) => if index < 3 then item.value else 0
    │                                                       ─────┬────
    │                                                            ╰────── its type isn't known yet here
    │
    │ Note: `.value` is looked up in the namespace of the value's type, so that type must be known where it's used: annotate it, as in `(p: Person) => p.value`, or write the function's full name
────╯
```

The same lambda written directly as `List.sumBy`'s argument is accepted, by path 1.

**A record literal with an effectful field** (SW-885). `shortNumber()` reads digits in the
`Parse` ability; `Position` and `Size` both have fields `x` and `y`:

```
def usePosition (p: Position): Nat := p.x

def inArgument(): {Parse} Nat := usePosition { x = shortNumber(), y = 0 }
```
```
[E-CANNOT-INFER] Error: can't tell which record type this literal is
    ╭─[ docs/proposals/postponement/sw885.sw:27:46 ]
    │
 27 │ def inArgument(): {Parse} Nat := usePosition { x = shortNumber(), y = 0 }
    │                                              ──────────────┬─────────────
    │                                                            ╰─────────────── nothing here says what type it should have
    │
    │ Note 1: add a type annotation, as in `({ x = 0, y = 0 }: Point)`
    │
    │ Note 2: more than one record type has exactly these fields: `Position`, `Size`
────╯
```

Here the parameter type *is* known, but effectful arguments run first, each bound to a fresh
variable, and the part bound is inferred, not checked. The same file has the literal as a tuple
part, as a nested field, and as an argument of a generic function (`firstOf (x: a) (xs: List a)`),
all with the same error.

A fourth shape is the method section in a `let`: `let g := .drop 1; g xs` is
`E-CANNOT-INFER` ("can't tell what `.drop` is applied to").

## How other systems do it

From the source of each system at a pinned commit (Lean 4 `0f852cc8`, Agda `df8c3885`, Idris 2
`c35a6bd1`, Rocq `3fb9a904`) and from the OmniML paper (O'Brien, Rémy, Scherer, *Omnidirectional
type inference for ML: principality any way*, arXiv 2511.10343v2). File and line references are
to those versions.

**Lean 4.** An elaborator that needs an unknown expected type throws a *postpone* exception;
the caller restores the state saved before it ran and records the syntax as a synthetic
metavariable with its saved context (`Elab/Term/TermElabM.lean:1374-1415`, `:1678-1701`). Sites
include structure instances, `.field` on an unknown type (`resolveLValLoop`, `Elab/App.lean`)
and anonymous constructors; `fun` is never postponed. `synthesizeSyntheticMVars`
(`Elab/SyntheticMVars.lean:638-672`) is a ladder: resume pending items in creation order while
one makes progress; then resume with postponing off, errors postponed; then **default
instances**, by descending priority, one at a time (`:237-243`), with the numeral default
`OfNat Nat` at low priority (`Init/Prelude.lean:1411`); then resume with errors reported; then
tactics. It runs at the end of each definition and at nested `withSynthesize` points, which save
the pending list, handle only what was created inside them, and put the rest back
(`:689-720`). Nothing stays stuck: the last step commits or fails. Errors are reported at the
postponed syntax against the type as now known.

**Agda.** A postponed check is a metavariable whose instantiation is a closure of the problem,
with an `UnBlock` constraint under a *blocker* (`TypeChecking/MetaVars.hs:629-661`). When a
blocking metavariable is solved, `wakeupConstraints` wakes what was waiting on it
(`TypeChecking/Constraints.hs:246-251`). A record expression at an unknown type finds every
record type with at least its fields: none is an error, one commits, several postpone
(`Rules/Term.hs:1177-1215`). A projection keeps its already-checked principal argument
(`CheckProjAppToKnownPrincipalArg`). Unsolved constraints are reported at the end of the module.
There is no defaulting.

**Idris 2.** Elaborators wrapped in `delayOnFailure` run first and are delayed on a matching
error; delayed elaborators are closed over their environment and kept in the unifier state
(`TTImp/Elab/Delayed.idr`, `Core/UnifyState.idr:102-107`). At the end of a term they are retried,
sorted by a reason chosen "to give the most likely useful error messages first", while some
succeed, then once more reporting all errors.

**Rocq.** No syntax is postponed, except, within one application, the arguments after a
user-written bidirectionality hint, which are checked after the application's type has been
coerced to the expected type (`pretyping/pretyping.ml:1057-1120`). Unification problems are
postponed and retried with heuristics. Record syntax is resolved by its first field's name
before typing.

**OmniML.** Any construct that needs a type's shape (record labels, polytypes) is a suspended
match constraint on one type variable, held in that variable's wait list and scheduled when the
variable is unified (§2.4, §4.1, §6). The result doesn't depend on the order. A match
constraint never discharged is unsatisfiable. Record literals use a closed-world rule: the
labels must exactly match one record type's (§3.2), which is Stitchwort's SW-805 rule.

## The proposed design

**One queue of suspended checks per declaration, used in the single elaboration pass.**

### What is queued

A construct that needs the *head* of a type that is still an unknown doesn't fail. It puts a
fresh *placeholder* unknown in the term, and a queued check holding: what to elaborate, with
anything already elaborated (a `.field`'s receiver is kept, as in Agda); its *blocker*, the
unknown at the head of the type it needs; the whole local context, saved; the error its site
would raise today; its span.

| kind | queued instead of | blocker | resumed as |
|---|---|---|---|
| K1 record literal | `E-CANNOT-INFER` for a literal at an unknown type | the expected type | the literal checked at the type now known |
| K2 `.field` or dot call | `E-CANNOT-INFER` when the receiver's type is unknown | the unknown met while finding the namespace | the lookup and call, with the kept receiver |
| K3 method section | today's untried section postponement, and its `E-CANNOT-INFER` | the section's parameter type | `x => x.f …` with `x : ?D` and a K2 body |
| K4 number literal | today's immediate `Nat` | the expected type | the literal at the type now known |

A lambda is never queued as a whole: it is always checked in place, and whatever in its body
needs its parameter's type is a K1-K4 item. Effectful parts need nothing new: the effect
translation already binds the part and infers a pure literal, which is a K1.

### Where it lives and how items wait

The queue is a per-declaration table, beside the pending instance searches, cleared when a
declaration starts. A snapshot records the number of items *and* the length of a log of which
items have been resumed, and restoring truncates both; so an attempt that is undone takes back
both the items it queued and the resumptions it made. Items are indexed by blocker, so a resume
point looks only at items whose blocker has been solved since the last point (OmniML's wait
lists, with the declaration as the store).

### When items resume, and in what order

Resume points:

- **W1, the end of each application**, after its arguments and before its type is compared
  with the expected type, for **only the items created during that application** (Lean's
  `withSynthesize`);
- **W2, before local `match`es and local definitions are lifted** to top-level helpers;
- **W3, each round of the pending-instance loop**;
- **W4, the end of the declaration.**

At each point, a ladder:

1. resume, in creation order, every item in scope whose blocker is solved, filling its
   placeholder with the checked term; repeat while any resumed;
2. run a round of instance search and effect-row constraints; if anything was solved, go to 1;
3. (W4 only) apply **one default**, by priority then creation order: (1) SW-805's field-name
   rule for a waiting record literal, (2) `Nat` for a waiting number literal; if one applied, go
   to 1;
4. (W4 only) if anything is still waiting, report the first such item's error: the error its
   site raises today.

Resume points are fixed places rather than the moment a blocker is solved, because the unifier
is a pure function of the global state, called from dozens of places that branch on its answer;
waking an item from inside it would elaborate syntax in the middle of a comparison.

**Termination** (argued, not proved): a K1 resumes at a known type and never re-queues itself;
a K2 re-queues only at a strictly later step of its receiver's type-unfolding, which is finite;
new items come only from elaborating syntax nodes of the declaration, at most once per node per
surviving attempt; returns from step 2 follow a solved unknown; each default resolves one item
and solves at least one unknown; and nothing in the ladder takes a snapshot. A step budget
remains the backstop.

### What goes away

The lambda try-then-postpone (path 1), the untried section postponement (2), `retrying` (4),
and SW-805's hold-back and rerun (5), with the three places that infer one side and, on
`E-CANNOT-INFER`, infer the other. Path 3 (after the expected type) stays: it is about which
goal a proof search sees, not about an unknown type.

### SW-805's rule becomes a default

The field-name rule still looks only at the literal's field names and the names in scope, but
it runs at step 3, not at the literal. Then every other part of the declaration has had its
chance to say the type, which is what the hold-back machinery of path 5 approximates for three
constructs. It also means number literals must default in the same ladder, after it: see the
measurements.

### Errors

A stuck item reports exactly today's error. A resumed item that fails reports its own error at
its own span, against the type now known (as Lean does).

## What the prototype measured

A prototype behind an environment variable queues K1 and K2 (not yet K3 or K4), with resume
points W1-W4 and the field-name rule as the only default. It was run over the standard library,
every example (321 accepted, 687 rejected, 53 extraction), the Advent of Code project and the
roguelike, with the switch off and on, comparing every declaration's content hash, every file's
errors and the CPU time. It was run with W1 both scoped (as proposed) and unscoped; the results
below are the scoped ones unless said, the hash and error-message results are the same either
way, and the CPU times are from the unscoped runs.

**The three tickets.** All three files are accepted, and copies with tests compute the right
values: `total [1, 2, 3] == 6`; `total [(0, { value = 5 }), (7, { value = 9 })] == 5`; and each of
SW-885's four functions, run on input digits, returns the number read.

**Acceptance.** One file changes: an accepted example becomes rejected.

```
test "in a list" := [{ row = 1, column = 2 }, { column = 3, row = 4 }].map (p => p.row) == [1, 4]
```
```
[E-TYPE-MISMATCH] Error: type mismatch
    ╭─[ examples/accept/record-literal-inferred.sw:20:82 ]
    │
 20 │ test "in a list" := [{ row = 1, column = 2 }, { column = 3, row = 4 }].map (p => p.row) == [1, 4]
    │                                                                                  ──┬──
    │                                                                                    ╰──── expected `Nat`, but this has type `Int`
────╯
```

`Position` has `Int` fields. The literals wait, `p.row` waits, `[1, 4]` is made `List Nat` at
once (number literals aren't queued yet), and only then does the field-name default make the
literals `Position`s. With K4 (numbers waiting, defaulted after the field-name rule), the order
would be: field-name default, then `p.row : Int`, then `1` and `4` as `Int` **[unverified: K4 is
not in the prototype]**.

Putting the field-name rule *at the literal* instead (Agda's order) fixes that test and breaks
two others in the same file, which is what the hold-back machinery exists for:

```
[E-TYPE-MISMATCH] Error: type mismatch
    ╭─[ examples/accept/record-literal-inferred.sw:33:31 ]
    │
 33 │ test "the other side says" := hidden 1 == Some ({ value = one })
    │                               ────┬───    ──────────┬──────────
    │                                   ╰────────────────────────────── expected `Option Cell`, but this has type `Option Hidden.Cell`
    │                                                     │
    │                                                     ╰──────────── this comparison is on `Option Cell` because of this
────╯
[E-TYPE-MISMATCH] Error: type mismatch
    ╭─[ examples/accept/record-literal-inferred.sw:35:40 ]
    │
 35 │ test "appended" := [{ value = 2 }] ++ [({ value = 3 }: Hidden.Cell)] == [{ value = 2 }, { value = 3 }]
    │                                        ──────────────┬─────────────
    │                                                      ╰─────────────── expected `Cell`, but this has type `Hidden.Cell`
────╯
```

(`Hidden.Cell` and `Cell` both have one field `value`; only `Cell` is in scope by its short
name.)

**Without scoping W1** (resuming every ready item at every application's end), one reject
example is also accepted:
`twice (c => c.size) (c => List.length c) (Counts.of 1)`, with `Counts` defined as `List Nat`
and a function `Counts.size`. Today it is rejected ("`List` has no field or function `size`").
Unscoped, the queued `c.size` is resumed three times: twice inside attempts that fail and are
undone, where `c : List Nat`, and once on the surviving route, where `c : Counts`. The program
is correct, and its test `a == 2` passes. With W1 scoped it stays rejected with today's error.

**Elaborated terms.** 26 declarations change hash, of the 23,213 declarations compared. The standard
library, the roguelike, the extraction examples and all but one accepted example are unchanged.
Seven declarations differ in their own term; the rest only refer to a changed one. Of the seven:

- five are **harmless**: a type annotation (`Ann`) wrapping one side of a comparison, in two
  tests; a motive solved to the goal as written instead of its unfolding; and, twice, a lambda's
  term as checked in place where today's term has a definitionally equal form (in one case the
  copy unification found from another definition; the other case is classified by analogy,
  **[unverified]** in detail);
- one is a **prototype bug the design excludes**: the placeholder was solved by unifying it with
  the checked term's *value*, and reading that value back unfolded a call
  (`Map.Spec.sameKey.%match1 (Position.%compare blocker other)` instead of
  `Map.Spec.sameKey blocker other`). The design fills the placeholder with the term itself;
- one is a **needed fix**: `rule.before == laterPage` now uses the generic decidable-equality
  dictionary where today's term has the specialised `Nat.decEq`, because the operator chose its
  form while the operand's type was a placeholder. The same value, a slower route.

All the changed declarations other than the two tests are proofs (theorems and their helpers),
re-checked by the kernel against their statements, and the statements (types) of all 26 are
identical with the switch off and on.

**Error messages.** No reject example's error changes (687 files).

**The catch-and-retry paths.** With K1 and K2 queued, the lambda try-then-postpone fires 8 times
(9 unscoped) instead of 100 (6 of them method sections, K3), and the rerun of path 5 fires 0
times instead of 5.

**Resume points.** With only W3 and W4, the standard library doesn't load:

```
[E-TYPE-MISMATCH] Error: type mismatch
      ╭─[ std/Map/Spec.sw:1862:96 ]
      │
 1862 │         (Eq.trans (Eq.cong (xs => List.last (List.filter xs (e => Map.Spec.isLess e.fst key))) h) (Eq.sym (Map.Raw.belowToList n key)))
      │                                                                                                    ────────────────┬────────────────
      │                                                                                                                    ╰────────────────── expected `List.last (List.filter (Map.Raw.toList n) (e => (match …) (Ord.%compare ord (?21 k v ord key m n h (Map.Raw.toList n) e) key))) = Map.Raw.below key n`, but this has type `List.last (List.filter (Map.Raw.toList n) (e => Map.Spec.isLess e.fst key)) = Map.Raw.below key n`
```

(shortened; `?21 …` is the placeholder for `e.fst`, still unfilled when `Eq.trans` compares
types). Without W2, a record literal holding a `match` is resumed after its declaration's
helpers have been lifted, and the AoC project fails.

**CPU time.** Single-threaded, two runs: the AoC project 38.0-38.3 s off, 35.9-36.0 s on (about
5% faster, from fewer failed attempts); everything else within noise. Peak memory was not
compared **[unverified]**.

**AoC answers and roguelike tests** with the queue on (W1 scoped): all 914 AoC tests and all 100
roguelike tests pass.

## The stage plan

Accepted programs may elaborate to different terms; every test, example outcome, AoC answer and
roguelike test must stay right.

1. The queue, the resumption log, resume points W1-W4 (scoped), placeholders filled by the term,
   the stuck report. Nothing queued yet, so nothing changes.
2. K1 and K2, with the field-name default. The ticket repros become examples; the one test above
   is annotated until stage 4.
3. K3, method sections.
4. K4, number literals, and the defaults ladder.
5. Remove the catch-and-retry paths, one commit each, each after its counter reads 0.
6. Later, each its own decision: report all stuck items; let unification wait on unknowns.

Each stage is checked by the full test suite, every example, the AoC answers and the roguelike's
tests, with every changed hash listed and classified.

## Risks and open questions

- **Order still matters.** The ladder is deterministic (creation order, priorities), but not
  order-independent as OmniML is, because defaults commit and unification answers at once. Both
  acceptance changes above are order effects.
- **Placeholders in comparisons.** A comparison that meets an unfilled placeholder fails rather
  than waits. W1 is enough for this corpus; new code may find cases it isn't.
- **Resumption inside attempts.** An item resumed inside an attempt that fails is undone and
  resumed again later. Correct, but it can change which route survives; scoping limits it.
- **Kept receivers.** A queued `.field` keeps a receiver elaborated before its type was known,
  with implicit arguments inserted under assumptions that may later be wrong. No case arose.
- **Several stuck items.** Today one error per declaration is reported; Lean and Idris report
  all.
- **Termination** is argued, not proved.

## What we would like you to answer

1. **Resume order and soundness of the result.** Is creation order within a scope, plus scoped
   resume points at the end of each application, a reasonable order? Are there programs where it
   gives a well-typed result that differs in meaning from what the programmer wrote (not merely
   a different but equal term), given that the kernel re-checks every term?
2. **Termination.** Is the argument above complete? In particular: can a resumed item that
   queues new items, together with snapshot restores inside resumed items, make the ladder loop?
   Is there a measure you would use instead?
3. **Unification.** Our unifier can't wait on an unknown; instead we resume early, at the end of
   every application. Is that a sound substitute in your experience, or will programs keep
   finding comparisons that meet a placeholder too early? Would you make stuck comparisons
   declaration-level constraints (as Agda does) before or after this queue?
4. **Defaults.** Is a field-name rule as the first default, and the `Nat` numeral default after
   it, the right order? Lean puts numerals at low priority; is there a case where a record's
   field-name default should wait for a number instead?
5. **Errors.** Should every stuck item be reported, or only the first? When a resumed item fails,
   is its own error (at its span, against the type now known) better than today's
   `E-CANNOT-INFER` at the same span, in your experience with Lean or Agda users?
6. **Scope at W1.** Lean's `withSynthesize` handles only the items created inside it. Is that the
   right rule for an application's end, or should an application also resume outer items whose
   blockers it solved?
7. **What we are unsure of:** whether checking every lambda in place, with no try-and-retry, will
   cost good error messages that today come from re-checking a lambda after the later
   arguments; and whether a kept `.field` receiver can carry implicit arguments that become wrong
   once the type is known.

---

*Sources: the design note `docs/proposals/postponement.md` (draft 2) in the Stitchwort
repository, and the system sources at the commits above. No web search was used for the
comparison; the sources were fetched from the projects' repositories.*
