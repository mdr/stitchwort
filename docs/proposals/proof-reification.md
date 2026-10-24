# Proof-only reification: letting proofs look inside a computation

Status: design note, 24 Oct 2026, for D1141 (d). Decided (Matt, 24 Oct
2026): all five decisions in §8 as recommended, renumbered D1144 to D1148
(surface form `match reify` with handler-style clauses; close the run-time
leak right after R1; any proof may use it; checked per declaration; keyword
`reify`). Stages R1 (SW-419) and R2 (SW-420) are built: see "As built (stage R1)" and "As built (stage R2)" after §8.

D1141 (d), as decided (effect-polymorphism.md §7, "After stage 1, first
part"): abilities stay on arrows, so a computation is passed as a thunk
`() -> {Fail} a`; proofs get an erased, proof-only `reify` or per-ability
eliminators to split on what a computation does; the runtime is not
committed to building trees. This note says how.

How claims are marked:

- **[checked]**: read in the source at `c68751ad` (`main`), with `file:line`.
- **[probe]**: I ran it with the release build of `main` from 24 Oct, 13:46
  (after the stage 1 merge). The probe files are in Appendix A.
- **[inferred]**: my reading, not tested.
- **[unverified]**: about another system, with no source found that says it.

## 1. The goal

A proof should be able to ask, of a thunk `t: () -> {Fail} a`: did it
finish with some `x`, or fail with some message `m`? And in each case, the
goal should become the goal for that case, so that the handlers in it
compute.

The motivating proof is SW-378's (errors.md §3.7):

```
theorem Fail.toResultMapIn (f: a -> {Fail} b): (xs: List a) ->
    Fail.toResult (() => xs.mapIn f) = Result.traverse (x => Fail.toResult (() => f x)) xs
```

Its `Cons x xs` step has to split on whether `f x` fails. Every lemma Fail.sw
has today avoids this: each handles a computation whose shape is known
(`Fail.need o msg` with `o` split, say), so it holds by `rfl`
(`crates/elab/src/std/Fail/Fail.sw:110-150`) **[checked]**.

Three things the design must not do:

1. **Expose rows.** A program can't build or take apart a row (D1122,
   `crates/elab/src/scope.rs:577-595`, `:1115-1129`) **[checked]**. The tree
   of a `{Fail} a` computation is `Comp (Plus Fail NoOp) (PlusRes Fail.res
   NoRes) a` (`crates/elab/src/effects.rs:190-205`) **[checked]**; none of
   that should appear in a proof.
2. **Add computation values to programs.** No `(c: {Fail} a)` binder, no
   `{Fail} a` as a type argument (the point of choosing (d) over (b)).
3. **Commit the runtime to trees.** Stage 4 (design F) may run `{Fail}`
   code as exceptions, CPS or evidence passing. Nothing a program can
   observe may depend on there being a `Done` or a `Call` at run time.

## 2. What the probes found

Two facts decide most of the design.

**Splitting already works, once the scrutinee is the tree.** A helper
`viewOf t := t ()`, typed over `Effect.Comp op res a` with `op` and `res`
inferred, gives the tree of a thunk. In a theorem, `match viewOf t with`
generalises `t ()` in the goal (the documented behaviour of an expression
scrutinee, `docs/syntax.md:1116-1124`) **[checked]**, and the `Done x`
branch of `Fail.toResultThen` (§3) closes by `rfl` **[probe, p1]**. The
`Call` branch's goal is stuck on `Fail.%elim (msg k => Err msg) stop …`,
where `stop: Fail` is the operation **[probe, p1]**.

**But a proof can't name the operation.** An ability's operations are
constructors named `Fail.%stop`, which source can't write, so that the name
`Fail.stop` is free for the operation itself
(`crates/elab/src/lib.rs:1154-1156`) **[checked]**. A pattern
`Call (L (Fail.stop msg)) rest` is a parse error ("`Fail.stop` is a
qualified name, which can't be used here"), and `stop msg` with the name
imported is too (lowercase is a variable) **[probe, p2]**. Writing the tree
type by hand fails earlier: `Effect.Plus Fail Effect.NoOp` is `E-ABILITY`,
"`Fail` is an ability, not a type or a value" **[probe, p0]**.

A third fact matters for §5:

**Programs can already look at the tree.** The same `viewOf`, used in a
`def`, makes `finishedNow (() => failing 0)` false and
`finishedNow (() => failing 3)` true, and both tests pass at run time
**[probe, p3]**. Nothing stops a program matching on `Effect.Comp`'s
`Done`/`Call`; only rows are internal. So "the runtime isn't committed to
trees" is not true today, with or without `reify`. No std or AoC program
does this: outside `core/Effect.sw` and `Effect/Laws.sw`, `Effect.Comp` is
named only in `examples/` (grep of `crates/elab/src/std`, `aoc`, `examples`)
**[checked]**.

## 3. Surface options

All three are shown on the same two proofs. `Fail.toResultThen` is the
sequencing law; `Fail.toResultMapIn` uses it.

```
-- Running `t`, then `k` on its result: fails as `t` does, or as `k` does.
theorem Fail.toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k (t ())) = Result.flatMap (x => Fail.toResult (() => k x)) (Fail.toResult t)
```

The statement needs nothing new: thunks and handlers only, as D1141 (d)
wants. Only the proof needs to look inside `t`.

### (i) A generic `Effect.reify`, returning a proof-only tree

```
theorem Fail.toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b): … :=
  match Effect.reify t with
    | Done x => rfl
    | Call (Fail.stop msg) rest => rfl
```

`Effect.reify t` is a term of some tree type, matched with `Done`/`Call`.

- *Naming operations.* `Call (Fail.stop msg) rest` has to mean
  `Call (L (Fail.%stop msg)) rest` plus an absurd `Call (R ()) _` for the
  closed row's end. So the elaborator has to rewrite `Call` patterns
  specially anyway: the injections are row structure (D1122).
- *Its type.* `Effect.reify t` is a term, so it has a type, and that type
  is shown in goals, `let`s and errors. It is exactly the computation type
  `{Fail} a` that (d) chose not to give a source spelling. Either we spell
  it (reopening D1134 in proof contexts) or messages print a type no one can
  write.
- *Continuations.* `rest` is a function returning a tree, which is again a
  computation value with that type.

So (i) brings back a little of option (b), only in proofs.

### (ii) Per-ability eliminators or views

Two forms.

*An induction principle over thunks*, written once per ability (or
generated):

```
theorem Fail.cases (motive: (() -> {Fail} a) -> Prop)
    (finished: (x: a) -> motive (() => x))
    (failed: (msg: Text) -> motive (() => Fail.fail msg)):
    (t: () -> {Fail} a) -> motive t

theorem Fail.toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b): … :=
  Fail.cases (t => Fail.toResult (() => k (t ())) = Result.flatMap (x => Fail.toResult (() => k x)) (Fail.toResult t))
    (x => rfl) (msg => rfl) t
```

- No rows, no tree, and it's proof-only by construction: its motive is a
  `Prop`, so it can only make proofs (`E-PROP-ELIM`, `docs/core.md:111`)
  **[checked]**.
- But the motive is written by hand: the whole goal again, with `t`
  abstracted. `match h: e with` was added to stop exactly this
  (calc-rewrite.md §8; `Bool.inspect` "asks for one", `docs/syntax.md:1130`)
  **[checked]**. In `toResultMapIn`'s step the thunk is `() => f x` and the
  goal contains `f x` deep inside a `mapIn` unfolding, so the motive would
  be long and fragile.
- Proving `Fail.cases` itself needs `t = (() => t ())`, which is function
  extensionality (`Quot.funext`, whose axiom is `Quot.sound`,
  `crates/elab/src/std/Effect/Laws.sw:3`) **[checked]**, plus the split of
  `t ()` that §2 shows can't be written today. So (ii) still needs (i) or
  (iii) underneath, in std.

*A view type*, `Fail.Outcome t` with constructors `finished x` and
`failed m`, matched as `match Fail.outcome t with`. Matching on it doesn't
generalise anything useful: the goal contains `t ()`, not `Fail.outcome t`
(`docs/syntax.md:1120`, occurrences are found by shape) **[checked]**. Each
branch would need an equation `t = (() => x)` and a rewrite, which again
needs function extensionality. Worse than `Fail.cases`.

### (iii) `reify` as a `match` scrutinee only, with handler-style clauses

`reify` isn't a term. It is a form of `match`, allowed only in proofs, whose
clauses are written like a handler's:

```
theorem Fail.toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k (t ())) = Result.flatMap (x => Fail.toResult (() => k x)) (Fail.toResult t) :=
  match reify t with
    | return x => rfl
    | Fail.stop msg, _ => rfl
```

- *Naming operations*: the way handlers already do (`| Fail.stop msg, k =>`,
  `Fail.sw:45-48`) **[checked]**. A reader who has written a handler can
  read this. The elaborator turns it into an ordinary generalised `match`
  on the tree `t ()`, with patterns `Done x` and `Call (L (Fail.%stop msg))
  rest`, and adds the absurd case for the end of the closed row itself.
- *No type to spell*: the scrutinee `t ()` is never a value the user sees;
  in each branch the goal has `Done x` or the failing `Call` in its place.
  This is what §2 found already works: the `Done` branch is `rfl`
  **[probe, p1]**, and the `Call` branch will be too once its operation is
  `Fail.%stop msg`, since `toResult`'s clause then takes its step
  **[inferred]** (as `Fail.toResultFail` holds by `rfl`, `Fail.sw:104`
  **[checked]**).
- *Continuations stay thunks*: in `| State.get (), k =>`, `k` has type
  `s -> () -> {State s} a`, a function returning a thunk (the elaborator
  binds `k` to `y => () => rest y`). So arrows-only holds even here. For
  `Fail` and `Abort`, `k`'s argument is `Empty`, so it's always `_`.
- *No equation form*: `match h: e with` gives `h: e = pattern`, but here
  both sides would be computations, whose type is the one (d) leaves
  unwritten. So `match h: reify t with` is refused with a note; the
  branches' goals already say what happened.

`Fail.toResultMapIn` under (iii), by induction on the list with the law:

```
theorem Fail.toResultMapIn (f: a -> {Fail} b): (xs: List a) ->
    Fail.toResult (() => xs.mapIn f) = Result.traverse (x => Fail.toResult (() => f x)) xs
  | [] => rfl
  | [x, ..xs] =>
    match reify (() => f x) with
      | return y => Eq.cong (Result.map (Cons y)) (Fail.toResultMapIn f xs)
      | Fail.stop msg, _ => rfl
```

In the `return y` branch, `f x` has become `Done y`, so the left side
computes to `toResult` of `Cons y` over the rest, and `Result.traverse`'s
`flatMap` (`crates/elab/src/std/Result/Result.sw:33`) **[checked]** computes
on `Ok y`; the induction hypothesis finishes it. Whether the two sides then
meet as `Result.map (Cons y)` of each, or need `Fail.toResultThen` on
`mapIn f xs` first, is **[inferred]**: the left side's tail is a `bind`
over an unknown `mapIn f xs`, so the step may be
`rewrite Fail.toResultThen (() => xs.mapIn f) (ys => Cons y ys) in …`. Either
way it is short, and each branch's goal is one the user can read.

### Other forms considered

- **`reify` only in std, lemmas for users** (the shape of (ii), built on
  (iii)): std proves `Fail.toResultThen`, `Fail.toOptionThen`,
  `Abort.toOptionThen`; users rewrite with them and never split. Good for
  most proofs, and it's what most users will use anyway. But a user's own
  ability (`Log`, `State`) would have no way in. Kept as D1144's option (b).
- **An `induction reify t` form** with an induction hypothesis per
  continuation: needed for abilities that resume (§4), not for `Fail`.
- **Opening up the old D1134 (c) trick** (helpers typed through
  `opsOf`/`resOf`): §2's `viewOf` is that trick, and it still can't name
  `Fail.%stop`. It also works in programs, which is the problem in §5.

### Recommendation: (iii)

`match reify t with` and handler-style clauses, allowed only in proofs, on
a thunk whose row is closed and lists abilities. It needs no new type, names
operations the way handlers do, keeps continuations as thunks, and reuses
the generalisation that `match` already does, which §2 shows works on the
tree. Std then proves the sequencing laws with it, so most users only
rewrite. (i) is the same machinery plus a type no one can write; (ii)
needs (iii) underneath and adds hand-written motives.

This is F\*'s division, in Stitchwort's terms: effectful code is abstract to
programs, and proofs reveal its representation. Ahman et al. say `reify`
"reveals the representation of an ST computation as a Pure function", used
for "extrinsic" proofs (POPL 2017, §2.4,
[ar5iv 1608.06499](https://ar5iv.labs.arxiv.org/html/1608.06499)).

## 4. The proof-only rule

### How erasure decides today

- A definition is erased (never emitted to JS) if its type is a proposition
  or a type former (`docs/core.md:435`) **[checked]**. The kernel's test is
  `is_type_former(…) || sort_of(…) == Sort::Prop`
  (`crates/core/src/check.rs:2504-2506`) **[checked]**.
- When a program or test runs, a definition whose result is erased "(a
  theorem, a proof-producing function, a type-level function) isn't run once
  it has all its arguments" (`crates/core/src/erase.rs:10-13`) **[checked]**.
- A `theorem`'s type must be a proposition (`E-NOT-A-PROP`,
  `docs/core.md:147`) **[checked]**, so every theorem is erased. A `def`
  whose type is a proposition or a type former is erased too; the keyword
  doesn't matter, the type does.
- Why it's safe, in the code's own words: "a proof or a type never decides
  which way a computation of data goes", because matching on a proof to
  make data is allowed only for one-constructor propositions with proof
  fields (`E-PROP-ELIM`) (`crates/core/src/erase.rs:35-42`) **[checked]**.
- A `match` in a definition becomes a generated definition `owner.%match1`
  (`docs/syntax.md:1116`) **[checked]**; in a theorem its result is the
  branch's goal, a proposition, so it is erased by the same test
  **[inferred]**.

### The rule

**`reify` may be used only in a declaration whose result is erased**: a
`theorem`, a `def` whose type ends in `Prop` (a predicate, `def Finishes (t:
() -> {Fail} a): Prop := match reify t with …`) or in a type former, and the
local definitions and `match`es inside those. Anywhere else (a `def` that
computes data, a `test`, an `instance`, an `export`) it is refused.

Checked by the elaborator, like D1122's boundary: when `match reify` is
elaborated, the current declaration's elaborated type is tested with the
kernel's erasure test. The signature is declared to the kernel before the
body is elaborated (`crates/elab/src/lib.rs:2225-2245`, `docs/core.md:147`)
**[checked]**, and the kernel computes a declared definition's erasure from
its type alone (`erase::of_def`, `crates/core/src/erase.rs:150-162`)
**[checked]**; calling it for the declaration being elaborated, whose state
isn't final yet, needs a small variant **[inferred]**. No
kernel change, and no new term former: what reaches the kernel is an
ordinary `match` on `t ()`, which the kernel already checks. The check is
about the *source* form, so handlers, whose translation is also a fold over
the tree (`Fail.%elim`, `foldComp` in §2's goal), are unaffected.

This is deliberately coarser than "only in erased positions". A data
definition that wants a proof built with `reify` (an `auto` argument, say)
calls a theorem that uses it. That is always possible, keeps the check to
one test per declaration, and matches F\*'s rule closely: "F⋆ programs using
primitive state are forbidden from using reify and reflect only in the
executable part of a program", while erased ghost code may use them; clients
get `ghost_reify`, whose result is `Ghost`, so it "can only be used within
specifications" (Ahman et al., §2.7, same link). Lean's `noncomputable` is
the same idea from the other side, a definition "exempt[ed] from
compilation" ([Lean reference, definition modifiers](https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/));
whether Lean lets computable code use such definitions in proofs and types
is **[unverified]**.

### What a program gets

```
def finished (t: () -> {Fail} a): Bool :=
  match reify t with
    | return x => True
    | Fail.stop msg, _ => False
```

```
[E-PROOF-ONLY] Error: `reify` can only be used in a proof
  ╭─ finished's result `Bool` is data, so this would run
  │
  Note: state what you need as a theorem and use `reify` there; to act on
        a failure at run time, use a handler such as `Fail.toResult` or
        `Fail.orElse`
```

### Why runtime code then can't observe the representation

A declaration that uses `reify` is erased. It is not emitted
(`docs/core.md:435`), and while a program runs it is the placeholder, not
computed (`erase.rs` rule 3) **[checked]**. What it produces is a proof or a
type, and the only way from a proof to data is `E-PROP-ELIM`'s one-branch
case (`erase.rs:35-42`) **[checked]**. A predicate defined with `reify`
can't be decided at run time either: a `Decidable (Finishes t)` instance is
data, so its body can't use `reify`. So no data a program computes depends
on how `reify` saw the tree.

That is only half the guarantee: §2 found programs can see trees without
`reify`. §6 (stage R2) closes that.

## 5. Abilities that resume

`Fail` and `Abort` never resume: their one operation returns `Empty`
(`Fail.sw:18-20`, `crates/elab/src/std/Abort/Abort.sw:25-26`)
**[checked]**. So a split is one step deep, every branch is final, and no
induction or function extensionality is needed (stage 0 found the same,
effect-polymorphism.md "As built (stage 0)") **[checked]**.

`State s` (`get`, `put`), `Log`, `Each` resume: after `State.get ()` the
computation continues with `k y` for the state `y`, which may perform more
operations. A proof about `State.run init (() => t ())` must therefore be by
*induction* on the tree, with a hypothesis for every continuation.

- A one-step `match reify` is still useful (the first operation of a known
  program), but it isn't enough for laws over an arbitrary `t`.
- A theorem can't recurse on `() => rest y`: the size-change check sees a
  thunk, not a smaller tree **[inferred]**, though `foldComp` recursing on
  `rest y` passes (`Effect.sw:19-23`) **[checked]**. So induction needs its
  own form, e.g.

  ```
  induction reify t with
    | return x => …
    | State.get (), k, ih => …    -- ih: (y: s) -> <the goal for k y>
  ```

  where the goal for `k y` is the original goal with `t` replaced, which is
  a motive the elaborator must build by abstracting `t ()`, the same search
  `match` does for generalisation.
- Equations between continuations (`bindAssoc`'s `Call` case) need function
  extensionality: `Effect/Laws.sw` already uses `Quot.funext` for exactly
  this (`Laws.sw:17`) **[checked]**. Fine for theorems; the axiom report
  (`stitchwort axioms`) will show `Quot.sound`.
- Open rows (`{Fail | e}`): the remaining operations are `R o` with
  `o: rowOp e`, which no one may inspect (D1122). A clause
  `| other, k =>` that only forwards would be needed, and a proof through
  it needs induction too.
- `IO` and `Partial`: no. `IO` is handled by the runtime; a `Delay` is
  opaque even to the kernel (`Effect.sw:214-218`) **[checked]**. F\* has the
  same limit: reification "only works for terminating code" (Ahman et al.,
  §1).

**In scope for a first stage:** `match reify` on a thunk whose row is
closed and lists abilities only: `{Fail}`, `{Abort}`, and the closed rows
of user abilities (a one-step split, so resuming abilities get it too, just
without induction). Out of scope: `induction reify`, open rows, bare rows,
`Partial`.

## 6. Interactions

- **Stage 1's `CompIn` and bare rows.** A thunk `() -> {e} a` with a row
  variable is `() -> CompIn e a` (`Effect.sw:161-163`) **[checked]**, stuck
  on `e`: there's no tree to split until `e` is known, and `Row`'s
  constructors are internal (D1122). `match reify` on it is refused:
  "this computation's row `{e}` isn't known; `reify` needs a row that lists
  its abilities". At `e := Empty` the thunk is a plain function, and a
  proof needs no `reify`.
- **D1140 (a)** (equation operands and branches whose type is a
  computation are passed as written). Under (iii) `reify` is never an
  operand or a branch, so it doesn't interact. D1140 (a) still matters for
  `Comp` types written by hand, which R2 below takes away from programs.
- **Handlers.** Unchanged, and still the only way a program observes an
  effect. `reify` clauses look like handler clauses, but a handler folds
  (deep) and runs, while `reify` splits once (shallow) and never runs.
- **Stage 4 (design F).** The kernel's meaning of a computation stays the
  tree: proofs, and the reference evaluator, compute with it. Stage 4's
  runtime must agree with it on what programs print (differential tests
  against the reference evaluator, already stage 4's acceptance,
  effect-polymorphism.md §6) **[checked]**. It needn't build a tree, because
  (1) declarations using `reify` are erased (§4) and (2) after R2 no
  program can match on `Done`/`Call` or name `Effect.Comp` either. Then the
  only operations on a computation a program has are: run it in place,
  pass it as a thunk, and hand it to a handler, and evidence passing, CPS
  and exceptions all implement those three.
- **The `effect-pass-*` examples.** They exercise stage 0 with hand-written
  `Comp NoOp NoRes` values in `def`s
  (`examples/accept/effect-pass-computations.sw`) **[checked]**. Under R2
  they'd move into theorems or into std-only tests.

## 7. Staged plan

| Stage | Work | Acceptance |
|---|---|---|
| R1 | `match reify t with` and handler-style clauses (`return x`, `Ability.op arg, k`) in the parser and elaborator; elaborated to a generalised `match` on `t ()` with the operation's internal constructor, the row's injections, and the closed row's absurd end; `k` bound as `y => () => rest y`; `E-PROOF-ONLY` (§4). Std: `Fail.toResultThen`, `Fail.toOptionThen`, `Fail.toOptionToResult` (`Fail.toOption t = (Fail.toResult t).toOption`, errors.md §3.7's "welcome" law), `Abort.toOptionThen`, and `Fail.toResultMapIn` | `Fail.toResultMapIn` checks in `Fail.sw` as stated in errors.md §3.7, **closing SW-378**; `examples/accept/reify-fail.sw` with the laws above and a one-step split of a user `State` program; rejects, one file each: `reify` in a data `def`, in a `test`, in an `instance`; on a bare row `{e}`; on an open row `{Fail \| e}`; on a `{Partial}` thunk; an operation of an ability not in the row; a missing clause (`E-NONEXHAUSTIVE`); `match h: reify`; `stitchwort axioms Fail.toResultMapIn` prints nothing |
| R2 | Close the leak in §2: outside std, `Effect.Comp`'s constructors and `foldComp`, `bind`, `translate`, `runPure` are internal, except in declarations whose result is erased (D1143) | p3's `finishedNow` is refused; the `effect-pass-*` examples moved (theorems, or a std test); std, AoC and examples check |
| R3 | When a proof needs it (board rule): `induction reify` for resuming abilities, closed rows; then a forwarding clause for open rows | the first such proof, likely `State.run` of `List.mapIn` or `Fail.toOption` at an open row; uses `Quot.funext` only where an equation between continuations is needed |

R1 is one lane, medium: a parser case, an elaborator rewrite into an
existing `match`, one declaration-level check, and std lemmas. R2 is small.
R2 must land before stage 4 starts, since stage 4 relies on it.

## 8. Decisions for the owner

**Decided (Matt, 24 Oct 2026):** each as recommended. The numbers below were provisional; they are recorded as D1144 (surface form), D1145 (run-time leak), D1146 (who may use it), D1147 (granularity) and D1148 (keyword).

Numbers are provisional.

**D1142: the surface form.**

- (a) **[Recommended]** `match reify t with`, handler-style clauses (§3
  (iii)). No new type; operations named as in handlers.
- (b) `Effect.reify t` as a term with `Done`/`Call (Fail.stop msg) rest`
  patterns (§3 (i)). Needs a printable type for the tree in proofs.
- (c) Per-ability `Fail.cases` with a written motive (§3 (ii)); still needs
  (a) or (b) inside std.

**D1143: close the run-time leak (stage R2).** Programs can match on
`Effect.Comp` today (§2, probe p3).

- (a) **[Recommended]** Yes, right after R1: `Comp`'s constructors and its
  eliminators become library-internal outside erased declarations. Without
  it, D1141 (d)'s "runtime not committed to trees" doesn't hold.
- (b) At the start of stage 4.
- (c) No: accept that programs can see trees, and let stage 4 keep a tree
  where a program matches on one.

**D1144: who may use `reify`.**

- (a) **[Recommended]** Every proof, in any file. The proof-only rule is
  what protects the runtime; users need it for their own abilities.
- (b) Std only, at first (`E-INTERNAL`, as D1122's names); users rewrite
  with std's lemmas.

**D1145: how fine the proof-only check is.**

- (a) **[Recommended]** Per declaration: its result must be erased (§4).
- (b) Per position: also inside erased arguments of data definitions. More
  permissive, and needs the elaborator to track which subterm positions are
  erased.

**D1146: the keyword.** `reify` (F\*'s word) **[Recommended]**, or a plainer
word such as `match outcome t with` or `match steps t with`. `reify` would
become reserved only after `match`, so no existing name breaks
**[inferred]**.

## As built (stage R1)

SW-419, 24 Oct 2026. `match reify t with`, the proof-only check, and the
std laws, as §7's R1 row says, with the deviations below. The kernel is
unchanged.

**Syntax.** `Expr::Reify { thunk, clauses, span }` (`ast.rs`). The parser
reads it in `match_expr` when the name after `match` is `reify` and the next
token isn't `with`, `,` or `:` (`reify_ahead`), so `match reify with` and
`match reify, x with` still match a variable called `reify`. The clauses are
a handler's (`handler_clauses`, shared with `handle`). A second scrutinee
after the thunk is a parse error, and so is `match h: reify t`, with a note
(`E-PARSE`). A clause's continuation may now be `_`, in handlers too.

**Elaboration** (`crates/elab/src/reify.rs`). `check_reify`:

1. The proof-only check (below).
2. The computation: for `() => e` (a lambda whose parameter is the unit
   pattern), `e` itself, elaborated with `infer_unrun`, so a call is passed
   as a computation and not run; for any other thunk, `t` is inferred, must
   be a function from `()`, and the scrutinee is `t ()`. Its type must be a
   `Comp` over a closed row of abilities (`effects::comp_parts`): a bare row
   `{e}`, an open row `{Fail | e}`, a `Partial` computation, or a type that
   isn't a computation is `E-REIFY`, each with its own message.
3. The alternatives, with patterns the compiler writes by identity:
   `internal_ctor_pattern` names a constructor as `%ctor d c`, which source
   can't spell and the pattern compiler resolves without a lookup (`lib.rs`,
   next to `%unit`). `return x` is `Done x`; `Ability.op arg, k` is `Call
   (R (… (L (op arg)))) k`, with one `R` per ability before it in the row;
   an operation's `()` argument is the unit pattern. The closed row's end is
   an absurd row, `Call (R … (R ())) _`, with no right-hand side. A missing
   `return` or operation clause is `E-NONEXHAUSTIVE` (naming each), a
   repeated one `E-DUPLICATE`, and an operation of an ability not in the row
   `E-ABILITY`.
4. `matching::generalised_term`: the ordinary generalised `match` on that
   term (as for an expression scrutinee), lifted to `owner.%matchN`.
   `matching::compile` takes the absurd rows as an extra argument.

**The proof-only check (D1147).** `Elaborator::body_type` holds the
declared type while a top-level declaration's body is elaborated
(`body_term`, and the step of a `decreasing` definition). When `reify` is
met, `Elaborator::body_erased` decides from it whether the result is
erased, by the kernel's own test (`check::telescope(…).result_erased`,
which is what `erase::of_def` uses); no variant was needed. Local definitions and
`match`es inside the body see the top-level declaration's answer. Anywhere
else (a test, a signature, an expression typed in) it is unset, and `reify`
is refused there too. `E-PROOF-ONLY`'s label says "this declaration computes
data, so this would run", or for those "this isn't the body of a proof".

**Std.** In `Fail.sw`: `Fail.toResultThen`, `Fail.toOptionThen`,
`Fail.toOptionToResult` (`Fail.toOption t = Result.toOption (Fail.toResult
t)`) and `Fail.toResultMapIn`, as stated in errors.md §3.7. In `Abort.sw`:
`Abort.toOptionThen`. Each `Then` law and `ToResult` is one split with
`rfl` in both clauses. `Fail.toResultMapIn` is by induction on the list:

```
  | [x, ..xs] =>
    let rest := Fail.toResultMapIn f xs
    match reify (() => f x) with
      | return y =>
        match reify (() => xs.mapIn f) with
          | return ys => rewrite <- rest in rfl
          | Fail.stop msg, _ => rewrite <- rest in rfl
      | Fail.stop msg, _ => rfl
```

The induction hypothesis is a `let`, so the second split generalises
`xs.mapIn f` in its type too, and it says what the rest gives (`Ok ys` or
`Err msg`). `stitchwort axioms` prints nothing for it.

**Tests.** `examples/accept/reify-fail.sw`: the five laws restated and
proved again, std's `Fail.toResultMapIn` used, and a user's `State s`
ability: predicates `Finished` and `PutsFirst` (`def`s ending in `Prop`),
`finishedKeepsState` and `putFirstForgets` (a `put` first makes `runState`
forget its initial state; `rfl` in the `put` clause), and on the row
`{State Nat, Fail}` two predicates and `notBoth`, where two hypotheses are
split with `t`. Rejects, one file each: `reify-data-def`, `reify-test`,
`reify-instance` (`E-PROOF-ONLY`); `reify-bare-row`, `reify-open-row`,
`reify-partial` (`E-REIFY`); `reify-other-ability` (`E-ABILITY`);
`reify-missing-clause` (`E-NONEXHAUSTIVE`); `reify-named-equation`
(`E-PARSE`).

**Deviations and findings.**

- *The continuation.* `k` is the `Call`'s own continuation, not
  `y => () => rest y`: a function from what the operation returns to the
  rest of the computation, so `| State.get (), rest =>` has `rest: s ->
  {State s} a`, and for `put` (which returns `()`) `rest: () -> {State s}
  a`. It is still a function, so arrows-only holds, and it needed no extra
  binding in the generated `match`. For `Fail` and `Abort` it is `Empty ->
  {Fail} a`.
- *A new code,* `E-REIFY`, for a thunk `reify` can't split (the note gave
  the messages but no code).
- *The thunk written in place* must have a body that is passed as a
  computation: a call, a variable, a dot call or a pipe (`() => f x`,
  `() => xs.mapIn f`). A block in a thunk hasn't been tried.
- *Goals.* In an operation's clause the goal is short (`Err msg = Err msg`
  in `toResultThen`). In a `return` clause it is shown with the handler
  unfolded (`Effect.foldComp (x => Ok x) … (k x) = …`), because the
  occurrence test generalises the evaluated goal, where `Fail.toResult` has
  already unfolded. So §3's "each branch's goal is one the user can read"
  holds only in part.
- *Using a law on a thunk written in a proof* is awkward: `() => e` is a
  lambda over the unit pattern, which becomes a lifted `match` helper, so
  `Fail.toResultThen (() => xs.mapIn f) …` written in a proof is a
  different term from the same thunk in the theorem's statement (`E-TYPE-
  MISMATCH`, with "two different `(match …)` appear here"). The `MapIn`
  proof above avoids it by splitting a second time instead of using
  `toResultThen`. Rewriting with these laws in users' proofs will meet the
  same thing; a thunk `() => e` elaborated as a plain lambda (its parameter
  ignored) would fix it, and is outside R1.

## Appendix A. Probes

Run with `/Users/matt/repos/mdr/stitchwort/target/release/stitchwort`
(`check` or `test`), built 24 Oct 13:46 from `main` after the stage 1
merge. Each file starts with `import Std (Effect, Fail, Result)` and
`import Std.Effect.Comp (Done, Call)`; p1 and p2 also
`import Std.Effect.Plus (L, R)`.

**p0**: spelling the tree type.

```
def FailTree (a: Type): Type := Effect.Comp (Effect.Plus Fail Effect.NoOp) (Effect.PlusRes Fail.res Effect.NoRes) a
```

`[E-ABILITY] `Fail` is an ability, not a type or a value`.

**p1**: splitting with a user-written `viewOf`.

```
def viewOf [op: Type] [res: op -> Type] [a: Type] (t: () -> Effect.Comp op res a): Effect.Comp op res a := t ()

theorem toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k (t ())) =
      Result.flatMap (x => Fail.toResult (() => k x)) (Fail.toResult t) :=
  match viewOf t with
    | Done x => rfl
    | Call (L stop) rest => ?
    | Call (R none) rest => ?
```

The `Done` branch is accepted. The `L` branch's goal begins
`Fail.%elim (msg k => Err msg) stop (y => Effect.foldComp …` on both sides,
with `stop: Fail` in context: stuck on the operation. (The `R` branch is the
closed row's end, `none: Effect.NoOp`.)

**p2**: naming the operation in a pattern. `Call (L (Fail.stop msg)) rest`:
`[E-PARSE] `Fail.stop` is a qualified name, which can't be used here`. With
`import Std.Fail (stop)`, `Call (L (stop msg)) rest`: `[E-PARSE] expected
`)`, but found `msg``.

**p3**: a program looking at the tree.

```
def finishedNow [op: Type] [res: op -> Type] [a: Type] (t: () -> Effect.Comp op res a): Bool :=
  match viewOf t with
    | Done x => True
    | Call o k => False

def failing (n: Nat): {Fail} Nat := if n == 0 then Fail.fail "zero" else n

test "runtime sees the tree" := finishedNow (() => failing 0) == False
test "runtime sees the tree, done" := finishedNow (() => failing 3) == True
```

`2 test(s): 2 passed, 0 failed`.

## As built (stage R2)

SW-420, 24 Oct 2026. D1145 (close the run-time leak). The kernel is
unchanged; the check is in name resolution.

**What is refused.** `Elaborator::is_proof_only` (`crates/elab/src/scope.rs`)
names the built-ins `Effect.Comp`'s constructors (`Done`, `Call`) and the
definitions `Effect.foldComp`, `Effect.bind`, `Effect.translate` and
`Effect.runPure`. `Elaborator::resolve` does not find them outside the
library when the code being elaborated is a body (`Phase::Body`) whose
declaration's result is not erased, or a body-less expression (a `test`).
`Elaborator::unknown` then reports `E-PROOF-ONLY`, "`Effect.Comp.Done` takes
a computation apart, so it can only be used in a proof", with notes saying
where it is allowed and to use a handler instead. I chose `E-PROOF-ONLY`
(not `E-INTERNAL`) because the names are usable in proofs, as `reify` is, and
the test is the same one (`body_erased`, the kernel's own `result_erased`),
so the two errors read alike.

**Where it is allowed.** The type `Effect.Comp` itself is still nameable
everywhere (it is a type, and a theorem's statement needs it). The five names
are allowed in the body of a theorem or of a `Prop`- or type-valued `def`,
in any signature or data type's fields (`Phase::Signature`, `Header`,
`Fields`: they are types, never run), and in the library files.
Elaborator-generated uses (a number literal where a computation is expected,
`handle`, the empty row's `runPure`) go by identity, not by name, and are
unaffected.

**Examples.**

- `reject/effect-runtime-sees-tree.sw`: Appendix A's p3 (`viewOf`,
  `finishedNow`), now `E-PROOF-ONLY` at the `Done` pattern.
- `accept/effect-pass-computations.sw` and the twelve
  `reject/effect-pass-*.sw`: `isDone: ... -> Bool` became
  `IsDone: ... -> Prop` (`Done value => Unit`), `allDone` uses `And`, the
  `= True := rfl` theorems are `:= Trivial`, and the rejects now fail with
  `E-TYPE-MISMATCH` (`Unit` where `IsDone c` is wanted) instead of `E-REFL`:
  the same path is tested, an arbitrary computation is not known to be
  `Done`. The run-time test `runIdentity` is a theorem.
- `soundness/{fake-child,hidden-recursive-call,higher-order-recursion,
  infinite-computation,restart-handler,mutual-restart-handler}.sw`: the same
  termination checks, with the functions returning `Prop` (in
  `hidden-recursive-call` the operation's answer is a `Prop` too; in
  `infinite-computation`, `forever` folds the tree it builds).
- `accept/handlers.sw` and `accept/rows.sw` keep their scenarios: the
  hand-written handlers and programs over `Comp` are local definitions of one
  theorem each (`handlersBehave`, `rowsBehave`), and each former `test` is a
  `let` checked by `rfl` (the dependent `res` stuck on a `Bool`, `translate`
  along `sigSwap`, the traces). Signatures, type-valued definitions and pure
  helpers stay at the top level.
- The unknown-name hint still lists a proof-only name as writable
  (`written` uses `resolve_any`).

**Not changed.** Std, AoC and the other examples never named these outside the
library, so nothing else moved.
