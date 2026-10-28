# Moving a closed computation into an open row (SW-424)

Status: design note, stopped for review. A prototype of the recommended
option is on branch `sw-424-delayed-translate` (commit marked PROTOTYPE).
The kernel is unchanged in every option considered here.

Claims marked [checked] were run or read on `main` at `f87729a2` (after
SW-422); file:line references are to that commit unless they say
"prototype".

## 1. Summary

When a computation over a fixed set of abilities (a *closed* row, `{Fail}`)
is used inside a thunk whose row is *open* (`{Fail | e}`, the row
`Fail.toResult` takes), the compiler wraps it in `Effect.translate`, which
moves a computation from one row to another. It does that at the moment it
meets the call. So the same code can end up with the `translate` in
different places, depending on whether a call was written straight inside the
thunk or reached through a thunk variable that a law is about. In the usual
case the unknown part `e` later becomes the empty row, and then every one of
these `translate`s moves the computation from `{Fail}` to `{Fail}`: it does
nothing, but it is still there, and terms that differ only in where it sits
are not equal by computation. `rewrite` with a law then finds nothing.

**Recommendation (option B below):** instead of `translate`, write a new
library definition `Effect.widenIn e m c`, defined by cases on the row `e`:
for the empty row it *is* `c`; for a row with abilities it is `translate m
c`, as today. Nothing is decided early, nothing about inference order
changes, and as soon as `e` becomes empty (by unification or by the end of
declaration default) every such move computes away, wherever it was put. This
is the same trick design C already uses for `CompIn`, `doneIn` and `bindIn`
(effect-polymorphism.md, "As built (stage 1, first part)").

The prototype does this in about 80 lines (one library definition, one
registry name, one branch in `lift`). With it the short `Fail.toResultMapIn`
proof checks, `Each.sw` is unaffected, and the named test binaries pass (§5).

## 2. The problem

### A minimal repro [checked]

No `reify` is needed:

```
import Std (Fail, Result)

-- `toResultThen` with `t` run inside a bigger computation than the law's.
theorem minimal (t: () -> {Fail} Nat):
    Fail.toResult (() => Succ (Succ (t ()))) = Result.flatMap (x => Ok (Succ x)) (Fail.toResult (() => Succ (t ()))) :=
  rewrite Fail.toResultThen (() => Succ (t ())) (x => Succ x) in rfl
```

On `main` this is `E-REWRITE-NOTHING`:

```
`rewrite` found no `Fail.toResult (%arg0 => Effect.bind (Effect.translate (Effect.sigCase Effect.sigLeft Effect.sigFromNo)
    (Effect.bind (t ()) (%2 => Done (Succ %2)))) (%5 => Done (Succ %5)))` in the goal
...
goal as it computes: `Fail.toResult (%arg0 => Effect.bind (Effect.bind (Effect.translate … …) (%2 => …)) (%2 => Done …)) = …`
```

Read the two terms side by side:

- **The law's instance.** `Fail.toResultThen (t: () -> {Fail} a) (k: …)`
  states `Fail.toResult (() => k (t ()))`. When the law was elaborated, `t ()`
  is a call of a `{Fail}` function inside a `{Fail | e}` thunk, so it became
  `translate m (t ())`. Substituting our thunk `() => Succ (t ())` for `t`
  gives `translate m (bind (t ()) Succ)`: the `translate` is around **the
  whole** inner computation, because our thunk was elaborated on its own, in
  the closed row `{Fail}`, as the law's argument.
- **The goal.** We wrote `Succ (Succ (t ()))` directly in the thunk, so only
  the call `t ()` was moved: `bind (translate m (t ())) Succ`, then `Succ`
  again. The `translate` is around **the call only**.

Both `m`s are `sigCase sigLeft sigFromNo`, the move from `{Fail}` into
`{Fail | e}`, and `e` has become the empty row in both statements, so both
`translate`s move `{Fail}` into `{Fail}`. `translate m (bind c k)` and `bind
(translate m c) (x => translate m (k x))` are equal, but only by a proof by
induction on `c` (naturality of `translate`), not by computing: `translate` is
a fold over the computation tree, and `c` here is a variable's call, which
doesn't compute.

The same thing stops the short proof of `Fail.toResultMapIn` [checked, as a
copy of the theorem in a file of its own]:

```
  | [x, ..xs] =>
    match reify (() => f x) with
      | return y =>
        rewrite Fail.toResultThen (() => xs.mapIn f) (ys => Cons y ys), Fail.toResultMapIn f xs in rfl
      | Fail.stop msg, _ => rfl
```

On `main`: `rewrite found no Fail.toResult (%arg0 => Effect.bind
(Effect.translate (…) (List.mapIn f xs)) (%5 => Done (Cons y %5)))`; the goal
has `Effect.translate (MkSigMap … …) (Effect.bind … …)`, the `translate`
around all of `(x :: xs).mapIn f` unfolded. So std's proof splits a second
time instead (`Fail/Fail.sw`, `Fail.toResultMapIn`).

### Why closing the row early broke `Each.sw`

The experiment in SW-422 (`lift-close.diff`, reported in the ticket, not
re-run here) set `e` to the empty row as soon as a `{A}` computation was moved
into `{A | e}` with the same abilities. That made the proof work, but in
`crates/elab/src/std/Each/Each.sw:104-112`

```
test "abort outside each: one abort stops every choice" :=
  Abort.toOption (() => Each.collectIn (() =>
    let n := Each.each [2, 3, 4]
    Abort.ensure (n % 2 == 0)
    n / 2)) == None
```

the thunk's row is `{Each | e}` (`Each.collectIn`'s parameter), `Each.each`
is `{Each}`, and only the *next* line, `Abort.ensure`, says that `e` must hold
`Abort`. Closing `e` at the first line makes the second line an error. Any fix
must therefore not decide anything about `e` when the closed call is met.

## 3. Where `translate` goes in, and when rows are settled [checked]

- **Insertion.** `fn lift` (`crates/elab/src/effects.rs:604`) moves a
  computation of a callee's row `from` into the current row `to`. When the two
  rows don't have the same shape (`same_shape`, `effects.rs:525`: same
  abilities in order and the same tail; a closed row and an open one never
  do), it builds a mapping (`mapping`, `effects.rs:813`) and calls
  `Builtin::Translate` (`effects.rs:696-716`). `lift` runs once per call, at
  the call: for an ordinary call in `comp_app` (`effects.rs:2179-2180`), for
  each stage in `Stages::run`/`finish` (`effects.rs:2247`, `2262`) and
  `run_stage` (`effects.rs:2318`), and in one more place (`effects.rs:3428`).
- **Rows settle late.** A row unknown such as `Fail.toResult`'s `e` is solved
  by unification when something says what it is (`unify::row_rule`), or
  defaulted to `Empty` at the end of the declaration:
  `Elaborator::finish` (`crates/elab/src/lib.rs:892-895`) calls
  `solve_obligations`, then `settle_rows` (`crates/elab/src/rows.rs:155`),
  which retries postponed comparisons and then `default_rows`
  (`rows.rs:181`).
- **Hidden helpers are made before that.** A definition body's lifted
  `match`es and local definitions are resolved by `e.lift(&key, true)`
  (`lib.rs:1971`) *before* `e.finish(&term, 0)`; a signature's at
  `lib.rs:2250`, also before `finish`. `Elaborator::lift`
  (`crates/elab/src/lift.rs:406`) runs `solve_obligations` but not
  `settle_rows`.

So the choice "translate or not" is made at the call (too early: `e` isn't
known), while `e` is known only at `finish`, after helpers have been made.

## 4. Options

Common to all: the kernel is unchanged; the elaborated term changes, so the
hashes of definitions containing such moves change (not a goal to keep,
per the project's rule), and the kernel re-checks every term.

### A. Delay the choice (as proposed in SW-422)

At the call, `lift` would put a placeholder (a frozen unknown, as hidden
helpers already use) and record "move `c` from `{A}` into `{A | e}`". After
rows settle, each placeholder becomes `c` if `e` is empty and `translate m c`
otherwise.

- *Each.sw:* fine; nothing is decided at the call.
- *Inference order:* the decision has to move: today rows settle after helpers
  are resolved (§3), and a helper's body can contain a placeholder. Either
  `settle_rows` (including defaulting) moves before `lift` in every path that
  lifts helpers (body, signature, `decreasing` step `decreasing.rs:1223`,
  `partial.rs:485`, `defaults.rs:156`, local retries), or helpers learn to
  carry placeholders and be patched. Defaulting before helpers are resolved
  changes when defaulting happens relative to what helper resolution solves;
  I haven't found anything that depends on it, but it is a reordering of the
  end of every declaration.
- *Unification while waiting:* a placeholder is opaque, so anything compared
  with the moved computation before the end of the declaration (a `rewrite`
  or `rfl` inside the same proof, an instance search) sees an unknown, not
  the computation. A proof would then behave differently depending on
  whether its `rewrite` comes before or after the end of the declaration; at
  minimum this needs a "decide now" step whenever a term is compared.
- *Result:* the cleanest terms (no wrapper at all when `e` is empty).
- *Cost:* the largest of the options that work: new placeholder kind,
  reordering of `finish`, a pass to fill placeholders.

### B. A row-indexed move that computes away at the empty row (recommended; prototyped)

Add to `core/Effect.sw`, next to `liftIn`/`lowerIn`:

```
def Effect.widenIn [a: Type] (pre: Type -> Type) (preRes: (t: Type) -> (t -> Type) -> pre t -> Type):
    (row: Effects) -> SigMap (pre NoOp) (preRes NoOp NoRes) (pre (rowOp row)) (preRes (rowOp row) (rowRes row)) ->
    Comp (pre NoOp) (preRes NoOp NoRes) a -> Comp (pre (rowOp row)) (preRes (rowOp row) (rowRes row)) a
  | Empty, m, computation => computation
  | Ops op res, m, computation => translate m computation
```

`pre t` is "these abilities, followed by `t`" (`Plus FailOp t` for `{Fail}`).
A closed `{Fail}` ends in `NoOp`, and the open `{Fail | e}` ends in `rowOp e`,
which is `NoOp` when `e` is `Empty` (`Effect.sw`, `rowOp`), so at the empty
row the two types are the same and the first clause type-checks. `lift`
writes `widenIn pre preRes e m c` instead of `translate m c` when it moves a
closed, total row into a total row with the same abilities in the same order
and a tail (prototype `effects.rs:697`, `fn widen` at `effects.rs:787`).
Every other move is unchanged.

- *Each.sw:* unchanged behaviour. Nothing is decided at the call; when
  `Abort.ensure` later makes `e` = `{Abort | r}`, `widenIn (Ops …) m c`
  computes to `translate m c`, the term `main` builds.
- *Inference order:* unchanged. `lift` reads and solves exactly what it did.
- *Hidden helpers:* nothing new. A helper body may contain `widenIn ?e …` with
  `?e` unsolved, exactly as today it contains `translate` whose type arguments
  mention `?e`.
- *Comparison inside a proof:* works at any time; once `e` is known to be
  empty, `widenIn Empty m c` computes to `c` wherever it is, which is what
  makes both repros check.
- *Inference risk (the external review's warning):* `widenIn ?e …` is, like
  `CompIn ?e B`, a definition stuck on a row unknown, and not injective in
  `?e` (`widenIn Empty m c` and `widenIn (Ops …) m' c'` can be equal). The
  unifier treats a stuck definition's spine structurally, which can solve
  `?e` against another `widenIn`'s row; this is the approximation the review
  asks to keep isolated (effect-rows-external-review.md, "Your inference
  machinery…"). It affects only which programs are accepted, never
  soundness, since the kernel re-checks. No test hit it.
- *Goals:* shown computed, so the wrapper doesn't appear once `e` is empty
  (checked: an `E-REFL` goal in the prototype shows `Fail.toResult (%arg0 =>
  Effect.bind (t ()) …)`, no `widenIn`, no `translate`).
- *Run time:* expected to be faster at the empty row: `translate` walks the
  whole tree to rename operations that are already in place, `widenIn Empty`
  returns its argument. Not measured.
- *Internal name:* `widenIn` joins the internal list of D1122
  (`Elaborator::is_internal`), so programs can't name it.
- *Cost:* small (§5).

### C. Normalise where the `translate` goes

Make the elaborator always put the move in one canonical place, so two
writings of the same code agree.

- *Innermost* (around each call, as now) is not stable under substitution:
  a law about `t ()` has its move around `t ()`, and substituting a thunk for
  `t` puts it around that thunk's whole body. That is exactly the repro.
- *Outermost* (elaborate the thunk's body in its own row, then move the whole
  body once) is stable under substitution, and would also cover moves that
  don't vanish (rigid `e`, or `{Fail}` into `{IO, Fail}`, see §6). But it needs
  the body's own row first: the body would be checked against a fresh row
  unknown, whose abilities are known only after the body (the `Each`/`Abort`
  case) and whose tail must be closed at some point, which brings back A's
  "decide at the end" problem for every thunk. It changes the check of every
  thunk checked against an open row, and the errors (`E-ABILITY` labels point
  at the call today).
- Too much change for this problem; worth revisiting only if §6 starts to
  matter.

### D. Make `rewrite` match up to `translate`

`rewrite` (and `rfl`) compare by computing. Making them treat `translate m
(bind c k)` and `bind (translate m c) (x => translate m (k x))` as the same
would need `rewrite` to normalise both sides with `translate`'s laws
(naturality, `translate` of `Done`) and to produce the proof steps, since the
kernel can't see them as equal (that would be a kernel change, ruled out).
That is a `simp`-like normaliser for one family of lemmas, and the naturality
law over continuations needs function extensionality (`Effect/Laws.sw` keeps
such laws apart for that reason), so proofs using it would depend on it.

Lean is in the same situation with its automatic monad lifts: its lifting
lemmas live in `LawfulMonadLift` (`monadLift_bind`: lifting a bind is binding
the lifts), proofs normalise lift placement with them, and the library keeps
`liftM` copies of these lemmas because "`rw` matches on syntax only"
([Init.Control.Lawful.MonadLift.Lemmas](https://leanprover-community.github.io/mathlib4_docs/Init/Control/Lawful/MonadLift/Lemmas.html),
[Init.Control.Lawful.MonadLift.Basic](https://leanprover-community.github.io/mathlib4_docs/Init/Control/Lawful/MonadLift/Basic.html)).
So this option is the general one, but it is a tool, not a fix; B removes the
need in the common case without it.

### E. Other ways considered

- *Close the row at once* (the SW-422 experiment): breaks `Each.sw` (§2).
- *Representation where opening a row costs nothing* (Koka's approach: its
  runtime passes handlers as evidence, and `open` adjusts that evidence;
  recent work infers closed rows and opens them automatically at
  instantiation, Ikemori et al.,
  [TFP 2022](https://prg.is.titech.ac.jp/papers/pdf/tfp2022inference.pdf),
  and moves the `open`s to reduce run-time adjustment, Furudono et al.,
  [TFP 2022](https://prg.is.titech.ac.jp/papers/pdf/tfp2022adjustment.pdf)).
  In Stitchwort computations are trees whose operation type is the row, so a
  move between rows is a real function on the tree; changing that is the
  representation question of D1119, not this ticket.
- *A cleanup pass at the end of each declaration* that replaces `translate m
  c` by `c` when both rows have become equal. Same result as B for finished
  terms, but terms compared *during* the proof (after `e` is solved, before
  the declaration ends) would still differ, and it has to recognise which
  `translate`s the compiler made. B gets the effect by computation instead.

## 5. Prototype (option B)

Branch `sw-424-delayed-translate`, commit `626d63d5` ("PROTOTYPE (SW-424)"):

- `crates/elab/src/std/core/Effect.sw`: `Effect.widenIn` (above).
- `crates/core/src/registry.rs`: `Builtin::WidenIn` (a name for the
  elaborator to find the definition; not a kernel rule).
- `crates/elab/src/scope.rs`: `WidenIn` is internal (D1122).
- `crates/elab/src/effects.rs`: in `lift`, the `widens` case and `fn
  widen`, with helpers `ops_ending`/`res_ending` that build `pre` and
  `preRes` as lambdas over the row's tail.
- `crates/elab/src/std/Fail/Fail.sw`: `Fail.toResultMapIn` with the short
  proof (one split, then `rewrite Fail.toResultThen …, Fail.toResultMapIn f xs
  in rfl`).
- `examples/accept/reify-thunk-in-proof.sw`: the minimal repro as
  `twiceThen`.

Results (release builds):

| Check | `main` | prototype |
|---|---|---|
| `minimal.sw` (§2) | `E-REWRITE-NOTHING` | checks |
| short `toResultMapIn` proof | `E-REWRITE-NOTHING` | checks; `stitchwort axioms` on a theorem using it prints nothing |
| `Each.sw` tests (in `the_standard_library_passes_its_own_tests`) | pass | pass |
| `-p stitchwort-elab --lib` | | 57 passed, 1 ignored |
| `-p stitchwort-cli --test examples` | | 7 passed |
| `-p stitchwort-driver --test std_library` | | 31 passed, 1 ignored |
| `-p stitchwort-driver --test ability_errors` | | 13 passed |
| `-p stitchwort-driver --test empty_row_kernel` | | 5 passed |

There is no `effect_rows` test binary; the row examples
(`examples/accept/effect-rows.sw` and the `row-*` rejects) run in the
`examples` binary. `cargo clippy -p stitchwort-elab` is clean. The full gate
(`nix flake check`) was not run.

Before merging it as the real change it would need: a unit test of `lift`'s
new case (closed into open with the same abilities; different order; more
abilities; partial), an example where `e` turns out non-empty and a law still
applies (`Each`-style), a test that `widenIn` is `E-STD-INTERNAL` from a program,
and the R1 note's limit bullet updated.

## 6. What stays open, with any option except C and D

The fix applies when the move does nothing in the end. Moves that really
move something keep depending on where they were put:

- a closed `{Fail}` call inside a thunk whose row has a row *variable* of the
  enclosing declaration (`{Fail | e}` with `e` rigid). Today such a theorem
  can't be stated at all: equating two `{e}` computations in a theorem is
  `E-ABILITY` on `main` ([checked]: `rigid.sw`, "its row variable isn't part
  of the enclosing function's abilities");
- `{Fail}` moved into a row with more abilities (`{IO, Fail}`) or in another
  order (`{B, A | e}` from `{A, B}`).

No current proof needs these. If one does, the remedy is lemmas about
`translate` (option D's normalisation, by hand at first).

## 7. Decisions for the owner

**D1150. How a closed computation is moved into an open row.**
(a) **[Recommended]** Option B: `Effect.widenIn`, a library definition by
cases on the row, which is the computation itself at the empty row and
`translate` otherwise. Small, decides nothing early, keeps inference order.
(b) Option A: placeholders decided after rows settle; needs `settle_rows`
moved before helper lifting in every declaration path, and placeholders are
opaque to comparisons inside the proof until then.
(c) Option C (outermost placement): changes how every thunk against an open
row is checked.
(d) Leave it: proofs split twice, as `Fail.toResultMapIn` does today.
Reason: (a) makes both repros check with no change to when anything is
solved; (b) gets the same final terms at a much larger cost and a new
ordering risk.

**D1151. `Fail.toResultMapIn`'s proof.**
(a) **[Recommended]** With D1150 (a), use the short proof (one split, then the
`Then` law and the induction hypothesis), as in the prototype.
(b) Keep the second split.
Reason: it is the proof the law was written to allow; the second split was a
workaround.

**D1152. The remaining cases (§6: rigid rows, rows with more abilities).**
(a) **[Recommended]** Nothing now; note the limit in proof-reification.md,
and add `translate` lemmas (naturality) when a proof needs them.
(b) Build option D's normalisation in `rewrite` now.
Reason: no current proof or program hits them, and the rigid case can't yet
be stated.
