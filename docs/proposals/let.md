# Proposal: `let` that holds proofs and data, and whose value the checker can see

**Status:** draft 1, for review (19 October 2026). Nothing is implemented.

This note can be read without knowing the codebase. The main part takes about
15 minutes; the [appendix](#appendix-details-for-the-reviewer) has the
details a reviewer needs (file and line references, the typing rule, the
pieces of the compiler each option touches).

## 1. The problem

The user's position: **a `let` should be able to hold a proof or ordinary data
alike, and later lines should know what it holds.** Today neither works. All
four examples below were run on `main` (at `74b22c4`) with `stitchwort check`.

**1. The checker forgets a `let`'s value.**

```
theorem one (n : Nat) : n <= n + 1 :=
  let p := n
  Nat.leAddRight p 1
```

```
[E-TYPE-MISMATCH] expected `Nat.leq n (n + 1) = True`,
                  but this has type `Nat.leq p (p + 1) = True`
```

`p` *is* `n`, but after the `let` line the checker only knows "`p` is some
`Nat`".

**2. A `let` can't hold a proof.**

```
theorem two (n : Nat) : n <= Succ (Succ n) :=
  let h := Nat.leSucc n
  Nat.leTrans n (Succ n) (Succ (Succ n)) h (Nat.leSucc (Succ n))
```

```
[E-UNIVERSE] expected something of type `Type`, but this has type `Prop`
```

The same proof with `Nat.leSucc n` written inline is accepted.

**3. A `let` leaves a trace in the compiled function that proofs then have to
mention.** With

```
def f (n : Nat) : Nat :=
  let m := n + 1
  if m < 3 then 0 else m
```

a proof about `f (n + 5)` gets stuck on

```
Effect.runPure (Decidable.elim (…) (\_ => Done 0) (\_ => Done (n + 5 + 1)))
```

while the same function without the `let` gets stuck on the
`Decidable.elim (…) (\_ => 0) (\_ => n + 5 + 1)` you'd expect. The
`runPure` and `Done`s come from the effects machinery, can't usefully be
written in a lemma, and so the day 2 proofs needed proof-only helper
functions.

**4. Two related gaps.**

- *Pattern `let`.* `let (a, b) := p` is a one-alternative `match`. When `p` is
  an unknown (a variable in a proof), the `match` can't compute, so the day 3
  proofs had to rewrite the implementation as `p.fst` / `p.snd`. Even then,
  `sw (sw p) = p` for `sw p = (p.snd, p.fst)` doesn't hold by computation,
  because Stitchwort has no *eta rule for pairs* (`p ≡ (p.fst, p.snd)`).
- *Termination* (found while writing this note). This is rejected with
  `E-TERMINATION` ("no argument is known to be smaller"):

  ```
  def len : List Nat -> Nat
    | Nil => 0
    | Cons _ rest =>
      let r := rest
      1 + len r
  ```

  For the same reason as problem 1: the termination checker sees `r`, not
  `rest`.

- *Dot notation after an effectful `let`* (reported from day 4). With
  `def Grid : Type := List (List Nat)` and `def Grid.rolls (grid : Grid)`:

  ```
  def m () : {IO} () :=
    let grid := Grid.parse (List.map (\x => 0) (IO.readAllLines ()))
    print grid.rolls.toText
  ```

  gives `[E-UNKNOWN-FIELD] List has no field or function rolls`. The same
  `let` in a pure function (`let grid := Grid.parse lines`) works, and so
  does `let grid : Grid := …`. See §7.

**What works today** (as a workaround): a local `def` or `theorem` in a block.
Both `def p : Nat := n` and `theorem h : n <= Succ n := Nat.leSucc n` make
examples 1 and 2 check, because local definitions are lifted to top-level
definitions, which the checker can unfold. But that's a different feature
with a different cost (a lifted value is recomputed at every use; see §4.2).

## 2. How `let` works today, and why

### 2.1 The mechanism

There is **no `let` in the kernel's term language.** The core terms are
variables, definitions, data, constructors, `Pi`, `Lam`, `App`, annotations,
case trees, equality and `J` (`crates/core/src/term.rs:82-121`). So the
elaborator has to express a `let` with something else, and it does it in two
layers:

1. **Every `let` is treated as effectful code.** The function that decides
   whether an expression "may perform operations" answers *yes* for any
   `let`, sequence or `handle`, whatever is in it:

   ```rust
   // crates/elab/src/effects.rs:938, in may_perform
   Expr::Let { .. } | Expr::Seq(..) | Expr::Handle { .. } => true,
   ```

   So in a pure function, a block with a `let` goes down the effects path:
   `infer`/`check` hand it to `run_pure` (`crates/elab/src/check.rs:338-339`
   and `:1034-1035`), which elaborates the block as a computation over the
   *empty* set of abilities and wraps the result in `Effect.runPure`
   (`effects.rs:1835-1845`).
2. **A pure `let` inside a computation is a function applied to the value.**
   The code that builds the sequence (`effects.rs:1286-1324`) binds the
   name as an ordinary variable (`cx.bind(name, ty)`, which knows its type
   but not its value), elaborates the rest of the block, and emits

   ```
   (\name => rest) value          -- annotated with  (name : A) -> Comp … T
   ```

   with the comment "A pure `let` is `(\name -> body) term`, annotated so the
   kernel can check it" (`effects.rs:1309`). An effectful `let x := op ()`
   becomes `Effect.bind (op ()) (\x => rest)` instead.

So `theorem one` above becomes, roughly:

```
Effect.runPure ((\p => Done (Nat.leAddRight p 1)) n)
```

and the generated JavaScript for `let m := n + 1; m + m` really does build
and unwrap a `Done` at run time:

```js
const $Main$dtwice = (v0) => $Std$dEffect$drunPure(
  (((v1) => ({ tag: "Done", value: $Std$dNat$dadd(v1)(v1) })))($Std$dNat$dadd(v0)(1n)));
```

### 2.2 How that produces each symptom

- **Problem 1:** the body `(\p => …)` is checked with `p` as an unknown of
  type `Nat`. That's the ordinary rule for a function: a function must work
  for *every* argument, so it can't assume `p` is `n`. The kernel checks it
  the same way.
- **Problem 2:** `Comp` and `runPure` only take *types of data*:
  `type Effect.Comp (op : Type) (res : op -> Type) (a : Type) : Type` and
  `def Effect.runPure : [a : Type] -> Comp NoOp NoRes a -> a`
  (`crates/elab/src/prelude.sw:1982`, `:2115`). A proof's type is a
  proposition (`Prop`), not a `Type`, so `Comp … (n <= Succ (Succ n))` is a
  universe error. *The error comes from the effects wrapper, not from the
  `let` itself*: `(\h => body) proof` on its own would be fine.
- **Problem 3:** the `if` is elaborated as part of the computation, so each
  branch is `Done …` and the whole is under `runPure`.
- **Termination:** same as problem 1; `r` is a lambda's parameter.

### 2.3 Why it was built this way

From the history and the design notes:

- `let` arrived with abilities, in commit `8052ce2` ("Abilities and handlers
  in the source language"), whose message describes "blocks, where each line
  at the block's column is a statement (`let x = e`, or an expression run for
  its effects)". Blocks were designed *for effectful code*; a pure `let`
  reused that path. The abilities note says the same: "blocks with `let` and
  sequencing" are part of the effects work
  ([abilities.md](abilities.md), Status), and `docs/core.md:235` records
  "`let` and the lines of a block are `Effect.bind`s; a pure `let` is a
  beta-redex".
- The opacity was known and accepted. The syntax-conveniences note lists as a
  fact about the compiler: "**`let x = e` is a function applied to `e`**,
  `(\x -> body) e`, so `x` is computed once but is *opaque* in types"
  ([syntax-conveniences.md](syntax-conveniences.md), background, and §3.4:
  "Plain values stay `let`s … opaque in types. A value that must compute in
  types can be a function of `()` or move to top level").
- Not adding a kernel `let` kept the kernel smaller (DESIGN.md principle 4,
  "a small trusted kernel"). *This is my reading; no note says it in so many
  words.*
- Treating *every* `let` as effectful (rather than only those whose value or
  rest performs something) looks like a simplification, not a decision: I
  found no comment or note giving a reason. *Speculative.*

This is the same choice Idris 2 made, for a similar reason (§3).

## 3. What other languages do

| Language | Pure `let` in a term | Can the checker see the value? | Opaque form | Effectful binding | Sharing at run time |
|---|---|---|---|---|---|
| **Rocq (Coq)** | `let x := v in b`, a core term | **Yes.** The context holds the *definition* `x := v : T`; "ζ-reduction" replaces `x` by `v` | tactics like `assert` | (no effects) | yes |
| **Lean 4** | `let x := v; b`, a core term | **Yes** ("definitionally equal to … replacing every `a` in `t2` by `t1`") | **`have x := v; b`**: "the value of `x` is not accessible to `b`" | `let x ← e` in `do` (bind); `let x := e` in `do` stays a plain `let` | yes |
| **Agda** | `let x = v in b` | **Yes**, by substitution: "Agda inlines all let-bound variables during type checking"; no `let` in the internal syntax | none | (no effects) | **no**: "let-binding cannot be used to introduce sharing" |
| **Idris 2** | `let x = v in e` | **No**: "essentially equivalent to `(\x => e) val`", chosen because making it compute "would need significant changes to the way `case` and `with` are elaborated" | (that *is* the default) | `x <- e` in `do` | yes |
| Haskell | `let` | (no dependent types) | — | `x <- e` in `do`; `let` in `do` is pure | yes (lazy) |
| Koka | `val x = e` | (no dependent types) | — | the **same** `val` syntax; the compiler uses the effect types to translate only effectful code into bind form | yes |
| **Stitchwort today** | `(\x => b) v` inside `runPure` | **No** | (that's the default) | the same `let` syntax; becomes `Effect.bind` | yes (but via `Done`/`runPure`) |

Takeaways:

- **The proof assistants used for mathematics (Rocq, Lean) both have a
  transparent `let` in the kernel.** Lean adds an opaque `have`, mainly for
  proofs (where the value doesn't matter) and for performance: since Lean
  4.22, it even turns non-dependent `let`s into `have`s automatically so its
  simplifier works better.
- **Agda gets transparency by substitution**, and pays with no sharing: `let
  x = expensive` used twice computes `expensive` twice.
- **Idris 2 is where Stitchwort is now**, deliberately, and points users who
  need computation to local function definitions (as Stitchwort's local `def`
  already does).
- **Effects languages separate "pure let" from "bind" by effect types, not by
  syntax** (Koka) or by syntax (Haskell's `<-`, Lean's `←`). Either way, a
  `let` with no effects never pays for the effect machinery. Stitchwort's
  `let` uses one syntax like Koka, but currently treats every `let` as
  effectful, which is where problems 2 and 3 come from.

## 4. The theory in plain words

### 4.1 A context with definitions

When the checker works through a function body it keeps a *context*: the
variables in scope and their types, e.g. `n : Nat`. A transparent `let` adds a
second kind of entry, a variable **with its value**: `p : Nat := n`. Rocq's
manual describes exactly this: a local context is a list of declarations,
each either an assumption `x : T` or a definition `x := t : T`.

The typing rule (Rocq's "Let" rule, in words):

> If `v` has type `A`, and `b` has type `B` in the context extended with
> `x : A := v`, then `let x := v in b` has type `B` with `v` put in for `x`.

Two things make it work:

- **Inside `b`**, whenever the checker compares two types, it may replace
  `x` by `v` (this replacement is called **ζ-reduction**, "zeta"). That's
  what problem 1 needs: `Nat.leq p (p + 1)` becomes `Nat.leq n (n + 1)`.
- **The type of the whole** has `x` replaced by `v`, so `x` never escapes its
  scope. (`let n := 3 in (zeros n : Vec Nat n)` has type `Vec Nat 3`.)

Note what's *not* in the rule: any requirement on what kind of thing `A` is.
A proof, a number, a type: all the same. That's why problem 2 disappears.

### 4.2 Why it's sound, and how it differs from the alternatives

- **Sound because it adds nothing new.** Anything you can prove with a `let`
  you could prove by writing `v` everywhere `x` appears (that's the
  substitution rule: if `b` type-checks with `x := v`, then `b` with `v`
  pasted in type-checks too). A `let` is a convenience with sharing, not new
  logical power, so it can't make `Void` provable. It's in the kernels of
  Rocq and Lean.
- **Versus `(\x => b) v` (today):** the function form checks `b` for *every*
  `x`, which is stronger than needed and loses the value.
- **Versus inlining (Agda):** same checking power, but the program computes
  `v` once per use.
- **Versus a lifted local `def` (Stitchwort's local `def`, Idris 2's advice):**
  transparent, but a value without parameters is recomputed at every use
  (there's nothing to remember it), and it's a separate top-level
  definition.

### 4.3 Known pitfalls

- **Cost in types.** If types mention many nested `let`s, unfolding them can
  make normal forms large (in the worst case each `let` doubles the size).
  Lean added `have` partly for this. For Stitchwort's sizes this is unlikely
  to matter; `have` can be added later if it does.
- **Error messages.** After unfolding, messages may show `n` where the user
  wrote `p`. Rocq and Lean both have this; it's cosmetic.
- **Unknowns (metavariables).** An unknown's solution may only mention
  variables it's allowed to depend on. A `let`-bound variable is best left
  out of that list (its value already says what it depends on). Stitchwort's
  elaborator already does this for variables a pattern match has replaced by
  a constructor, so the machinery exists.
- **Effects.** A value produced by an *operation* (`let x := get ()`) can't
  be transparent: the value isn't known until a handler runs. Every language
  in §3 keeps that case as an opaque bind. Only pure `let`s become
  transparent.

## 5. Options for Stitchwort

Common to all three options, **step 0: a `let` isn't effectful unless its
value or the rest of the block is.** `may_perform` should look inside a
`let` (as it already does for `if` and `match`) instead of answering *yes*.
Then a pure function's block never goes through `Comp`/`runPure`. This alone,
an elaborator-only change of a few dozen lines, fixes problems 2 (proof
`let`s) and 3 (the `runPure`/`Done` trace in proofs and in the generated
JavaScript), because the remaining `(\h => body) proof` has no `Type`
restriction. It doesn't fix problem 1 or termination. *I haven't prototyped
step 0; the claim rests on the error coming from `Comp`/`runPure`'s
`[a : Type]` (§2.2) and on the `if` without a `let` elaborating as wanted
(example 3, `g`).*

### Option A: a transparent `let` in the kernel (Rocq/Lean style). **Recommended.**

- **Core:** a new term `Let(x, A, v, b)`, checked by the rule in §4.1. The
  kernel's context already stores, for each variable, *what it evaluates to*
  (inside a case branch, the matched variable already evaluates to the
  constructor value: `crates/core/src/check.rs:21-24`, `:520-531`), so a
  `let` just pushes `v` instead of a fresh variable. Evaluation computes `v`
  once and shares it. No new reduction machinery: values never contain a
  `Let`, so conversion is unchanged.
- **Elaborator:** step 0, then a pure `let` becomes `Let` instead of the
  annotated application, with the elaborator's context also recording the
  value (the same mechanism as case-branch refinement). An effectful
  `let x := op ()` stays `Effect.bind` (opaque, like Haskell's `<-` and
  Lean's `←`). A pure `let` inside an effectful block becomes a `Let` whose
  body is the rest of the computation, so it's transparent there too.
- **Fixes:** all of problems 1-3, and termination through `let r := rest`
  (the termination checker can treat `r` as `rest`; one more case to
  handle, not automatic).
- **Soundness:** §4.2. Kernel risk is small: one new term with the textbook
  rule, and the kernel already handles variables-with-values.
- **Erasure and JavaScript:** a `let` whose type is a proposition or a type
  is dropped at run time (one more rule in `erase.rs`; the JS backend
  already skips proofs). A data `let` becomes `const x = v;` (or the current
  arrow-function form) without `Done`/`runPure`: faster and smaller output.
- **Hashes:** every definition containing a `let` gets a new hash (a new term
  tag). Not a concern now.
- **Size:** medium. A new `Term` variant touches every pass over terms: term
  utilities, kernel check, evaluator (and the stack-safe stepper), quoting,
  pretty-printing, hashing, references, termination, erasure, JS, and in the
  elaborator the lifting/capture code and unification's term walks. Rough
  guess: 500-900 lines with tests, two or three lanes (step 0; kernel `Let`;
  elaborator + backends).

### Option B: no kernel change; make proof `let`s local theorems

- Step 0, then a `let` whose type is a proposition is elaborated as a lifted
  local `theorem` (the feature that already works, §1); data `let`s stay
  `(\x => b) v`.
- **Fixes:** problems 2 and 3. **Not** problem 1 or termination: data
  `let`s stay opaque, as in Idris 2. Users who need a transparent data value
  use a local `def` (recomputed at each use).
- **Soundness:** nothing new in the kernel. **Size:** small (≈150 lines).
- **Downside:** two kinds of `let` that behave differently depending on the
  value's type, which is surprising; and it doesn't meet the user's stated
  position for data.

### Option C: no kernel change; inline for checking (Agda style)

- Step 0, then the elaborator replaces `x` by the elaborated `v` everywhere
  in the rest of the block (it already has "a name that stands for a term"
  for local definitions, `bind_local` in `crates/elab/src/check.rs:159`).
- **Fixes:** problems 1-3 and termination.
- **Downside:** no sharing: `let big := expensive n` used three times runs
  `expensive n` three times, in the evaluator and in JavaScript. That's a
  real performance trap for AoC-style programs. Could be limited to proofs
  and types (which are erased, so duplication is free), but then data
  `let`s are opaque again and C collapses into B.

### Comparison

| | Step 0 alone | A: kernel `Let` | B: proof `let` = local theorem | C: inline |
|---|---|---|---|---|
| 1. value visible | no | **yes** | no (use local `def`) | **yes** |
| 2. proof `let` | **yes** | **yes** | **yes** | **yes** |
| 3. no `runPure` trace | **yes** | **yes** | **yes** | **yes** |
| termination through `let` | no | **yes** (one extra case) | no | **yes** |
| computed once | yes | **yes** | yes | **no** |
| kernel change | no | one term | no | no |
| size | small | medium | small | small |

## 6. Recommendation

**Option A, staged:** first step 0 on its own (small, elaborator only,
immediately removes problems 2 and 3 and the run-time `Done` wrapping), then
the kernel `Let` with the elaborator and backends. It's what Rocq and Lean
do, it matches the user's position (proofs and data alike, value visible),
it keeps sharing, and its kernel rule is the textbook one. An opaque `have`
can wait until a proof is slow because of a `let` (Lean's reason for it).

## 7. What happens to pattern `let` and the `if`-after-`let` case

- **`if` after `let`** (problem 3): fixed by step 0. The block becomes
  `Let m := n + 1 in (if …)`, and unfolding `f (n + 5)` gives exactly the
  `Decidable.elim … (\_ => 0) (\_ => n + 5 + 1)` you'd get without the
  `let`. No proof-only helpers needed.
- **Pattern `let` on a tuple or record**: a transparent `let` alone doesn't
  help, because the `match` is still stuck on an unknown `p`. Agda's answer
  fits well with option A: for a type with one constructor and no recursion
  (tuples, records), translate `let (a, b) := p` into `let a := p.fst; let
  b := p.snd` (Agda's manual: `let (c x y z) = t in u` binds "`x = f t`,
  `y = g t`, `z = h t`"). Then the block computes even when `p` is unknown,
  and the day 3 rewrite to `chosen.fst`/`chosen.snd` would have been
  unnecessary. Pattern `let`s on types with several constructors are
  already refused (`E-LET-REFUTABLE`); nested patterns and other
  one-constructor data types without field functions stay `match`es.
- **Dot notation and the declared type (`Grid` vs `List`).** The checker
  works with types *after* unfolding nicknames, so `grid`'s type is
  `List (List Nat)`. To find `Grid.rolls`, the elaborator separately
  records each variable's type *as written* (`Written` in
  `crates/elab/src/dot.rs:21-30`). A pure `let` records the written result
  type of its value, here `Grid` from `Grid.parse`'s signature
  (`written_of`, called from the pure branch of `comp_check`,
  `crates/elab/src/effects.rs:1103-1108`). The effectful branch (the value
  performs an operation, so the `let` becomes `Effect.bind`) records
  nothing (`effects.rs:1099-1102`), which is exactly the failing case. So
  this is a separate, small elaborator bug, not caused by `let`'s opacity,
  and option A doesn't fix it by itself. The design should keep the rule
  "a `let` variable's written type is the annotation if there is one, else
  the written result type of the value's outermost call", for **both**
  kinds of `let`: for an effectful value, the call that produces the bound
  result (`Grid.parse …` after its effectful arguments have been run) is a
  pure call, so `written_of` can be applied to it. With option A the pure
  `let` keeps doing what it does now (`written_of` on the value). I suggest
  fixing this in step 0, with a test that `grid.rolls` works after an
  effectful `let`.
- **Pair eta** (`p ≡ (p.fst, p.snd)`) is a separate kernel feature (a
  conversion rule, as in Agda's records "η-equality by default" and Lean's
  structure eta). It's needed for `sw (sw p) = p` by `rfl`, with or without
  this proposal. I suggest a separate note.

### 7.1 What this buys for the day 2 proof (block-walking spec = ID-walking spec)

The next proof the user wants is that day 2's specification, which walks
k-digit *blocks*, equals a brute-force one that walks *ids*. The current day
2 proofs (`aoc/day02.sw`, `specWindow` and friends) show the friction: long
nested `Bool.inspect (…) (\u => <the whole goal restated>)` terms, and
helpers that exist only because a `let` before an `if` left a `runPure`
term no lemma could mention. Under option A:

- **Proofs can name their steps.** `let hLo := lemmaA …` then
  `let hHi := lemmaB … hLo` then the final combination, instead of one
  nested expression. Today each such `let` is `E-UNIVERSE`.
- **Intermediate quantities can be named in proofs and functions alike.**
  `let lo := b * Succ m` in a lemma's proof, used where the goal says
  `b * Succ m`, is accepted, because `lo` unfolds (problem 1). The same in the
  spec functions means a lemma about them sees the arithmetic, not an opaque
  variable.
- **Functions with a `let` before an `if` unfold to ordinary terms**
  (`Decidable.elim …` / `ifThenElse …`), so lemmas about one step of a walk
  can be stated in source and used by rewriting, and no proof-only twin of
  the implementation is needed.
- **Walking functions can use `let` for the next position** (`let next :=
  rest`) and still pass the termination check (one extra case in the
  checker, §A.3).
- **Tuple state** (`let (lo, hi) := r` on an unknown `r`) computes after the
  projection translation of §7, so a lemma about a walk over an arbitrary
  range doesn't get stuck on the `match`.

What this proposal does *not* provide, and that such a proof may still want:
pair eta (above), and conveniences for equational reasoning (a `calc`-style
chain, or rewriting by an equation without writing the motive for `J` /
`Bool.inspect` by hand). Those are separate items; I'd look at the proof
after option A lands before designing them.

## 8. Open questions for the user

1. Go with option A, staged as step 0 first, then the kernel `Let`?
   [Yes.]
2. Add an opaque `have x := proof` now, as Lean has? [No; add it only if a
   proof gets slow because of a `let`.]
3. Translate tuple/record pattern `let`s into projections (§7) as part of
   this work? [Yes, in the elaborator lane after the kernel `Let`.]
4. Pair/record eta: a separate design note? [Yes, separate; it's a
   conversion-rule change with its own soundness questions.]
5. Fix dot notation after an effectful `let` (`grid.rolls`, §7) in step 0?
   [Yes; it's small and independent of the kernel change.]

## Sources

- Lean: *Theorem Proving in Lean 4*, "Dependent Type Theory", Local
  Definitions: <https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/>
  ("`let a := t1; t2` is definitionally equal to the result of replacing
  every occurrence of `a` in `t2` by `t1`").
- Lean: `letFun` / `have`: <https://lean-lang.org/doc/api/Init/LetFun.html>
  ("equal to `(fun x => b) v`, so the value of `x` is not accessible to
  `b`").
- Lean 4.22 release notes (non-dependent `let` turned into `have`; `have` is
  `let +nondep`): <https://lean-lang.org/doc/reference/latest/releases/v4.22.0/>
- Lean `do` notation (`let x ← e` is bind; `let x := e` is a plain `let`):
  <https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/>
- Rocq reference manual, Calculus of Inductive Constructions (local
  contexts with definitions `x := t : T`; the Let rule):
  <https://rocq-prover.org/doc/V8.20.0/refman/language/cic.html>
- Rocq reference manual, conversion rules (ζ-reduction, δ for local
  definitions): <https://rocq-prover.org/doc/V8.20.0/refman/language/core/conversion.html>
- Agda: let and where: <https://agda.readthedocs.io/en/latest/language/let-and-where.html>
  ("Agda inlines all let-bound variables during type checking"; "let-binding
  cannot be used to introduce sharing"; record patterns in `let`).
- Agda: record types (η-equality by default):
  <https://agda.readthedocs.io/en/latest/language/record-types.html>
- Idris 2: changes since Idris 1:
  <https://idris2.readthedocs.io/en/latest/updates/updates.html> (`let x =
  val in e` is "essentially equivalent to `(\x => e) val`"; use local
  function definitions for computation).
- Haskell 2010 report, `do` expressions (`let` vs `<-`):
  <https://www.haskell.org/onlinereport/haskell2010/haskellch3.html#x8-470003.14>
- Koka: D. Leijen, "Type directed compilation of row-typed algebraic
  effects", POPL 2017 (only effectful code is translated to bind form):
  <https://www.microsoft.com/en-us/research/publication/type-directed-compilation-of-row-typed-algebraic-effects/>
  *(cited from memory, not re-read for this note).*

## Appendix: details for the reviewer

### A.1 Evidence for §2 (at `74b22c4`)

| Claim | Where |
|---|---|
| No `Let` in core terms | `crates/core/src/term.rs:82-121` (`enum Term`) |
| Every `let` "may perform" | `crates/elab/src/effects.rs:938` |
| Pure contexts route such code to `run_pure` | `crates/elab/src/check.rs:338-339` (infer), `:1034-1035` (check); `infer_inner` has `unreachable!` for `Let` at `:359` |
| `run_pure` = computation over the empty row + `Effect.runPure` | `crates/elab/src/effects.rs:1835-1845` |
| `let` in computation mode | `effects.rs:1075-1115` (`comp_check`, `Expr::Let`) |
| Pure `let` = annotated beta-redex; effectful = `Effect.bind` | `effects.rs:1286-1324` (`sequence`; comment at `:1309`) |
| `if` in computation mode checks branches against `Comp …` | `effects.rs:1130-1157` |
| `Comp`, `runPure` take `Type` | `crates/elab/src/prelude.sw:1982`, `:2115` |
| Kernel context maps variables to values; case branches substitute | `crates/core/src/check.rs:20-27`, `:520-531` |
| Elaborator context has the same, plus name-for-term locals | `crates/elab/src/check.rs:26-31`, `:136-148`, `:159` (`bind_local`) |
| Pattern `let` is a one-alternative `match` | `crates/syntax/src/parser.rs:877` (`MatchKind::Let`); `docs/syntax.md` "Patterns in `let` and lambdas" |
| Design statements of opacity | `docs/proposals/syntax-conveniences.md` (background bullet "`let x = e` is a function applied to `e`"; §3.4); `docs/core.md:235` |
| History | `8052ce2` (abilities; `let` introduced with blocks), `ec2a784` (pattern `let`), `ddd7b2f` (local definitions) |
| JS output with `Done`/`runPure` | `stitchwort build --js` on `export def twice (n : Nat) : Nat := let m := n + 1; m + m` (as a block) |

Repro files used for §1 (scratch, not committed): examples 1-4 as shown,
the `len` example, and the local `def`/`theorem` workaround, which checks.

### A.2 Kernel rule for option A

```
Γ ⊢ A : Sort s      Γ ⊢ v : A      Γ, x : A := v ⊢ b : B
────────────────────────────────────────────────────────  (Let)
            Γ ⊢ Let(x, A, v, b) : B[v/x]
```

In the NbE checker this is: check `A` is a type, check `v` against `eval A`,
push `env = eval v`, `types = eval A`, then infer/check `b`. Because the
body's type is a *value* computed in an environment where `x` evaluates to
`v`, it contains no reference to `x`'s level, so it can be used (and quoted)
outside the `let` directly: the "must not escape" condition holds by
construction. `eval(Let(x, A, v, b), env) = eval(b, env ++ [eval(v, env)])`
(strict, shared). Quoting never produces `Let`.

Checking mode: `check(Let(x, A, v, b), T)` = the same, then `check(b, T)`.
The annotation `A` can be required in core terms (the elaborator always
knows it), which keeps the kernel's `Let` inferable.

### A.3 Points to settle during implementation

- **Case trees.** A `Case` may only appear at the top of a body, on a
  parameter or a field (the fresh-wrapper invariant, [abilities.md
  §"The fresh-wrapper invariant"](abilities.md)). A `Let` should initially be
  a leaf expression only, never a tree node, and `Case` on a `let`-bound
  variable stays forbidden (a `match` on one is lifted as today). Allowing
  `Let` *above* a `Case` on a parameter (useful for `where` values at the
  start of an equation) is a possible later relaxation.
- **Lifting.** A `match` (or local `def`) after a `let` is lifted to a
  helper that receives the `let` variable as an argument, so inside the
  helper the value is opaque again. The helper's call site still computes, so
  proofs about the outer function unfold fine; only proofs *inside* the
  helper body that need the value would notice. Option: capture the value
  (pass `v`'s free variables and re-`let` it inside), later if needed.
- **Metavariables.** Exclude `let`-bound variables from the spine of new
  metavariables, as variables refined by a case branch are excluded today
  (`docs/core.md`, "Metavariables").
- **Termination.** In `termination.rs`, a `let`-bound variable whose value
  is a field of a parameter should count as that field. Without this,
  `len` above still fails (but the user can inline).
- **Erasure.** `erase.rs`: a `Let` whose `A` is a proposition or a type
  former isn't evaluated when running (placeholder), like rule 1 for
  arguments. JS: emit nothing for it.
- **Stack safety.** `step.rs` (stack-safe evaluation) needs a `Let` frame;
  the differential test (`crates/driver/tests/differential.rs`) should get
  `let` cases.
- **Effects.** `may_perform(Let)` = `may_perform(value) ||
  may_perform(body)`; `infer_inner`/`check` gain a pure `Let` case;
  `sequence`'s pure branch emits `Let` instead of the annotated redex. A
  `let` in a `partial` function (a `Delay` computation) behaves the same.
  `Expr::Seq` (a statement run only for effects) can stay as it is: in a
  pure block it does nothing useful, and it could become a warning.
- **Dot notation.** A pure `let` already records the variable's type "as
  written" for dot notation (`cx.set_written`); keep that for the kernel
  `Let`. Add it for effectful `let`s: in `comp_call`, the final pure call
  (after effectful arguments are bound) is a term `written_of` accepts; return
  its written type alongside the computation. Accept test: the `grid.rolls`
  example in §1.
- **Tests.** Accept: the four examples; a type-level `let` (`let n := 3;
  (zeros n : Vec Nat n)`); a proof `let` used twice; a `let` inside an
  effectful block used in a type; `len`. Reject: using an effectful `let`'s
  value in a type (must stay opaque); a kernel `Let` whose value doesn't
  match its annotation; a mutated hash-pinned term (to show the kernel, not
  just the elaborator, checks `Let`).
