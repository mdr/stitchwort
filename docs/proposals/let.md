# Proposal: `let` that holds proofs and data, and whose value the checker can see

**Status:** Draft 2 (after review), 19 October 2026. Decided: option A,
staged (§6, §8). All three stages are implemented; §A.7 records how stage 3
was done and what it left.

Draft 2 folds in an independent review. Its points are now part of the
design itself (the rules in §6.1 and the stages in §6.2), not a list of
comments; §A.6 records how each point was handled.

This note can be read without knowing the codebase. The main part takes about
15 minutes; the [appendix](#appendix-details-for-the-reviewer) has the
details a reviewer needs (file and line references, the typing rule, the
pieces of the compiler each stage touches).

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
Effect.runPure (Decidable.elim (…) (_  => Done 0) (_  => Done (n + 5 + 1)))
```

while the same function without the `let` gets stuck on the
`Decidable.elim (…) (_ => 0) (_ => n + 5 + 1)` you'd expect. The
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
    let grid := Grid.parse (List.map (x => 0) (IO.readAllLines ()))
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
   (name => rest) value          -- annotated with  (name : A) -> Comp … T
   ```

   with the comment "A pure `let` is `(name => body) term`, annotated so the
   kernel can check it" (`effects.rs:1309`). An effectful `let x := op ()`
   becomes `Effect.bind (op ()) (x => rest)` instead.

So `theorem one` above becomes, roughly:

```
Effect.runPure ((p  => Done (Nat.leAddRight p 1)) n)
```

and the generated JavaScript for `let m := n + 1; m + m` really does build
and unwrap a `Done` at run time:

```js
const $Main$dtwice = (v0) => $Std$dEffect$drunPure(
  (((v1) => ({ tag: "Done", value: $Std$dNat$dadd(v1)(v1) })))($Std$dNat$dadd(v0)(1n)));
```

### 2.2 How that produces each symptom

- **Problem 1:** the body `(p => …)` is checked with `p` as an unknown of
  type `Nat`. That's the ordinary rule for a function: a function must work
  for *every* argument, so it can't assume `p` is `n`. The kernel checks it
  the same way.
- **Problem 2:** `Comp` and `runPure` only take *types of data*:
  `type Effect.Comp (op : Type) (res : op -> Type) (a : Type) : Type` and
  `def Effect.runPure : [a : Type] -> Comp NoOp NoRes a -> a`
  (`crates/elab/src/prelude.sw:1982`, `:2115`). A proof's type is a
  proposition (`Prop`), not a `Type`, so `Comp … (n <= Succ (Succ n))` is a
  universe error. *The error comes from the effects wrapper, not from the
  `let` itself*: `(h => body) proof` on its own would be fine.
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
  `(x => body) e`, so `x` is computed once but is *opaque* in types"
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
| **Idris 2** | `let x = v in e` | **No**: "essentially equivalent to `(x => e) val`", chosen because making it compute "would need significant changes to the way `case` and `with` are elaborated" | (that *is* the default) | `x <- e` in `do` | yes |
| Haskell | `let` | (no dependent types) | — | `x <- e` in `do`; `let` in `do` is pure | yes (lazy) |
| Koka | `val x = e` | (no dependent types) | — | the **same** `val` syntax; the compiler uses the effect types to translate only effectful code into bind form | yes |
| **Stitchwort today** | `(x  => b) v` inside `runPure` | **No** | (that's the default) | the same `let` syntax; becomes `Effect.bind` | yes (but via `Done`/`runPure`) |

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
- **Versus `(x => b) v` (today):** the function form checks `b` for *every*
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
  Running the program shares each value, but the *checker* can still
  duplicate large terms when it writes a value back out as a term (for an
  error message, a metavariable's solution, or a lifted helper). Lean added
  `have` partly for this. We don't add `have` now; instead one deliberately
  nasty test (deeply nested `let`s, each using the previous one twice) must
  finish, or stop cleanly, under the existing work budget (§6.2, stage 3).
- **Error messages.** After unfolding, messages may show `n` where the user
  wrote `p`. Rocq and Lean both have this; it's cosmetic.
- **Unknowns (metavariables).** The elaborator fills in unknowns (implicit
  arguments, `_`) by solving equations. A solution is a term that will be
  used elsewhere, possibly outside the `let`, so it must never mention the
  `let`'s variable `x` after `x` has gone out of scope: it must mention `v`
  instead. This is a rule the implementation has to keep (§6.1, rule 2), and
  stage 2 includes checking the solver against it.
- **Effects.** A value produced by an *operation* (`let x := get ()`) can't
  be transparent: the value isn't known until a handler runs, so it can't
  be known while checking. Every language in §3 keeps that case as an
  opaque bind; for Stitchwort this is necessary, not just convenient. Only
  pure `let`s become transparent. Note that "pure" is about what *computing
  the value* does now: `let f := u => get ()` binds a function, and making
  a function performs nothing, so it's a pure (transparent) `let` even
  though *calling* `f` later performs `get`.

## 5. Options for Stitchwort

Common to all three options, **step 0: a `let` isn't effectful unless its
value or the rest of the block is.** `may_perform` should look inside a
`let` (as it already does for `if` and `match`) instead of answering *yes*.
Then a pure function's block never goes through `Comp`/`runPure`. This alone,
an elaborator-only change, fixes problems 2 (proof `let`s) and 3 (the
`runPure`/`Done` trace in proofs and in the generated JavaScript), because
the remaining `(h => body) proof` has no `Type` restriction and computes
away like any other function application. It doesn't fix problem 1 or
termination. *I haven't prototyped step 0; the claim rests on the error
coming from `Comp`/`runPure`'s `[a : Type]` (§2.2) and on the `if` without
a `let` elaborating as wanted (example 3).*

Step 0 involves **two separate decisions**, and they look at different
things:

1. **Does the whole block go through the effects machinery?** That depends on
   the whole thing: `let x := v; rest` may perform if `v` may, *or* `rest`
   may.
2. **How is `x` bound?** That depends on `v` alone:

   | `v` | `rest` | `x` is bound by |
   |---|---|---|
   | pure | pure | an ordinary pure binding (no effects machinery) |
   | pure | effectful | a pure binding (transparent once `Let` exists) around the rest of the computation |
   | effectful | either | `Effect.bind`: `x` is opaque, whatever `rest` does |

   So "the block is effectful" must never be read as "so use bind": a pure
   value stays a pure binding even in an effectful block.

Step 0 also fixes the separate dot-notation bug after an effectful `let`
(`grid.rolls`, §1 and §7), since that code is being changed anyway.

### Option A: a transparent `let` in the kernel (Rocq/Lean style). **Recommended.**

- **Core:** a new term `Let(x, A, v, b)`, checked by the rule in §4.1. The
  kernel's context already stores, for each variable, *what it evaluates to*
  (inside a case branch, the matched variable already evaluates to the
  constructor value: `crates/core/src/check.rs:21-24`, `:520-531`), so a
  `let` just pushes `v` instead of a fresh variable. Evaluation computes `v`
  once and shares it. Because evaluated values never contain a `Let`, **the
  comparison of two values (the conversion check) needs no new case**. That
  is narrower than "nothing changes": evaluation, extending the context,
  turning values back into terms (quoting), and any shortcuts in the
  comparison all meet the new term, and must keep the bookkeeping rule in
  §6.1 (rule 1).
- **Elaborator:** step 0, then a pure `let` becomes `Let` instead of the
  annotated application, with the elaborator's context also recording the
  value (the same mechanism as case-branch refinement). An effectful
  `let x := op ()` stays `Effect.bind` (opaque, like Haskell's `<-` and
  Lean's `←`). A pure `let` inside an effectful block becomes a `Let` whose
  body is the rest of the computation, so it's transparent there too.
- **Fixes:** all of problems 1-3, and termination through `let r := rest`
  (the termination checker treats `r` exactly as it treats `rest`; one more
  case to handle, not automatic).
- **Soundness:** §4.2. Kernel risk is small: one new term with the textbook
  rule, and the kernel already handles variables-with-values. The risks are
  in the bookkeeping around it, which §6.1 turns into rules and tests.
- **Erasure and JavaScript:** a `let` is erased exactly when a function
  parameter of the same type would be (a proof, or a type): the existing
  rule, applied to one more kind of binder. A data `let` becomes
  `const x = v;` (or the current arrow-function form) without
  `Done`/`runPure`: faster and smaller output.
- **Hashes:** every definition containing a `let` gets a new hash (a new term
  tag). Not a concern now.
- **Size:** medium. A new `Term` variant touches every pass over terms: term
  utilities, kernel check, evaluator (and the stack-safe stepper), quoting,
  pretty-printing, hashing, references, termination, erasure, JS, and in the
  elaborator the lifting/capture code and unification's term walks. Rough
  guess: 800-1200 lines with tests, in three stages (§6.2).

### Option B: no kernel change; make proof `let`s local theorems

- Step 0, then a `let` whose type is a proposition is elaborated as a lifted
  local `theorem` (the feature that already works, §1); data `let`s stay
  `(x => b) v`.
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

## 6. Decision and plan

**Option A, staged** (decided, §8): first step 0 on its own (small,
elaborator only, immediately removes problems 2 and 3 and the run-time
`Done` wrapping), then the kernel `Let`, then the elaborator and backends.
It's what Rocq and Lean do, it matches the user's position (proofs and data
alike, value visible), it keeps sharing, and its kernel rule is the
textbook one. An opaque `have` waits until a proof is slow because of a
`let` (Lean's reason for it).

### 6.1 Rules the implementation must keep

The typing rule is standard and adds no new logic (§4.2). What can go wrong
is bookkeeping: keeping straight a `let`'s *name*, its *value*, and the
unknowns that are allowed to appear in types. These rules are part of the
design; each has tests in §6.2.

1. **A `let` takes a slot, but adds no unknown.** In the context, `x`
   occupies a position like any variable (so variable numbering in terms
   counts it). But when the checker evaluates, `x` *is* `v`: no "unknown
   `x`" ever appears in a computed type, so nothing that mentions `x` can
   leak out of the `let`'s scope. (Details: §A.2.)
2. **No unknown's solution mentions a `let` variable that has gone out of
   scope.** Where `x` would appear, the solution has `v` (as `f v`, never as
   `f x`). This covers both an unknown created *before* the `let` and solved
   inside it, and one created *inside* the `let` whose solution is used after
   it. Stage 2 checks the solver against this rather than assuming it.
   (Details and what the code does today: §A.3.)
3. **Termination: `let x := v` is exactly as small as `v`.** Whatever the
   termination checker knows about `v` (strictly smaller than a parameter,
   equal to one, or unknown) it knows about `x`, no more. It looks for
   recursive calls in both `v` and the rest of the block, so a recursive
   call can't hide in a `let`'s value. It decides this from the terms, not
   by asking whether `x` and `v` compute to the same thing.
4. **Lifted helpers keep what a `let` holds.** A `match` or local `def`
   after a `let` is moved into a separate generated function (§A.4). That
   function must still know `x := v`: it receives the variables `v` needs
   and re-creates `let x := v` inside, rather than receiving `x` as a plain
   argument. This is in the first implementation, not a later improvement,
   since otherwise "later lines know what a `let` holds" would be false
   inside every `match`.
5. **Erasure follows the existing rule.** A `let` is dropped at run time
   exactly when a function parameter of its type would be (its type is a
   proposition, or it's a type), using the same test the compiler already
   uses for parameters; otherwise it's computed once, before the rest.
6. **Effects: the value decides the binding.** As in the step-0 table (§5):
   only an effectful value makes `x` opaque. Making a function that performs
   something when called is pure.

### 6.2 Implementation stages

Each stage is a separate lane, merged and checked before the next starts.
Sizes are rough guesses, including tests.

**Stage 1: step 0, and dot notation after an effectful `let`.**
*Scope:* `may_perform` looks inside `let` (the whole block may perform if the
value or the rest may); binding follows the value (§5 table); a pure block
no longer goes through `Comp`/`runPure`. The pure binding stays the
annotated `(x => rest) v` for now. Fix `grid.rolls`: an effectful `let`
records the written type of the pure call that produces its result.
*Files:* `crates/elab/src/effects.rs` (`may_perform`, `comp_check`,
`sequence`, `comp_call`), `crates/elab/src/check.rs` (`infer`/`check` gain a
pure-block case instead of handing it to `run_pure`).
*Tests:* problem 2 (proof `let`) and problem 3 (`f (n + 5)` unfolds to
`Decidable.elim … (_ => 0) …`) accepted; generated JS for `twice` has no
`Done`/`runPure`; `let f := u  => get (); …` in a pure function is pure;
an effectful value still binds with `Effect.bind`, and a pure value inside
an effectful block doesn't; `grid.rolls` after an effectful `let`.
*Size:* small, about 150-250 lines.

**Stage 2: the kernel `Let`.**
*Scope:* the new core term and its rule (§A.2) in every pass over terms in
`crates/core`: checking, evaluation (and the stack-safe stepper), quoting,
printing, hashing, references; the audit of the solver against rule 2.
*Files:* `crates/core/src/term.rs`, `check.rs`, `value.rs`, `step.rs`,
hashing and printing; `crates/elab/src/unify.rs` (audit; §A.3).
*Tests:* a hand-built `Let` checks; one whose value doesn't match its
annotation is rejected; a mutated hash-pinned `Let` is rejected by the
kernel. For rule 1: a `let` followed by a dependent function or `Pi` whose
type is shown or used outside the `let`; nested `let`s under binders
(`a => let x := … a …; b => let y := … x … b …; …`); the type-level
`let n := 3; (zeros n : Vec Nat n)`. For rule 2: an unknown created before
a `let` and solved inside it; one created inside and used after it; both
must end up mentioning `v`, not `x`. Differential tests
(`crates/driver/tests/differential.rs`) get `let` cases.
*Size:* medium, about 300-450 lines.

**Stage 3: the elaborator and backends use `Let`.**
*Scope:* pure `let`s elaborate to `Let`, so values are visible (problem 1);
lifted `match`/local `def` helpers re-create `let`s (rule 4, §A.4);
termination (rule 3); erasure and JavaScript (rule 5); tuple and record
pattern `let`s become projections (§7).
*Files:* `crates/elab/src/effects.rs`, `check.rs`, `lift.rs`,
`matching.rs`, `local.rs`; `crates/core/src/termination.rs`,
`crates/core/src/erase.rs`; `crates/js/src/lib.rs`; the parser's pattern
`let` translation.
*Tests:* problem 1 (`one`); `len` accepted; a recursive call inside a `let`'s
value still checked (a non-terminating one rejected); the dependent `match`
test below; a proof `let` used twice; a `let` inside an effectful block used
in a type; using an effectful `let`'s value in a type is rejected; a proof
`let` emits nothing in JS; `let (a, b) := p` on an unknown `p` computes;
`let (a, b) := expensive` evaluates `expensive` once; the nested-`let` cost
test (§4.3). The dependent `match` test:

```
theorem t (xs : List Nat) : … :=
  let ys := xs
  match ys with
  | Nil       => … (a goal that mentions xs) …
  | Cons y zs => …
```

where the branches only check if the helper still knows `ys` is `xs`.
*Size:* medium, about 350-500 lines.

## 7. What happens to pattern `let` and the `if`-after-`let` case

- **`if` after `let`** (problem 3): fixed by step 0. The block becomes
  `Let m := n + 1 in (if …)`, and unfolding `f (n + 5)` gives exactly the
  `Decidable.elim … (_ => 0) (_ => n + 5 + 1)` you'd get without the
  `let`. No proof-only helpers needed.
- **Pattern `let` on a tuple or record**: a transparent `let` alone doesn't
  help, because the `match` is still stuck on an unknown `p`. Agda's answer
  fits well with option A: for a type with one constructor and no recursion
  (tuples, records), bind each name to a field (Agda's manual:
  `let (c x y z) = t in u` binds "`x = f t`, `y = g t`, `z = h t`"). To
  compute the right-hand side only once, it goes into a hidden temporary
  first:

  ```
  let (a, b) := e     becomes     let tmp := e
                                  let a := tmp.fst
                                  let b := tmp.snd
  ```

  (When `e` is already a variable, `tmp` is unnecessary.) `tmp` can't be
  referred to and doesn't appear in error messages. Nested tuple and record
  patterns repeat this: `let ((a, b), c) := e` binds `tmp := e`, then
  `tmp2 := tmp.fst`, `a := tmp2.fst`, `b := tmp2.snd`, `c := tmp.snd`. Then
  the block computes even when `e` is unknown, and the day 3 rewrite to
  `chosen.fst`/`chosen.snd` would have been unnecessary. Pattern `let`s on
  types with several constructors are already refused (`E-LET-REFUTABLE`);
  other one-constructor data types without field functions stay `match`es.
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
  `let` keeps doing what it does now (`written_of` on the value). Fixed in
  stage 1, with a test that `grid.rolls` works after an effectful `let`.
- **Pair eta** (`p ≡ (p.fst, p.snd)`) is a separate kernel feature (a
  conversion rule, as in Agda's records "η-equality by default" and Lean's
  structure eta). It's needed for `sw (sw p) = p` by `rfl`, with or without
  this proposal: a transparent `let` tells the checker `x` is `v`, but says
  nothing about an arbitrary unknown pair. It gets its own note (§8).

### 7.1 What this buys for the day 2 proof (block-walking spec = ID-walking spec)

The next proof the user wants is that day 2's specification, which walks
k-digit *blocks*, equals a brute-force one that walks *ids*. The current day
2 proofs (`aoc/day02.sw`, `specWindow` and friends) show the friction: long
nested `Bool.inspect (…) (u => <the whole goal restated>)` terms, and
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
  checker, §6.1 rule 3).
- **Tuple state** (`let (lo, hi) := r` on an unknown `r`) computes after the
  projection translation of §7, so a lemma about a walk over an arbitrary
  range doesn't get stuck on the `match`.

What this proposal does *not* provide, and that such a proof may still want:
pair eta (above), and conveniences for equational reasoning (a `calc`-style
chain, or rewriting by an equation without writing the motive for `J` /
`Bool.inspect` by hand). Those are separate items; I'd look at the proof
after option A lands before designing them.

## 8. Decisions (19 October 2026)

1. **Option A, with step 0 first**, then the kernel `Let`, then the
   elaborator and backends (§6.2).
2. **No `have` now.** An opaque `have x := proof` is added only if a proof
   gets slow because of a `let`.
3. **Tuple and record pattern `let`s become projections** (§7), through a
   hidden temporary so the value is computed once; in stage 3.
4. **Pair/record eta gets a separate note.** It's a change to the
   conversion rule with its own soundness questions.
5. **Dot notation after an effectful `let` (`grid.rolls`) is fixed in step
   0** (stage 1).

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
  val in e` is "essentially equivalent to `(x => e) val`"; use local
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
knows it), which keeps the kernel's `Let` inferable. The premise is
`A : Sort s` for any `s`: a proof (`A : Prop`), data (`A : Type u`) and a
type (`A` a universe) all go through the same rule.

**The NbE invariant (rule 1 of §6.1).** Two numberings must not be
confused:

- *syntactic* positions: de Bruijn indices in terms, and the context depth.
  `x` occupies a slot, so terms under the `let` count it, and `Var` indices
  in `b` are shifted by one;
- *semantic* neutral levels: the `Value::Neutral(Head::Var(l), _)` that
  stand for unknown variables. A transparent `let` creates **none**: its
  slot's environment entry is `eval v`, so no value can contain a neutral
  for `x`'s level.

The "doesn't escape" argument above depends on exactly this. A fresh
neutral is created at level `cx.level()` = the context length, so after a
`let` the levels in use have a gap at `x`'s slot. That gap already occurs
for case-branch refinement (`crates/core/src/check.rs:20-27`; the
elaborator's `Ctx::fresh_meta`, `crates/elab/src/check.rs:265-276`, skips
any slot whose value isn't its own neutral), so quoting at a depth that
counts the slot is the existing convention. Tests in stage 2 (§6.2):
a dependent `Pi`/lambda after a `let` whose type is quoted outside the `let`;
nested `let`s under binders. Strict evaluation means an unused data `let`'s
value is still computed when the program runs; that's a cost, not a change
of meaning, since the value is pure and total. While *checking*, the value is
computed only when needed (§A.3, "Cost at check time").

### A.3 Metavariables: the invariant and the audit

**Invariant (rule 2 of §6.1):** no metavariable solution may contain a
reference to an out-of-scope transparent local definition; occurrences of
that local are replaced by (evaluated to) its value first.

What the code does today (read for this draft, *not run*):

- `crates/elab/src/unify.rs:311` (`solve`) takes the spine's arguments,
  which must force to distinct bare neutrals `Head::Var(l)`, and builds the
  solution with `rename` (`:342`), which works on *forced semantic values*:
  the only way it emits `Term::Var` is for a neutral `Head::Var(l)` found in
  the renaming, and any other variable fails (`Fail::No`). Since a
  transparent `let` slot evaluates to `v`, never to a neutral (A.2), a
  solution can only ever contain `v`'s value. *So the invariant probably
  holds without change; this is a reading of the code, not a test.*
- `Ctx::fresh_meta` (`crates/elab/src/check.rs:265-276`) and
  `lift::spine` (`crates/elab/src/lift.rs:133`) leave a slot out of a new
  metavariable's spine when its value isn't its own neutral. A `let` slot
  qualifies automatically, so "exclude `let` variables from the spine"
  needs no new code.
- The places to audit are those that work on *terms* rather than values,
  where a syntactic `Var` for `x` could be carried across the `let`'s
  scope: `zonk`/`zonk_keeping` (`unify.rs:488`, `:495`), lifting's
  `unrefine`/`replace` (`lift.rs:548`, `:140-200`), matching's
  generalisation (`matching.rs`), and any code that quotes a value at a
  depth computed differently from `cx.level()`. The audit is a step of
  stage 2: list each such site and say why it's safe, or fix it.

Tests (both directions): a metavariable created outside the `let` and solved
inside it (e.g. an implicit argument whose solution is `f x` must be
recorded as `f v`); a metavariable created inside the `let` whose solution
is used after it.

**Audit result (stage 2, at the commit that adds the kernel `Let`).** The
invariant holds at every site below, by reading the code; the elaborator
doesn't yet put a `let` in its context (stage 3), so the two tests above
can't run end to end yet and move to stage 3. What makes each site safe,
and what stage 3 must keep true:

| Site | Works on | Why no out-of-scope `x` can appear |
|---|---|---|
| `solve`, `rename` (`crates/elab/src/unify.rs:311`, `:342`) | values | A solution emits `Term::Var` only for a spine variable, which must force to a bare `Head::Var(l)` with an empty spine. A `let` slot never evaluates to a neutral of its own level, so it can't be in a spine, and an occurrence of `x` in the right-hand side has already become `v`'s value. Holds as long as the elaborator puts `v`'s value (or a deferred value that isn't a bare neutral of the slot's level) in the slot. |
| `Ctx::fresh_meta` (`crates/elab/src/check.rs:268`), `lift::spine` (`crates/elab/src/lift.rs:133`), the matching copies (`crates/elab/src/matching.rs:325`) | environment | All test `is_var(env[l], l)`: a slot whose value is its own neutral is a plain variable. A `let` slot holding `v`'s value fails the test, so it's left out of a new metavariable's spine and never copied. **Stage 3 caveat:** if the elaborator defers a `let`'s value the way the kernel does (below), its placeholder must not be the slot's own neutral, or these three sites would take the `let` for a plain variable and put it in spines; give pending slots a test of their own. |
| `zonk_keeping` (`crates/elab/src/unify.rs:495`, `Let` case `:542`) | terms | It rewrites a term in place; under a `Let` it counts the slot (`level + 1`). A metavariable application is evaluated in an environment of plain variables, so its result may mention `x` syntactically, but only at a position inside `x`'s scope, where the term was. Its output isn't a metavariable solution. |
| `go_replace`/`unrefine` (`crates/elab/src/lift.rs:164`, `Let` case `:213`; `:551`) | terms | A `Let` inside the lifted term binds its own slot (`under + 1`), so its variable stays a variable. A `let` slot in the *context* (stage 3) isn't `is_var`, so `unrefine` replaces it by `quote` of its value: no `x` escapes, though the value is pasted unshared (§A.4, rule 4, stage 3). |
| Quoting (`crates/core/src/value.rs` `quote`) | values | Values contain no neutral for a `let` slot (A.2), and quoting never produces `Let`. |
| Kernel context (`crates/core/src/check.rs:75` `define`, `:94` `eval`) | both | Every evaluation goes through `Ctx::eval`, which computes the pending `let`s a term mentions before evaluating it, so no value the checker builds sees the placeholder; case refinement, which rewrites the whole environment, computes every pending `let` first (`:558`, `:705`). |

**Cost at check time (added in stage 2, decided by the user on 19 October
2026).** The function form `(x => b) v` cost nothing to check unless a type
needed `v` (`Closure::apply_lazy`), and a kernel `Let` that evaluated `v` on
entry would have made every closed `let` cost its value at check time. So the
kernel computes a `let`'s value only when checking first evaluates a term
that mentions it, and then once: the context holds the value term
(`Ctx::define`), and `Ctx::eval` computes the pending `let`s a term mentions,
in their own scope (each value's own pending `let`s first). This is a local
definition held in the checker's context, not a new kind of value: values
never contain a deferred computation, so quoting, conversion and the
evaluator are unchanged, and nothing deferred reaches a term or the
elaborator. The kernel has no metavariables, so a computed value can't go
stale; exhaustion while computing one is an `E-RESOURCE` error and leaves it
pending. Running a program stays strict (`value.rs`, `Frame::LetBody`). An
application's argument whose result type mentions it is computed through the
same path (`check.rs:276`).

Measured (release build, the prelude, `List.length xs` as the body):
checking `let xs := List.range 200000; …` takes about 3 µs, the same as the
function form (about 4 µs); evaluating the value, which a strict rule would
add, takes about 83 ms. Tests: `crates/core/tests/let_term.rs`
(`a_value_no_type_needs_is_not_computed_while_checking`, which also shows a
value used twice in types is computed once, and
`a_pending_let_computes_the_ones_its_value_mentions`).

**Nested-`let` cost.** The adversarial test (20 `let`s on an unknown `a`,
each the previous one used twice, compared and printed) passes under the
default limits without reaching them, but takes about 8 s per check in a
debug build: a neutral value's spine isn't shared, so `x20`'s value is a tree
of 2^20 nodes once built. That's the evaluator's value representation, not
the `let` rule (the function form would build the same value once a type
needed it).

### A.4 Lifting with re-created `let`s

How capture works today (from `crates/elab/src/lift.rs`, read, not run): a
lifted `match` or local `def` is elaborated in place and recorded as a
`Draft` holding a copy of the context's `env` (`lift.rs:99-129`). When it's
resolved, `unrefine` (`lift.rs:548-564`) rewrites the helper's body and type:
each slot whose `env` entry is a plain variable stays a variable (and may
become a capture); every other slot (today, only a variable a case branch
replaced by a constructor) is replaced by `quote` of its value. Captures are
then computed from the rewritten terms (`captures`, `:570`).

*Consequence (speculative, not tested):* with a transparent `let` slot and
no other change, `unrefine` would already paste the **normal form** of `v`
wherever `x` occurs in the helper. That keeps the value visible, but loses
sharing (`v` recomputed at each use in the helper) and can blow up the
helper's size. So the original concern (the helper sees `x` as an opaque
argument) wouldn't quite happen, but the default behaviour is still wrong.

Plan for stage 3:

- The context records, for each `let` slot, its elaborated value term and
  type (beside `env`), and `Draft` copies it.
- In the helper's **body**, `unrefine` doesn't paste `v`: it keeps `x` and
  re-creates `Let(x, A, v', …)` inside the helper, where `v'` is `v` after
  the same `unrefine` (so `v`'s free variables become captures by the
  existing rules, and a `let` whose value uses an earlier `let` re-creates
  that one first). Because a `Let` is only a leaf for now (A.5, case trees),
  it's re-created at the top of each leaf of the helper's case tree that
  uses `x`; only one leaf runs, so `v` is still computed at most once per
  call.
- In the helper's **type** (its result type and its captures' types), `x`
  is replaced by `v'` (types are erased, so this costs nothing at run time).
- A `match` on `x` itself: the scrutinee isn't a plain variable, so today's
  generalisation applies (`matching.rs:10-19`): a new variable stands for
  the scrutinee, and occurrences of its value in the goal are replaced by
  it. For `let ys := xs; match ys with …` that abstracts `xs` in the goal,
  which is what the dependent test in §6.2 needs. *Unverified; the test
  decides.*

### A.5 Other points to settle during implementation

- **Case trees.** A `Case` may only appear at the top of a body, on a
  parameter or a field (the fresh-wrapper invariant, [abilities.md
  §"The fresh-wrapper invariant"](abilities.md)). A `Let` should initially be
  a leaf expression only, never a tree node, and `Case` on a `let`-bound
  variable stays forbidden (a `match` on one is lifted as today). Allowing
  `Let` *above* a `Case` on a parameter (useful for `where` values at the
  start of an equation) is a possible later relaxation.
- **Lifting.** §A.4.
- **Metavariables.** §A.3.
- **Termination.** `crates/core/src/termination.rs` computes, for each
  argument of a recursive call, its relation to the caller's parameters
  (`<`, `≤`, unknown) from the terms alone (module comment, lines 19-35).
  A `Let` slot gets *exactly the relation computed for `v`*: a strict
  descendant stays `<`, the parameter (or its rebuilt constructor) stays
  `≤`, anything else is unknown. This accepts `len` without creating any new
  evidence of descent. The traversal walks both `v` and `b` for calls (the
  module's "every occurrence of a member is a call" rule extends to `Let`'s
  value). Never use conversion (`x ≡ v`) to derive descent.
- **Erasure.** `crates/core/src/erase.rs` erases a definition's parameter
  when the kernel's relevance test `is_erased` holds for its type
  (`crates/core/src/check.rs:1627`: a type former, or a type in `Prop`),
  via `telescope`. A `Let` uses the *same* test on `A`: if the binder would
  be erased as a parameter, its value isn't evaluated when running (the
  placeholder takes the slot, as for an erased argument) and JS emits
  nothing for it; otherwise it's evaluated once, strictly, before the body.
  No second "is this a proof?" test; elimination of a proof into data stays
  governed by the existing `E-PROP-ELIM` rule. The JS backend
  (`crates/js/src/lib.rs`) already uses the kernel's erasure information.
- **Stack safety.** The stack-safe evaluator needs a `Let` frame (it's in
  `value.rs`, `Frame::LetBody`; `step.rs` runs `Delay` values and needed no
  change);
  the differential test (`crates/driver/tests/differential.rs`) should get
  `let` cases.
- **Effects.** `may_perform(let x := v; rest)` = `may_perform(v) ||
  may_perform(rest)` classifies the block; the binding follows `v` alone
  (§5 table). `may_perform` tracks what *evaluating* the expression
  performs now, not effects latent in a returned function, so `let f := u
  => get ()` is pure (lambda bodies already don't count,
  `effects.rs:909`). `may_perform(rest)` must be asked with `x` bound
  and its type known, as `Expr::LocalDefs` already does ("asked again once
  the names are in scope", `effects.rs:938-941`), so that a call of `x`
  is judged by `x`'s type. *Checked in stage 1:* `call_performs` finds a
  bound variable's type through `head_type` (`cx.lookup`), so with `x` in
  scope a call of an effectful `x` is judged effectful. Before `x` is bound
  (the first question, on the whole `let`) the name isn't in scope and the
  call is judged by whatever else the name means, usually nothing (pure);
  the rest is asked again once `x` is bound, so the call is then run with
  `runPure` (in a pure function: `E-ABILITY` unless handled), as for local
  definitions. Tests: `examples/accept/let-pure.sw`,
  `examples/reject/let-bound-effectful-call.sw`. `infer_inner`/`check` gain a pure
  `Let` case; `sequence`'s pure branch emits `Let` (stage 3) instead of the
  annotated redex (stage 1). A `let` in a `partial` function (a `Delay`
  computation) behaves the same. `Expr::Seq` (a statement run only for
  effects) can stay as it is: in a pure block it does nothing useful, and it
  could become a warning.
- **Pattern `let`s.** The projection translation (§7) is done where pattern
  `let` is turned into a one-alternative `match` today
  (`crates/syntax/src/parser.rs:877`, `MatchKind::Let`) or in the
  elaborator, whichever knows the type is a tuple or record; the temporary
  gets a name the user can't write and is hidden from diagnostics.
- **Compile-time cost.** One adversarial test: about 20 nested `let`s, each
  defined from the previous one used twice, used in a type that must be
  compared and printed. It must pass, or fail with the existing
  resource-limit error, under the existing work budget (`g.budget`); it
  must not hang or exhaust memory.
- **Dot notation.** A pure `let` already records the variable's type "as
  written" for dot notation (`cx.set_written`); keep that for the kernel
  `Let`. Add it for effectful `let`s: in `comp_call`, the final pure call
  (after effectful arguments are bound) is a term `written_of` accepts; return
  its written type alongside the computation. Accept test: the `grid.rolls`
  example in §1.
- **Tests.** Listed per stage in §6.2.

### A.6 How the review was handled

The independent review (19 October 2026) agreed with option A staged after
step 0, and with the five decisions. Each point and where it now lives:

| Review point | Where |
|---|---|
| 1. "conversion is unchanged" too strong; NbE level invariant; tests | §5 option A wording; §6.1 rule 1; §A.2; stage 2 tests |
| 2. Metavariable invariant, audit, tests both ways | §4.3; §6.1 rule 2; §A.3; stage 2 |
| 3. Termination provenance = provenance of `v`; walk value and body | §6.1 rule 3; §A.5 |
| 4. Lifting must preserve `x := v` in the first implementation | §6.1 rule 4; §A.4; stage 3 dependent `match` test |
| 5. Step 0: classify the block vs choose the binding | §5 table; §A.5 effects |
| 6. Erasure as the existing relevance judgement | §5 option A; §6.1 rule 5; §A.5 |
| 7. Pattern `let`: single evaluation via a temporary | §7; §A.5 |
| 8. Compile-time cost: adversarial test under the budget | §4.3; §A.5; stage 3 |
| 9. Effectful-`let` opacity necessary; latent effects are pure | §4.3; §6.1 rule 6 |
| 10. Comparison to Rocq/Lean | no change needed |

Two refinements of the review, from reading the code (not disagreements
with its conclusions):

- **Lifting.** Draft 1 said a helper would receive `x` as an opaque
  argument; the review took that at face value. Reading `lift.rs`, the
  existing `unrefine` would more likely paste `v`'s normal form into the
  helper (§A.4), so the value stays visible but unshared. Re-creating the
  `let`, as the review prefers, is still the right fix; the reason is
  sharing and size as much as transparency.
- **Metavariables.** The review asked for an audit rather than an
  assumption. The solver (`unify.rs`) works over semantic values, so the
  invariant probably holds there already; the audit's real targets are the
  term-level passes (`zonk`, lifting, generalisation), listed in §A.3.

### A.7 Stage 3 as implemented

What the elaborator and backends do now, and where it departs from the plan
above.

- **The context.** `Ctx::define` (`crates/elab/src/check.rs`) binds a pure
  `let`; `effects::pure_let` and the pure branch of `sequence` emit
  `Let(x, A, v, rest)`. `Ctx::lets` records each slot's type and value
  terms, for lifting. A value that is quick to compute (under a small work
  budget, `unify::cheaply`; most are, being stuck on variables) is computed
  when bound. Otherwise the slot is *deferred*: it holds a solved
  metavariable applied to a dummy and the context, `?d _ x₀ … xₙ`, whose
  solution is `_ x₀ … xₙ => v`, so anything that forces the value computes
  it, and a `let` of a long list in `main` costs nothing to check. This is
  the marker the stage 2 audit asked for: a deferred slot is never its own
  variable, so `fresh_meta`, matching and `lift::spine`'s variable test
  leave it alone, and with the context in its spine a case split's
  refinement reaches it. A forced deferred value isn't cached.
- **Lifting (rule 4).** A helper re-creates the `let`s it uses at the top
  of each leaf of its case tree (and inside a local definition's
  parameters), with the `let`s their types and values use, in order
  (`Elaborator::unrefine_body`, `with_lets` in `lift.rs`). The value's free
  variables become captures by the existing rules. A helper's *frozen*
  metavariable (never solved by unification) has the `let`s in scope in
  its spine (`lift::spine`), so a call that passes something using a `let`
  (a generalised scrutinee) passes the variable and shares the value.
  `match` on a `let`'s name generalises it as before, and in the
  alternatives the name is the matched value (`matching.rs`, `alias`): so
  `let ys := xs; match ys with | Cons y zs => … ys …` sees `ys` as
  `Cons y zs`. The kernel's `Let` records that a value the body doesn't use
  is skipped when running, so the owner's copy of a `let` only the helper
  uses costs nothing.
- **Folding solutions back (rule 2's other side).** A metavariable's
  solution mentions a `let`'s value, never its variable, so a solution the
  program runs would compute the value again: a decision procedure for
  `if m < 3` after `let m := n + 1` was `decLessEq (n + 1) 2`. Zonking
  (`unify::zonk_in`) folds occurrences of each enclosing `let`'s value
  (its normal form, when that's cheap to compute) back to the variable,
  outermost first, and lifting does the same for the `let`s it re-creates.
- **Termination (rule 3).** Nothing further was needed in the elaborator:
  `len` with `let r := rest` is checked by the kernel's rule from stage 2.
- **Erasure (rule 5).** `Term::Let` has a fifth field, set by the kernel
  when it checks the `let`: running skips the value (the placeholder takes
  the slot) when `A` is a proposition or a type former, by the parameter
  test, or when the body doesn't use `x`. Hashing ignores it (it's
  determined by the rest). JS emits nothing for a skipped `let`, a
  `const` for one in a case tree's leaf (so a self-tail-call loop keeps its
  `let`s per turn), and an applied arrow function inside an expression.
- **Pattern `let`s (§7).** `crates/elab/src/patlet.rs`: a `let` whose
  pattern is made of tuples, records, variables and `_` binds projections
  (`Pair.fst`, `Pair.snd`, the records' generated projections) through a
  hidden `%p` (none when the right-hand side is a variable). *Departure:*
  where the expected type is evidently a proposition, the `match` is kept,
  since there splitting a variable refines the goal, which a proof by
  `let (a, b) := p` relies on (`examples/accept/let-patterns.sw`,
  `swapTwice`). Projections give no evidence of descent to the termination
  checker, unlike the `match` did.
- **AoC.** Answers unchanged; `stitchwort check` times unchanged within
  noise. Day 2's local `terms` now takes `size` as a parameter: its proofs
  state lemmas for any `size`, and a re-created `let` would have made
  `terms` know the digit count instead.

Leftovers: a forced deferred value is recomputed at each forcing; the
adversarial nested `let`s (20 deep, each the previous one twice) check in
about 5 s in a release build, mostly comparing two copies of a 2^20-node
value (no sharing in neutral spines), and the false claim's error message is
about 5 MB; a lifted local definition recomputes a re-created `let`'s value
at each call; pattern `let`s in proofs and on other single-constructor types
stay `match`es.
