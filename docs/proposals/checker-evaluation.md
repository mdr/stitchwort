# Proposal: the type checker should compute only what it needs

**Status:** Draft 1, 19 October 2026. Analysis and options; nothing is
implemented. Measured at `8e3d71c`. One scratch prototype (stage 1 below) was
built, measured and thrown away.

The main part takes about 15 minutes to read. The
[appendix](#appendix-details-for-the-reviewer) has the file and line
references, every measurement, and the prototype, for an independent reviewer.

## 1. The problem in one example

```
def main () : {IO} () := print (Nat.toText (List.length (List.range 200000)))
```

`stitchwort check` takes 0.45 s on this; an empty program takes 0.14 s. The
difference is the type checker building the 200,000-element list and counting
it, **twice**, although `print`'s type (`Text -> {IO} ()`) doesn't depend on
what's printed. `stitchwort run` then computes it a third time, which is the
only one that's needed.

The user's point: there are many places, especially in program bodies, where
the checker doesn't need to know a value exactly, and it shouldn't compute it
there. This note finds those places, explains why they happen, compares with
how Lean, Agda, Rocq and Idris avoid the same work, and proposes a staged plan.

## 2. Why the checker computes: the short explanation

A dependently typed checker sometimes *must* compute. In `rfl : 2 + 2 = 4`, the
only way to check the proof is to work out `2 + 2`. In `Vec Nat (n + 1)`, the
type contains a value. So every such checker has an evaluator inside it.

The question is *how much* it computes when it does. There are two styles:

- **Eager (call-by-value, "compute everything you're given"):** whenever a
  value goes into a type, compute it completely, then carry the finished
  result around. This is how Stitchwort's checker works today.
- **On demand ("lazy"):** carry the *expression* around, and compute only the
  part a question needs, at the moment it's asked. To check that `V cost` and
  `V cost` are the same type, notice that both sides are literally the same
  and stop; to check `rfl : cost = 200000`, compute `cost` because that
  question needs it. This is how Lean, Agda, Rocq and Idris all work (§4).

Stitchwort's evaluator is one machine shared by the checker and by
`stitchwort run` (`crates/core/src/value.rs`). It is strict: when a function's
argument is evaluated, it is evaluated fully, and a definition with all its
arguments runs as soon as it can (`value.rs:5-7`, `unfold` at `value.rs:900`).
That's the right design for running programs. For checking it means "whenever
a value enters a type, compute it to the end".

There is already one place that avoids this: `Closure::apply_lazy`
(`value.rs:216`). When the checker applies `f a` and works out its type
`B[a]`, it computes `a` only if `B` *mentions* the parameter at all. That is
why `f (List.length (List.range 200000))` with `f : Nat -> Nat` costs nothing
extra (measured, §3). But "mentions" is all or nothing: as soon as the type
mentions the argument in any way, the argument is computed completely.

## 3. Where the checker over-computes (measured)

Each program below uses `def cost : Nat := List.length (List.range 200000)`,
which takes about **0.155 s** to compute once (`stitchwort run` adds exactly
that). So "extra time ÷ 0.155" counts how many times the checker computed
`cost`. Times are the best of 3, release build, Apple M-series laptop; the
empty-program baseline is 0.14 s.

| # | Program (body) | `check` time | times `cost` computed | Needed? |
|---|---|---:|---:|---|
| 1 | `f cost` with `f : Nat -> Nat` | 0.14 s | 0 | no, and it isn't (`apply_lazy`) |
| 2 | `cost \|> Nat.toText` | 0.14 s | 0 | no |
| 3 | `let n := cost` then `n + 1` | 0.15 s | 0 | no |
| 4 | `print (Nat.toText cost)` in `main` | 0.45 s | **2** | no |
| 5 | the same with two `print`s | 0.75 s | **4** | no |
| 6 | `cost.toText` (dot notation) | 0.30 s | **1** | no |
| 7 | `cost == 5` (a `Bool`) | 0.45 s | **2** | no |
| 8 | `if cost < 5 then 1 else 2` | 0.76 s | **4** | no |
| 9 | `mk cost : V cost` (`V` indexed by a `Nat`) | 0.90 s | **5** | no: both sides are literally `V cost` |
| 10 | `f cost : cost = cost` with `f (n : Nat) : n = n` | 1.04 s | **6** | no, same reason |
| 11 | `rfl : cost = cost` | 0.75 s | **4** | at most 2; 0 if identical sides are noticed |
| 12 | `test "…" := cost == 200000` | 0.47 s | 2 at `check` | the test needs 1, at `test` time |
| 13 | `List.range 100000 == List.range 100000` | fails: **`E-RESOURCE`** | — | no |
| 14 | a record `p` with a proof field, then `rfl : p.position = 1000000` | 0.66 s (0.15 s without the `rfl`) | the *proof* is computed | no: only `position` is asked for |

Three causes explain all of these.

**Cause 1: values are put into types instead of names for them** (rows 4–8).
The elaborator evaluates an argument up front to build a type, even where the
type turns out not to need it.

- An operation call (`print x`): `effects::make_call` evaluates `x`
  (`crates/elab/src/effects.rs:1764`) to compute `print`'s result type. The
  kernel then re-checks the generated `Call (print x) rest`, and because the
  constructor `Call`'s second field has type `res o -> …` (it mentions the
  first field), the kernel evaluates the first field, `print x`, which
  evaluates `x` again (`crates/core/src/check.rs:286-294`). That's the 2 in
  row 4.
- Dot notation: the receiver is evaluated unconditionally
  (`crates/elab/src/dot.rs:654`, `:772`).
- `==` and `if`: `a == b` is elaborated by evaluating the proposition `a = b`
  (`crates/elab/src/numbers.rs:541`) to search for a decision procedure, and
  `if` evaluates the proposition and its negation (`crates/elab/src/check.rs:1292`,
  `:1314-1316`). The search only needs the proposition's *shape* (an equation
  between two `Nat`s, a `<=`), not the numbers.

**Cause 2: computing is all or nothing** (rows 9–11, 14). Once a value must go
into a type, the strict evaluator computes it completely, including parts no
one looks at:

- `V cost` versus `V cost` is decided by computing `cost` on both sides
  and comparing 200000 with 200000. Lean would see two identical expressions
  and stop.
- Every type is computed twice, once by the elaborator and once by the
  independent kernel re-check. That doubling is deliberate (the kernel is the
  trusted judge) and isn't the problem; what it doubles is.
- Proofs are computed too. While checking, nothing is erased (erasure is only
  on while running), so evaluating a record that contains a proof computes the
  proof (row 14: 0.5 s spent on `Nat.leAddRight 1000000 1`, a proof that
  `1000000 <= 1000001` built by a million recursive steps). This is the TODO's
  "the checker evaluates proofs inside concrete types".

**Cause 3: computed values replace the program's own expressions** (row 13).
When the checker fills in hidden arguments (`_`), it solves them from the
*computed* type, so the solution is the computed value, not the short
expression it came from. For `xs == ys` the decision search
(`crates/elab/src/auto.rs:342-395`) solves the hidden list arguments of the
list decision procedure to the two fully built 100,000-element lists, and
those become part of the elaborated program as list literals. The kernel then
checks a 100,000-deep literal with its recursive checker and stops with
`E-RESOURCE` (it's fine at 20,000, and fine for `List.range n == List.range n`
with `n` a parameter). The same thing is in TODO.md for `sym rfl`, whose
hidden arguments are "solved to the list". *That the 100,000-deep literal is
what trips the depth guard is inferred from the code and these measurements,
not traced line by line.* The TODO item "`long n == long n` gives
`E-RESOURCE` at 100,000 characters" fits this cause; I didn't reproduce that
exact program.

## 4. How other languages avoid this

All four established systems compute on demand. None of them evaluates an
argument just because it appears in a type.

**Lean 4.** Terms are kept as expressions; instantiating a function type
`(x : A) -> B` with an argument substitutes the expression, without
evaluating it. Computation happens only through `whnf` ("weak head normal
form": compute just until the outermost shape is known, e.g. "it's a `Cons`",
leaving the fields uncomputed). Equality of types (`isDefEq`, and the kernel's
own check) first tries cheap tests (the same object, the same constant applied
to equal arguments) and only then unfolds definitions, one at a time, choosing
which side to unfold by "definitional height": *lazy delta reduction*. Users
can mark definitions `@[reducible]` or `@[irreducible]` to steer unfolding.
Proofs are never computed to compare them (proof irrelevance). Failed
comparisons are cached. The kernel re-checks everything, as Stitchwort's
does, but with the same lazy machinery.
([Type Checking in Lean 4: definitional equality](https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html);
[Lean reducibility attributes](https://lean-lang.org/doc/api/Lean/ReducibilityAttrs.html);
[Lean 4.9.0 on transparency trade-offs](https://blog.lean-lang.org/blog/2024-7-1-lean-490).)

**Agda.** The checker's evaluator is a call-by-need abstract machine: it
computes to weak head normal form, and arguments are computed only if
inspected, at most once per reduction
([Agda 2.5.4 changelog, "Call-by-need reduction"](https://hackage.haskell.org/package/Agda-2.5.4/changelog);
[Agda.TypeChecking.Reduce.Fast](https://hackage-content-origin.haskell.org/package/Agda-2.6.1.3/docs/Agda-TypeChecking-Reduce-Fast.html);
a `--call-by-name` flag was added later to turn the sharing off,
[2.6.2 changelog](https://hackage.haskell.org/package/Agda-2.6.2/changelog)).

**Rocq (Coq).** The kernel's conversion check uses a lazy machine ("a call by
need strategy, with sharing of reductions") and unfolds constants one at a
time, by a configurable `Strategy` level; `Opaque` makes conversion "delay
unfolding the specified constants as much as possible". Full, eager
computation (`vm_compute`, `native_compute`, which "first normalizes the terms
before comparing them") is used only when the user asks for it, for
computation-heavy proofs
([Rocq manual: conversion, Strategy, vm_compute](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html)).

**Idris 2.** Values in the checker hold their constructor and function
arguments as *closures* (an unevaluated term plus its environment); the source
says "'Closure' is an unevaluated thunk, which means we can wait until
necessary to reduce constructor arguments"
([Idris2 `src/Core/Value.idr`](https://github.com/idris-lang/Idris2/blob/main/src/Core/Value.idr);
[Brady, Idris 2, ECOOP 2021](https://arxiv.org/abs/2104.00480)).

**smalltt / András Kovács.** smalltt is a small, very fast elaborator built to
demonstrate techniques. Its main one is *glued evaluation*: a call of a
top-level definition is kept both as "this definition applied to these
arguments" and as its lazily computed unfolding. Comparison tries the folded
form first and unfolds only on failure ("approximate conversion checking ...
deciding conversion without computing all beta-redexes"), and solutions of
hidden arguments use the folded form, so they stay small. The README notes "a
noticeable constant overhead during evaluation but overall the trade-off is
well worth it"
([smalltt README](https://github.com/AndrasKovacs/smalltt);
[elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo), the series
Stitchwort's environment-based evaluator resembles).

**What this means for Stitchwort.** Stitchwort is the odd one out: a strict
evaluator inside the checker. That was a sensible start (one evaluator,
shared with `run`, easy to trust and test), and the costs above are the price.
The others show two separate ideas, which can be adopted separately:

1. **Name, don't compute** (Lean's substitution of expressions): when a type
   needs "the argument", give it a *name* for the argument, and compute only if
   a question requires it.
2. **Compute only the outer layer, and only on demand** (whnf, call-by-need,
   glued values): when computing is needed, stop as soon as the question is
   answered.

## 5. Options

Gains are from §3's measurements where stated, otherwise estimates.

**(a) Targeted: bind instead of evaluate, in the elaborator.** Where the
elaborator now evaluates an argument to build a type (operation calls, dot
receivers, `==`/`if`), it binds the argument to a variable instead, works out
the type with the variable, and emits `(\x => …) arg`, exactly as a pure
`let` is emitted today (which is why row 3 costs nothing). If the type turns
out to mention the variable, fall back to today's code. The kernel then never
evaluates the argument either, because the lambda's type doesn't depend on
it, so `apply_lazy` skips it.
*Gain:* rows 4–8 and 13 to zero. **Prototyped for `print`:** 0.45 s → 0.14 s,
two `print`s 0.75 s → 0.14 s, `run` output unchanged, and all 73 programs in
`examples/accept/` and `aoc/` give the same `stitchwort test` result
(appendix A.4). *Size:* small (tens of lines per site). *Risk:* none to the
kernel (no kernel change; the kernel still checks the output). Generated JS
gets one extra immediately applied function per site (cheap, removable later),
and term hashes change (not a goal to keep). *Run time:* one extra
function application per call site; negligible.

**(b) Lazy argument values (thunks) while checking.** A new kind of value,
"this term in this environment, not computed yet", created where the checker
puts an argument into a type (`apply_lazy`, constructor fields, a kernel
`let`), and computed at most once, when something looks inside it (a `case`, a
native operation, comparison, printing). Two lazy values for the same term and
environment are equal without computing either. Only the checker makes them;
`run` (erasure on) never does, so the run-time evaluator stays strict.
*Gain:* rows 9–11 and 14 (`V cost` against `V cost` is equal without
computing; the proof field in row 14 is never looked at); fewer, smaller
hidden-argument solutions. *Size:* medium–large. There is a useful
foothold: solved metavariables already are "values that may need forcing",
with a `force` function called before looking inside a value (about 90 call
sites, `value.rs:251`, `needs_forcing` at `value.rs:833`), and a thunk could
follow the same discipline. *Risk:* this is the trusted core. Soundness rests
on Stitchwort being pure and total: computing fewer things, later, gives the
same answers (no effect can be skipped, nothing can fail to finish, and
`Partial` code only runs through its opaque `Delay`). The danger is a missed
`force`, which would make the checker *reject* a correct program or, worse,
compare a thunk wrongly; the existing recursive reference evaluator
(`crates/core/src/reference.rs`) and differential tests are the guard. Resource
limits change shape (work moves to where it's needed).

**(c) Weak-head evaluation and lazy unfolding in comparison.** Compare
"definition `d` applied to `x`" with "`d` applied to `y`" by comparing `x` and
`y` before unfolding `d`; unfold one side at a time. Meaningless without (b)
or (d), because today both sides were fully computed before comparison starts
(`conv` at `value.rs:1134` only ever sees finished values). So this is part of
(b)/(d), not a separate step.

**(d) Glued values (Kovács).** Calls of definitions stay folded, carrying a
lazily computed unfolding; comparison, hidden-argument solutions and error
messages use the folded form. *Gain:* everything (b) gives, plus small
solutions (row 13 and the `sym rfl` TODO item at the root), plus error messages
that say `cost` rather than `200000`. *Size:* large; it changes the value type
everywhere in `crates/core` and `crates/elab`. *Risk:* as (b), larger. Worth
it only if (a) and (b) leave real programs slow.

**(e) Memoisation.** Remember the value of a closed constant like `cost`
after computing it once (today each mention computes it again:
`value.rs:505`), or remember comparison results. *Gain:* rows 9–11 would
compute `cost` once instead of 4–6 times, but only for named constants; the
inline `List.length (List.range 200000)` gets nothing. *Size:* small. *Risk:*
memory (a million-element constant stays alive for the whole check), and the
cache must be separate for checking and running (erased values differ).
Lean and Rocq do cache; here it is a low priority.

**What not to change.**

- `stitchwort run` stays strict; its speed work is the separate speed report.
  Any laziness is for checking only.
- `rfl`, `test` and `decide` still compute when they need to: that's
  their job. They should compute *once*, not 2–6 times.
- The kernel keeps re-checking the elaborator's output independently.
- No user-visible strategy annotations (Lean's `@[irreducible]`, Rocq's
  `Strategy`) unless a real program needs them.

## 6. Recommendation: a staged plan

**Stage 1 (small, elaborator only, now).** Option (a) at the three sites:
operation calls (`make_call`), dot receivers, and `==`/`if`/`decide` (run the
decision search on the proposition with its operands bound as variables, then
apply the result to the real operands). Note: `effects.rs` is being changed by
the `let` stage-1 lane, so this lands after it.
*Tests:* add check-time cases to the benchmark suite (`bench/`, which already
records deterministic step counts and has `check-*` entries), each a program
whose check work must **not grow** with the size of a closed input: rows 4, 5,
6, 7, 8 and 13 above at two sizes (e.g. 20,000 and 200,000), asserting equal
step counts. Row 13 becomes an accept example. Plus `run` output unchanged for
`examples/` and the differential tests.

**Coordinate with the `let` design (stage 2, the kernel `Let`).** Today a pure
`let x := v` costs nothing at check time (row 3) because it's emitted as
`(\x => …) v`. A transparent kernel `Let` that *evaluates* `v` into the
context, with today's strict evaluator, would compute every closed `let` value
while checking (twice: elaborator and kernel). Either the kernel `Let` holds
its value lazily (a first, contained use of option (b)), or that cost is
accepted knowingly. This should be settled before let stage 2 starts. (This
note does not change the `let` design otherwise; see
`docs/proposals/let.md`.)

**Stage 2 (medium–large, core, after stage 1 and let stage 2).** Option (b),
lazy argument values while checking, starting at the narrowest places
(`apply_lazy` and constructor fields that later field types mention, and the
`let` slot), with a "same term, same environment" shortcut in comparison.
Gate: the differential tests against the reference evaluator, and the new
benchmarks for rows 9–11 and 14. Opus, with a design review first.

**Stage 3 (only if needed).** Glued values, option (d), if real programs
(AoC proofs, large literals in types) still show check-time blow-ups or giant
hidden-argument solutions after stage 2. Memoisation (e) only if a program
shows repeated computation of named constants.

## 7. Open questions for the user

1. **Stage 1 now, as a small lane?** It's elaborator-only, prototyped for
   `print`, and turns the known "`print` computed twice" and the `==`
   `E-RESOURCE` into zero cost. [Yes; after the `let` stage-1 lane merges,
   since both touch `effects.rs`.]
2. **The kernel `Let` (let stage 2): lazy value, or accept computing every
   closed `let` value at check time?** [Lazy: a contained thunk for the `let`
   slot only, designed as part of let stage 2, so stage 2 here can reuse it.]
3. **Is option (b) worth the risk to the trusted core, given that stage 1
   removes the cases seen so far in real programs?** [Decide after stage 1:
   measure AoC check times again; do (b) if any program spends more than a
   second checking on values its types don't need.]

---

## Appendix: details for the reviewer

### A.1 The evaluator and the checker (at `8e3d71c`)

- One machine for checking and running: `crates/core/src/value.rs`, `run`
  (`:406`). Erasure (`crates/core/src/erase.rs`) is on only while running, so
  while checking, proofs and types are computed like data.
- Reduction policy (`value.rs:5-7`, `unfold` `:900-930`): a definition stays
  folded only until it has all its parameters **and** its case tree can take a
  step; then it runs. So the result of `eval` is fully computed except under
  lambdas and where stuck on a variable or unsolved metavariable. Arguments
  are computed before the call (`eval_step`, `Term::App`, `:544-570`).
- A closed constant (arity 0) is recomputed at every mention
  (`eval_step`, `value.rs:505`): there is no cache.
- `Closure::apply_lazy` (`value.rs:216-226`): computes the argument only if
  `self.body.mentions(0)`, a syntactic test on the codomain term
  (`term.rs:403`). Used by the kernel's application rule
  (`check.rs:190`) and the elaborator's argument loop
  (`crates/elab/src/check.rs:759, 777, 786, 793`; `numbers.rs:776`).
- Constructor and data parameters: the kernel and elaborator evaluate a field
  only if a later field's type mentions it (`later_types_mention`,
  `core/src/check.rs:659-665`; uses at `:146`, `:291`;
  `elab/src/check.rs:1752`). Otherwise `unused()` stands in.
- Comparison (`conv`, `value.rs:1134-1350`) works on finished values, layer by
  layer, without recursion; it never unfolds anything because nothing is left
  to unfold except stuck definitions (compared by head and arguments) and
  eta. No pointer-equality shortcut (values of the same term in the same
  environment are compared structurally).
- Metavariables: `force` (`value.rs:251`) replaces a solved metavariable at
  the head of a value; the machine forces scrutinees (`needs_forcing`,
  `:833`). About 90 `force(` call sites across `crates/elab` and `crates/core`
  (grep count), and about 520 `Value::` pattern sites, which bounds the size of
  option (b) or (d).

### A.2 Every evaluation site found, and whether its result is needed

Kernel (`crates/core/src/check.rs`):

| Site | What | Needed? |
|---|---|---|
| `:144-147` data parameters | parameter types; a parameter's value if later ones mention it | yes for indices; computed fully |
| `:175` Pi domain | the domain type | yes (types are small) |
| `:190` application | argument, only if the codomain mentions it | when mentioned, fully computed though often only compared |
| `:205`, `:211` annotations, typed equations | the annotation type | yes; any values in it computed fully |
| `:263` lambda body | codomain applied to a fresh variable | cheap |
| `:289-294` constructor fields | field value if a later field's type mentions it | for `Comp.Call` (`prelude.sw:1984`, `rest : res o -> …`) the operation, including its argument, is computed though `res` looks only at which operation it is |
| `:311` `rfl` | compares the two (already computed) sides | yes, legitimately |
| `:337` check by inference | compares two computed types | yes; cost is in computing them |
| `:397`, `:404` `J` | motive and proof | yes |
| `:532`, `:620` case branches | goal with the scrutinee replaced by the pattern | yes |
| `:826`, `:840`, `:915`, ... | declared types | yes; any values in them computed fully |

Elaborator (`crates/elab/src`), the sites that matter:

| Site | What | Needed? |
|---|---|---|
| `effects.rs:1764` `make_call` | the operation's argument, for the result type | only if the result type depends on it (never for `IO`) |
| `effects.rs:838-841`, `:897` | row tails, result types, ability arguments | yes (types) |
| `dot.rs:654`, `:772` | dot-notation receiver | only if the result type mentions it |
| `dot.rs:189` | arguments, to compute a type syntactically | only if the type mentions them |
| `numbers.rs:541` `==` | the proposition `a = b`, so both operands | the search needs the shape and the type, not the values |
| `check.rs:1292`, `:1314-1316` `if` | the proposition and its negation | same |
| `check.rs:1373` Bool coercion of a proposition | the proposition | same |
| `auto.rs:342-395` decision search | hidden arguments solved by unifying with the computed proposition | the solutions become the computed values (cause 3) |
| `check.rs:759-793` application | argument, if the codomain mentions it | as the kernel |
| `check.rs:800`, `dot.rs:718` postponed arguments | the checked argument, to unify with a placeholder | yes, but fully computed |
| `unify.rs` | works on computed values; `solve`/`rename` build solutions from them | solutions are as big as the computed values |

### A.3 Measurements

Release build (`nix develop -c cargo build -q --release -p stitchwort-cli`),
`stitchwort check FILE`, wall time, best of 3 except where noted. A scratch
Python script wrote the programs and timed them. `cost` is
`def cost : Nat := List.length (List.range 200000)`.

| Program | check | Notes |
|---|---:|---|
| `def main () : {IO} () := print "hi"` | 0.14 s | baseline |
| `print (Nat.toText cost)` | 0.45 s | `run`: 0.62 s (one more computation, 0.16 s) |
| two such `print`s | 0.73–0.75 s | |
| the original inline program from the speed report | 0.45 s | same as with `cost` |
| `def go (u : ()) : Text := Nat.toText cost` then `print (go ())` | 0.45 s | wrapping in a function doesn't help: `go ()` runs |
| `def big : Nat := cost`, or `def big (u : ()) : Nat := …` | 0.14–0.15 s | defining is free; nothing evaluates a body |
| `f cost`, `f : Nat -> Nat` | 0.14 s | `apply_lazy` skips it |
| `cost \|> Nat.toText` | 0.14 s | |
| `let n := cost` / `n + 1` | 0.15 s | the `(\x => …) v` form |
| `cost.toText` | 0.30 s | 1 computation, the receiver |
| `cost == 5` | 0.45 s | 2 |
| `if cost == 5 …` | 0.46 s | 2 |
| `if cost < 5 …` | 0.76 s | 4 |
| `type V (n : Nat) = { xs : List Nat }`, `def mk (n : Nat) : V n := { xs = [] }`, `def big (u : ()) : V cost := mk cost` | 0.90 s | 5 |
| `def f (n : Nat) : n = n := rfl`, `def big (u : ()) : cost = cost := f cost` | 1.04 s | 6 |
| `def big (u : ()) : cost = cost := rfl` | 0.75 s | 4 |
| `test "length" := cost == 200000` | 0.47 s | 2 at `check`; `stitchwort test` 0.45 s total |
| `def big (u : ()) : Bool := List.range 100000 == List.range 100000` | 0.24 s, `E-RESOURCE` "recursed more deeply than allowed" | at 20,000: accepted, 0.23 s |
| `def big (n : Nat) : Bool := List.range n == List.range n` | 0.15 s | accepted |
| record `Dial` with `inRange : position <= highest`; `def p : Dial 1000001 := { position = 1000000, inRange = Nat.leAddRight 1000000 1 }` | 0.15 s | defining is free |
| the same plus `theorem t : p.position = 1000000 := rfl` | 0.66 s | the proof field is computed |

### A.4 The stage-1 prototype

A scratch change in `crates/elab/src/effects.rs` (`comp_call`, the pure-argument
path just before `return make(cx, x)`), behind an environment variable, then
reverted:

```rust
// after: let x = check(cx, arg, &dom)?;
if std::env::var_os("SW_PROTO").is_some() && !row.partial {
    let mark = cx.mark();
    cx.bind_hidden("%arg".into(), dom.clone());
    let (inner, result_ty) = make(cx, Term::Var(0))?;
    let rt = cx.quote(&result_ty)?;
    if !rt.mentions(0) {
        let comp = comp_type(cx, &row.total(), result_ty.clone())?;
        let comp_t = cx.quote(&comp)?;
        cx.reset(mark);
        let dom_t = cx.quote(&dom)?;
        let lam = Term::Lam("%arg".into(), Icit::Explicit, Rc::new(inner));
        let pi = Term::Pi("%arg".into(), Icit::Explicit, Rc::new(dom_t), Rc::new(comp_t));
        let mut env = cx.env.clone();
        env.push(stitchwort_core::value::unused());
        let result_ty = stitchwort_core::value::eval(cx.g(), &env, &rt)?;
        return Ok((Term::app(Term::Ann(Rc::new(lam), Rc::new(pi)), x), result_ty));
    }
    cx.reset(mark);
}
```

It mirrors the existing effectful-argument path a few lines below, which
already binds `%op` and checks `mentions(0)` (`effects.rs:1729-1745`).
Results: `print (Nat.toText cost)` 0.45 s → 0.14 s; two prints 0.73 s →
0.14 s; `run` prints `200000` twice as before. `stitchwort test` on all 73
files in `examples/accept/` and `aoc/` gave the same exit status with and
without the variable. Not covered: `Partial` rows (skipped by the prototype;
the real change must handle the `lift` wrapper), the generated JS, hashes, the
gate. A real implementation would make the `make_call` path itself take a
bound variable rather than add a second path.

### A.5 Why laziness is sound here, and where it could go wrong

- **Same answers.** In a pure, total language every way of computing a term
  gives the same result (confluence), and every way finishes (totality), so
  computing an argument later, or not at all when it isn't inspected, cannot
  change whether two types are equal. Stitchwort's non-total code (`Partial`)
  runs only through the opaque `Delay` type, which the checker doesn't run.
  Effects are data (`Comp`), so nothing is performed by evaluation.
- **Option (a) is not laziness**: it changes the generated term
  (`(\x => body) arg`), which the unchanged kernel checks. The only argument
  needed is that the result type was computed with `x` free and doesn't
  mention it, which the code tests.
- **Option (b) risks:** a missing `force` before a `match` on a value
  (a thunk would look like none of the expected shapes, so a correct program
  would be rejected with a confusing error, or an internal-error panic); a
  wrong "same term, same environment" shortcut (it must compare the
  environment by identity, not by content, to be cheap and safe); thunks
  escaping into `run` (must not happen: `run` has erasure on, and the
  constructor of thunks should check for that); resource limits (the step
  budget and frame limits must count thunk evaluation, which they do if
  thunks are evaluated by the same machine); and the machine's
  no-re-entry rule (`value.rs:286-292`; forcing a thunk inside the machine
  must be a machine state, like `Control::Force` for metavariables, not a
  nested `run`).
- **Interaction with the run-time evaluator.** The machine is shared. A new
  `Value` variant costs a match arm on the run path even if never created
  there; the speed report's micro-benchmarks (`bench/baseline.toml`) would
  show any slowdown.

### A.6 Sources

- Chris Bailey (ammkrn), *Type Checking in Lean 4*, definitional equality:
  https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html
- Lean API, reducibility attributes:
  https://lean-lang.org/doc/api/Lean/ReducibilityAttrs.html
- Lean 4.9.0 release post (transparency trade-offs, `seal`/`unseal`):
  https://blog.lean-lang.org/blog/2024-7-1-lean-490
- Agda 2.5.4 changelog ("Compile-time weak-head evaluation is now
  call-by-need"): https://hackage.haskell.org/package/Agda-2.5.4/changelog
- Agda abstract machine, `Agda.TypeChecking.Reduce.Fast`:
  https://hackage-content-origin.haskell.org/package/Agda-2.6.1.3/docs/Agda-TypeChecking-Reduce-Fast.html
- Agda 2.6.2 changelog (`--call-by-name`):
  https://hackage.haskell.org/package/Agda-2.6.2/changelog
- Rocq reference manual, conversion rules, `Opaque`, `Strategy`, `lazy`,
  `vm_compute`, `native_compute`:
  https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html
- Idris 2 source, values with closures:
  https://github.com/idris-lang/Idris2/blob/main/src/Core/Value.idr
- Edwin Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021:
  https://arxiv.org/abs/2104.00480
- András Kovács, smalltt (glued evaluation, approximate conversion):
  https://github.com/AndrasKovacs/smalltt
- András Kovács, elaboration-zoo: https://github.com/AndrasKovacs/elaboration-zoo
