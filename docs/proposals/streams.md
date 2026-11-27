# Proposal: infinite streams

**Status:** draft 1, 27 November 2026. Ticket SW-4962 (Fable, paper), from
Matt's question the same day: "how might we best implement infinite streams
in Stitchwort? ... How might we prove things about them? How can we augment
our capabilities in this area?" A design note only: nothing in the compiler
or std changes. Three decisions for Matt in [§7](#7-decisions-for-matt)
(D3770 to D3772). Written against `main` at `9615d5bec`; the probe files in
[streams/](streams/) were checked and run with the main checkout's release
binary.

Earlier decision this reopens: D1911 (30 Oct, [research/inductives.md
§5.4](../research/inductives.md)): "keep codata out of Stitchwort for now
(no streams, no coinductive types or propositions)". This note keeps the
kernel half of that and proposes dropping the library half.

## 0. Summary

**What a user could write and prove, with no kernel change.** A stream is a
function from a position to the value there. With that, all of this checks
today (files [Fn.sw](streams/src/Probe/Fn.sw) and [Corec.sw](streams/src/Probe/Corec.sw) in [streams/](streams/)):

```
def fibs: Stream Nat := Stream.unfold (p => (p.fst, (p.snd, p.fst + p.snd))) (0, 1)
test "fibs" := fibs.take 8 == [0, 1, 1, 2, 3, 5, 8, 13]

theorem Stream.mapIterate ∀ (f: a → a) (x: a): (Stream.iterate f x).map f = Stream.iterate f (f x) :=
  Stream.ext ((Stream.iterate f x).map f) (Stream.iterate f (f x)) (n => (Nat.iterateSuccLast f n x).flipped)
```

- The stream laws are real equalities (`=`), not a separate "behaves the
  same" relation. Two streams with the same value at every position are
  equal (`Stream.ext`, from std's `Quot.funext`), and the coinduction
  principle ("a relation kept by head and tail is inside equality",
  `Stream.bisim`) is an ordinary theorem, 8 lines, proved once.
- The unfolding rules hold by computing: `(Stream.iterate f x).tail =
  Stream.iterate f (f x)`, `(s.map f).tail = s.tail.map f` and
  `(Stream.unfold step start).tail = Stream.unfold step (step start).snd`
  are all `byComputing`.
- Rocq and Agda, which have coinductive types in the kernel, get neither for
  free: there equal-everywhere streams are equal only by an added axiom or
  in cubical mode ([§3](#3-how-other-systems-do-it)). Lean has no
  coinductive data at all, and Mathlib's `Stream'` is this same encoding.

**What it costs.** Speed: reading position n of an unfolded stream costs n
steps, so walking the first n values costs n² (measured: 2,000 values 0.37
s, 4,000 values 1.16 s; a state machine does 20,000 in 0.11 s). And a
definition that refers to itself, Haskell's `ones = 1 : ones`, is still
refused; one writes `Stream.repeat 1` or an `unfold` with its state named.

**Recommendation.** Build streams as a std library on this encoding
(D3770), with a second small type, `Stream.Gen`, a state and a step
function, for running fast, linked to `Stream` by theorems (D3772). Keep
coinductive types out of the kernel (D3771): they would be the largest
trusted addition since quotients, they clash with the kernel's record eta,
and what they would add (self-referential definitions, mixed
inductive-coinductive data, lazy sharing) no program has asked for. About
two hours of lane time for the library and its guide page
([§6](#6-plan)).

## 1. What Stitchwort can do today

All probes are in [streams/](streams/), a seven-file project (`cd
docs/proposals/streams && stitchwort check && stitchwort test`: 7
namespaces, 6 tests pass).

### 1.1 A stream as a function of the position

```
type Stream (a: Type) = { at: Nat → a }

def Stream.head (s: Stream a): a := s.at 0
def Stream.tail (s: Stream a): Stream a := { at = n => s.at (Succ n) }
def Stream.map (s: Stream a) (f: a → b): Stream b := { at = n => f (s.at n) }
def Stream.iterate (f: a → a) (x: a): Stream a := { at = n => Nat.iterate n f x }
def Stream.unfold [s: Type] (step: s → Pair a s) (start: s): Stream a :=
  { at = n => (step (Nat.iterate n (st => (step st).snd) start)).fst }
```

Checked and found to hold:

| Fact | Proof today |
|---|---|
| `s.tail.cons s.head = s` | `Stream.ext`, then a two-case `match` on the position |
| `(iterate f x).tail = iterate f (f x)`; `(s.map f).tail = s.tail.map f`; `(s.cons x).tail = s`; `(unfold step st).head = (step st).fst`; `(unfold step st).tail = unfold step (step st).snd` | `byComputing` (function eta, record eta and `Nat.iterate`'s equation do it) |
| `Stream.ext`: equal at every position gives `s = t` | one line from `Quot.funext` |
| `Stream.bisim`: a relation kept by head and tail is inside `=` | induction on the position, then `ext` |
| `(iterate f x).map f = iterate f (f x)` | one line by position (`Nat.iterateSuccLast`), or 8 lines by `Stream.bisim` ([Bisim.sw](streams/src/Probe/Bisim.sw)) |
| `Stream (Stream Nat)`: a stream of streams | works; the type stays in `Type` |

`stitchwort axioms` lists `Quot.sound` for `ext`, `bisim` and everything
that uses them. It is the one axiom Stitchwort already accepts
(docs/core.md, "Quotients"), and `Effect/Laws.sw` uses `Quot.funext` the
same way.

So the function encoding is, provably and inside Stitchwort, "the" type of
streams: it has the constructor and observations, the unfold with its
computation rules, and coinduction as equality. Nothing about its
*meaning* is missing. What is missing is below.

### 1.2 What isn't convenient

1. **No library.** None of the above is in std. `Nat.iterate` and
   `List.unfold` are; `Stream` isn't.
2. **Self-reference is refused.** `def ones: Stream Nat := ones.cons 1` is
   `E-TERMINATION` ("`ones` has no parameters, so nothing can get
   smaller"), and so is Haskell's `fibs = 0 : 1 : zipWith (+) fibs (tail
   fibs)`. A lazy list by hand, `type LList a = | LNil | LCons (head: a)
   (rest: Unit → LList a)`, is accepted as a type, but it is inductive:
   its only values are finite, and `def from (n: Nat): LList Nat := LCons n
   (u => from (n + 1))` is `E-TERMINATION`. The error's advice (`Partial`,
   or fuel) doesn't mention streams.
3. **Speed.** `at n` of an `iterate` or `unfold` recomputes from the
   start, and nothing is remembered between positions. `((Stream.iterate
   (+ 1) 0).take n).sum` on the fast runtime: 0.17 s for 1,000, 0.37 s for
   2,000, 1.16 s for 4,000 (roughly ×3 per doubling: quadratic). Measured
   once each, wall clock, on a loaded machine.
4. **Definitions whose natural form is by observation need arithmetic.**
   `interleave s t` (alternate the two) is, by observation, "head is `s`'s
   head; tail is `interleave t s.tail`". As a function of the position it
   is `if n % 2 == 0 then s.at (n / 2) else t.at (n / 2)`, and then
   `(s.interleave t).tail = t.interleave s.tail` is *not* `byComputing`
   (probed: `E-REFL`); it needs a parity argument. Defined through
   `unfold` with the pair `(s, t)` as its state, the tail law is by
   computing again (probed, `interleaveTail` in Corec.sw), so the library should define such functions that way.
5. **Possibly-finite and branching infinite data** (a list that may or may
   not end, an infinite tree, a process that answers requests) have no
   type. Each can be encoded ([§4.1](#41-a-the-library-on-functions)), but
   nothing is written.

### 1.3 A stream as a state machine

```
type Machine (a: Type): Type 1 =
  | MkMachine (s: Type) (start: s) (next: s → Pair a s)
```

[Mach.sw](streams/src/Probe/Mach.sw): `map`, `tail`, `take` and `iterate`
work, and `take 20000` runs in 0.11 s (linear). But the type must be
declared in `Type 1` (`E-UNIVERSE` otherwise, since it stores a type), so
`Machine (Machine Nat)` is refused, a `List (Machine Nat)` is too, and
`Quot.funext` (which std has at `Type 0` only) doesn't reach it: two
machines that produce the same values are not provably equal. partial.md
§6.2 (variant 2c) found the same about this encoding in October. With the
state type as a *parameter* instead of a field, `Gen s a = { state: s,
step: s → Pair a s }`, the universe problem goes, at the price of the
state showing in the type ([§4.1](#41-a-the-library-on-functions)).

### 1.4 A stream as an effect

[Yield.sw](streams/src/Probe/Yield.sw): an endless producer written as a
loop, `def natsFrom (n: Nat): {Yield, Partial} () := (yield n; natsFrom (n
+ 1))`, and a handler `firstN` that takes five values and drops the rest.
The test passes (`[10, 11, 12, 13, 14]`). But the result is `{Partial}
List Nat`, and nothing can be proved about it: `theorem …: firstN 2 … =
[0, 1] := byComputing` is `E-PARTIAL`, because a `Partial` computation is
an opaque `Effect.Delay` that only the runtime runs (docs/core.md, "Partial
computations"). Good for programs that produce as they go (it is the shape of
`cat.sw`'s loop over input), no use for proofs.

### 1.5 Predicates about infinite behaviour

"`p` holds at every position" is `∀ (n: Nat) => p (s.at n)`, and "the
invariant holds forever" for an iterated step is already std's
`Nat.iterateKeeps`. For a property that isn't naturally indexed by a
number (two transition systems simulate each other, a process can always
answer), the general tool is a greatest fixed point. Because `Prop` is
impredicative (docs/core.md, "Universes") it is definable today, with no
axiom ([Gfp.sw](streams/src/Probe/Gfp.sw), 14 lines):

```
def Gfp (f: (a → Prop) → a → Prop) (x: a): Prop :=
  ∃ (r: a → Prop) => (∀ (y: a) => r y → f r y) ∧ r x

theorem Gfp.coinduct …: (∀ y, r y → f r y) → r x → Gfp f x     -- the coinduction rule
theorem Gfp.unfold … (mono: f is monotone): Gfp f x → f (Gfp f) x
```

This is the construction behind Lean's `coinductive` predicates and Rocq's
Paco ([§3](#3-how-other-systems-do-it)); neither needed a kernel change
for it.

## 2. What "streams in the kernel" would mean

For comparison with the systems below, the kernel feature is: a new kind
of type declaration whose values may be infinite (a *coinductive* type),
definitions that build such values by saying what each observation of the
result is (*copatterns*: `(repeat x).head = x`, `(repeat x).tail = repeat
x`), and a *productivity* check in place of the termination check: every
observation must be answered in finitely many steps. The check is either
syntactic (*guardedness*: the recursive call sits directly under the
constructor or observation, nothing else around it) or by types (*sized
types*: the type records how deep a value is defined). Equality of two
such values is *bisimilarity*: the same head, and bisimilar tails,
forever.

## 3. How other systems do it

Every claim below was read today from the source named, at the tag or
commit given, unless marked [not checked].

### 3.1 Agda (v2.9.0 manual; agda-stdlib v2.4.1)

- **Coinductive records with copatterns** are the recommended form, under
  `--guardedness`: `record Stream (A : Set) : Set where coinductive; field
  hd : A; tl : Stream A`, and `repeat` defined by `hd (repeat a) = a`, `tl
  (repeat a) = repeat a`. Equality of streams is a second coinductive
  record `_≈_` ("pointwise equality (a bisimulation and an equivalence)"),
  not `≡`; the manual's `merge-split-id` proves `merge (split xs) ≈ xs`
  (`doc/user-manual/language/coinduction.lagda.rst`).
- **A record constructor doesn't guard.** With `constructor cons`, `cycle
  a = cons a (cycle a)` "does not termination-check"; the copattern form
  does (same file).
- **No eta.** "Agda does not permit the `eta-equality` directive in
  `coinductive` `record` declarations, since η for coinductive types is
  unsafe in general and can make the type checker loop" (same file).
- **Musical notation** (`∞`, `♯`, `♭`) is "the old way of coinduction
  support"; "you are advised to use" coinductive records (same file).
- **Sized types.** The manual page is "a stub". The safe-Agda page lists
  `--sized-types` among the unsafe options: it "lacks some checks that
  rule out improper, inconsistent uses of sizes"
  (`language/safe-agda.lagda.rst`). Issue #1201, "Check needed when ∞ < ∞
  is ok for sizes", is still open (GitHub API, today). And "the option
  `--guardedness` is inconsistent with sized types, thus, it cannot be
  used with both `--safe` and `--sized-types`"
  (`tools/command-line-options.rst`).
- **Standard library.** Three stream types side by side:
  `Codata.Guarded.Stream` (`--safe --guardedness`, a coinductive record;
  `unfold`, `iterate = unfold < f , id >`, `map`, `zipWith`, `interleave`
  by copatterns), `Codata.Sized.Stream` (`--sized-types`, not `--safe`; a
  `data` with a `Thunk`), and `Codata.Musical.Stream`. The guarded one's
  properties are mostly about positions: `lookup-iterate : lookup
  (iterate f x) n ≡ ℕ.iterate f x n`, `take-iterate`, `drop-iterate`
  (`src/Codata/Guarded/Stream/Properties.agda`), that is, Agda's own
  library reasons about streams through the function-of-position view.

### 3.2 Idris 2 (v0.8.0)

- `data Stream : Type -> Type where (::) : a -> Inf (Stream a) -> Stream a`
  in the prelude (`libs/prelude/Prelude/Types.idr`); `ones = 1 :: ones` is
  the tutorial's example (`docs/source/tutorial/typesfuns.rst`, "Infinite
  Data Types"). `Inf` marks the recursive argument as possibly infinite;
  `Delay` and `Force` are inserted by the checker, as for `Lazy` (same
  page).
- The totality checker tracks whether a recursive call is under a `Delay`
  under a constructor (`Guardedness = Toplevel | Unguarded | Guarded |
  InDelay`, `src/Core/Termination/CallGraph.idr`). The tutorial warns: "the
  current implementation has had limited effort put into it so far ... Do
  not rely on it for your proofs yet!" (`tutorial/theorems.rst`).
- `Data.Stream` in base has `iterate f x = x :: iterate f (f x)`,
  `unfoldr`, `index`, and theorems stated by position (`zipWithIndexLinear
  : index i (zipWith f xs ys) = f (index i xs) (index i ys)`); base also
  has `Colist` (may end).

### 3.3 Lean 4 (v4.36.0; Mathlib at the same tag)

- **No coinductive data in the kernel.** Mathlib: `def Stream' (α : Type
  u) := ℕ → α`, with `cons`, `tail`, `map`, `iterate` and `corec` defined
  on positions (`Mathlib/Data/Stream/Defs.lean`), `IsBisimulation` and
  `eq_of_bisim : s₁ ~ s₂ → s₁ = s₂` proved through `Stream'.ext`, and
  `map_iterate : iterate f (f a) = map f (iterate f a)` by `funext n;
  induction n` (`Mathlib/Data/Stream/Init.lean`). This is §1.1's design.
- **Possibly-finite:** `Seq α := { f : Stream' (Option α) // f.IsSeq }`,
  where `IsSeq` says a `none` is followed only by `none`s
  (`Mathlib/Data/Seq/Defs.lean`); `WSeq α := Seq (Option α)` adds "still
  computing" steps and is described as the "model ... appropriate for
  Haskell style lazy lists" (`Mathlib/Data/WSeq/Basic.lean`).
- **General coinductive types as a library (M-types):** `PFunctor.M` is
  built from finite approximations, `inductive CofixA : ℕ → Type` (a tree
  cut off at depth n), a structure of one approximation per depth that
  agree, and a proved `M.bisim : … → ∀ x y, R x y → x = y`
  (`Mathlib/Data/PFunctor/Univariate/M.lean`). `QPF.Cofix` quotients it:
  `def Cofix F := Quot Mcongr`, with `Cofix.bisim`
  (`Mathlib/Data/QPF/Univariate/Basic.lean`).
- **Coinductive predicates in core** (2025): the `coinductive` command
  rewrites the declaration to a "flat" inductive functor and hands it to
  the `PartialFixpoint` machinery, which builds the greatest fixed point
  and generates the coinduction principle; nothing is added to the kernel
  (`src/Lean/Elab/Coinductive.lean`, header comment; predicates only).
- **For running:** `class Stream (stream : Type u) (value : outParam (Type
  v)) where next? : stream → Option (value × stream)`
  (`src/Init/Data/Stream.lean`): a state machine whose state type is part
  of the type; its `forIn` is a `partial def`. The newer iterators
  (`src/Init/Data/Iterators/Basic.lean`) are the same shape, `IterStep`
  with `yield`, `skip` and `done`, plus `Finite` and `Productive` classes
  for termination. `@[implemented_by]` swaps in a faster implementation
  that "the kernel and type checking are unaffected" by
  (`src/Lean/Compiler/ImplementedByAttr.lean`): unproved, like a
  Stitchwort native.

### 3.4 Rocq (V9.3.0 reference manual, `doc/sphinx/language/core/coinductive.rst`)

- `CoInductive Stream : Set := Seq : nat -> Stream -> Stream.` and
  `CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).`
- **Guardedness:** "each recursive call in the definition must be
  protected by at least one constructor, and only by constructors"; the
  manual's `filter` fails it. (So does `zipWith (+) fibs (tail fibs)`:
  `zipWith` is not a constructor.) A `cofix` unfolds "only when it occurs
  at the head of an application which is the argument of a case analysis".
- **The subject reduction problem:** "The ability to define coinductive
  types by constructors, hereafter called *positive coinductive types*, is
  known to break subject reduction ... due to dependent pattern-matching
  which implies propositional η-equality, which itself would require full
  η-conversion for subject reduction to hold, but full η-conversion is not
  acceptable as it would make type checking undecidable."
- **The fix:** "negative coinductive types", a primitive record defined by
  its projections, "akin to the *copattern* style ... in e.g. Agda";
  "As of Coq 8.9, it is now advised to use negative coinductive types".
- **What the fix loses:** "propositional η-equality is lost when going to
  the negative presentation. It is nonetheless logically consistent to
  recover it through an axiom", and likewise `Axiom Stream_ext : forall
  (s1 s2: Stream), EqSt s1 s2 -> s1 = s2`. Bisimilar streams are equal in
  Rocq only by an axiom.
- **Proofs.** A coinductive proof is a `cofix` term and must itself pass
  the guard check. Paco's tutorial (snu-sf/paco v4.2.3, `src/tutorial.v`)
  says of it: "non-compositional ... inefficient ... not user-friendly ...
  interacts poorly with builtin automation tactics", and "Coq does not
  generate any lemmas for coinductive definitions". Paco replaces `cofix`
  with a lemma-based `pcofix` over a greatest fixed point with a parameter
  (the facts assumed so far), "that does not involve any syntactic
  guardedness criterion"; its README adds up-to techniques through Pous's
  companion. Paco is a library: it is §1.5's `Gfp` with one more argument.

### 3.5 Haskell (GHC 9.12.2 `ghc-internal`; `haskell/vector` at `313568c7ac1f`)

- A stream is an ordinary list: `iterate f x = x : iterate f (f x)`
  (`GHC/Internal/List.hs`). Laziness makes it work, each cell is computed
  once and then shared, and finite and infinite lists are one type, so
  `length (iterate f x)` type-checks and loops. There is no totality
  check, and so no proofs inside the language.
- **What it gains:** any definition goes, including `fibs`; equational
  reasoning on paper; and fusion, which removes the intermediate lists:
  GHC rewrites `iterate` to `build (\c _n -> iterateFB c f x)` by a
  `RULES` pragma (same file), and `vector` represents a stream as a state
  machine, `data Stream m a = forall s. Stream (s -> m (Step s a)) s` with
  `Step = Yield a s | Skip s | Done`
  (`vector-stream/src/Data/Stream/Monadic.hs`), §1.3's type. Haskell hides
  the state type behind `forall`; Stitchwort can't without `Type 1`.
- The `Stream` package's `Data.Stream` (always-infinite) [not checked].

### 3.6 Others

Hyvernat (LMCS 2025, as summarised in research/inductives.md C13, which
read it in full): checking termination and productivity separately is not
enough once inductive and coinductive types nest; a sound checker needs
its own size-change analysis with priorities. Guarded type theory with a
"later" modality: partial.md §5.11. Unison's `Stream` ability, Koka and
F\*: [not checked]; §1.4 is what the effect route looks like here.

### 3.7 What the comparison says

| | Kernel support | Equal-everywhere streams are `=` | Self-referential definitions | Shared, computed once |
|---|---|---|---|---|
| Agda (`--guardedness`) | coinductive records, guard check | no (a relation; yes in cubical mode [not checked]) | guarded ones | yes [not checked] |
| Idris 2 | `Inf`, guard check ("do not rely on it") | no | guarded ones | yes [not checked] |
| Rocq | `CoInductive`, guard check | by axiom | guarded ones | lazily unfolded |
| Lean 4 + Mathlib | none | **yes, a theorem** | no (`corec`) | no |
| Haskell | laziness, no checks | no proofs | all | yes |
| Stitchwort today (§1.1) | none | **yes, a theorem** | no (`unfold`) | no |

Three lessons. Kernel coinduction has a history of soundness and
type-preservation bugs in every system that has it (Rocq's subject
reduction, Agda's sized types, Idris's caveat). Even with it, the classic
self-referential definitions mostly fail the guard check, and proofs need
a library like Paco. And the system with the most stream mathematics
proved, Mathlib, uses the function encoding.

## 4. The options

### 4.1 (a) The library on functions

**Types.**

- `Stream a = { at: Nat → a }`, as in §1.1, with `head`, `tail`, `cons`,
  `at`, `take`, `drop`, `map`, `zipWith`, `repeat`, `iterate`, `unfold`,
  `interleave`, `scan`, `tails`, and `Nat.iterate`-style lemmas for each.
  A record, not an alias, so `s.map f` and `s.take 5` read with dots and a
  stream isn't confused with any other function from `Nat`.
- `Stream.Gen s a = { state: s, step: s → Pair a s }`, for running: `map`,
  `zipWith` (state `Pair s t`), `take`, `fold` over the first n, `find`
  with fuel, all linear time. The state type is in the type, as in Lean's
  `Stream` class and Rust's iterators, so it stays in `Type` and needs no
  universe above. `Gen.toStream` is `Stream.unfold g.step g.state`, with
  the linking theorems (`(g.map f).toStream = g.toStream.map f`,
  `g.take n = g.toStream.take n`): write the program with `Gen`, state and
  prove the property with `Stream`.
- Later, when wanted: `Colist a` (may end) as `Nat → Option a` with "a
  `None` stays `None`", Mathlib's `Seq`; and general coinductive data
  (infinite trees, interaction trees) as an M-type built from depth-n
  approximations, Mathlib's `PFunctor.M`, with its bisimulation theorem
  proved once. Stitchwort has what the construction uses: indexed families
  (`CofixA` is one), records with proof fields, `Quot.funext`.

**Kernel:** nothing. **Soundness risk:** none new (`Quot.sound`, already
accepted). **Syntax:** none new. **Effects:** a `Stream` is a pure value;
its functions take pure callbacks (a stream whose elements perform `IO` is
§1.4's producer, a different thing). **Native and JS:** ordinary records
and closures, nothing to add. **Performance:** `Stream` quadratic for
`unfold`-built streams walked in order; `Gen` linear.

**Proofs** ([§5](#5-proof-techniques-and-std-support)): by position
(`Stream.ext` and induction on `Nat`), or by `Stream.bisim`. Both give
`=`, so `rewrite` works with stream laws.

**Doesn't give:** self-referential definitions; sharing (a stream read
twice is computed twice); `Gen`'s state type leaks into signatures, so a
list of differently-built generators needs them converted to `Stream`.

### 4.2 (b) Coinductive records in the kernel

`cotype Stream (a: Type) = { head: a, tail: Stream a }`, definitions by
copatterns, and a guard check.

**The kernel would add:** a coinductive declaration form (with its own
positivity rules, and rules for nesting with inductive types and
quotients); corecursive definitions that unfold only under an observation
(a new evaluation rule in both evaluators, the machine and the reference,
and in conversion); a productivity checker, which by Hyvernat's result
can't be the existing size-change checker run a second time; erasure, JS
and native code for lazily built values. docs/core.md would gain a
section the size of "Partial computations" and "Quotients" together, and
all of it is trusted.

**Clashes with what Stitchwort has.**

- *Record eta.* Stitchwort's kernel has eta for declared records
  (`{ x = p.x, y = p.y } = p` by conversion, docs/core.md "Record eta").
  Agda forbids exactly that for coinductive records because it "can make
  the type checker loop", and Rocq's manual gives full eta for
  coinductives as what would make checking undecidable. So coinductive
  records would be a second kind of record without eta, and then
  `s.tail.cons s.head = s` is no longer provable at all without more.
- *Equality.* As in Rocq, bisimilar would not imply equal. Either a second
  axiom is accepted beside `Quot.sound`, or every stream theorem is about
  a relation `≈` that `rewrite` can't use. Option (a) has neither problem.
- *`byComputing`.* `ones.take 3 = [1, 1, 1]` would compute, but `ones =
  ones.tail` would not be by computing (unfolding is only under an
  observation), where today `(repeat 1).tail = repeat 1` is.

**Gives beyond (a):** definitions written as a system of observations
without naming a state (`interleave` as in §1.2 item 4); guarded
self-reference (`ones`), though not `fibs`; mixed inductive-coinductive
types such as Agda's stream processors; and, with a lazy runtime, values
computed once and shared.

**Proofs** would be corecursive terms checked by the same guard checker
(Rocq's `cofix`, with Paco's four complaints), unless a library like Paco
is also built on `Gfp`, which (a) can have anyway.

**Sized types** instead of a guard check would accept more (`fibs`), and
are the one variant with a known open inconsistency in the system that
ships them. Not for a kernel whose point is being small.

### 4.3 (c) Building on `Delay` and abilities

Producers as `{Yield a, Partial}` loops, consumed by handlers (§1.4). It
exists today and runs in constant memory. Giving it proofs would mean
giving `Effect.Delay` equations, which changes the trusted model
("every `Delay` is a one-element set", docs/core.md) that makes `Partial`
cheap to trust; research/inductives.md §5.4 already recommended against.
A total producer could instead be a `Gen` whose step performs abilities
(`step: s → {e} Pair a s`), which is option (a) again with a row variable,
and worth a line in the `Gen` lane's brief.

### 4.4 A trusted speed-up for (a)

`Stream.unfold` could get a native implementation that remembers the
states it has computed, so reading positions in order costs one step each,
as a Haskell list does. To the kernel nothing changes (a native computes
what its pinned definition computes, docs/core.md "Trust"), but the
trusted native set grows from numbers and floats to a data structure with
hidden state, in three runtimes, and a stream held for a long run keeps
every value alive. `Gen` gets the speed with no trusted code. Only worth
doing if a real program is measured to need it.

### 4.5 Comparison

| | (a) library | (b) kernel coinduction | (c) effects |
|---|---|---|---|
| Kernel change | none | large, trusted, Fable review, docs/core.md | none (or `Delay` equations: large) |
| New soundness risk | none | high: the area with the worst record elsewhere | none as is |
| Streams equal when equal everywhere | theorem | no, or a new axiom | nothing provable |
| `map f (iterate f x) = iterate f (f x)` | 1 line | corecursive proof of `≈` | not statable |
| `ones = 1 :: ones` | no; `Stream.repeat 1` | yes | a loop |
| Run time, walk n values | n² (`Stream`), n (`Gen`) | n, shared | n |
| Lane time | about 2 h | days, after a design note and review | 0 |

## 5. Proof techniques and std support

**Is bisimulation equality?** Yes, in option (a), as a theorem:
`Stream.bisim r step s t (h: r s t): s = t`. It follows from `Stream.ext`,
which follows from `Quot.funext` and record eta. No quotient of streams is
needed, because the function encoding has no junk: a stream *is* its
observations. (For `Gen` it is not: two generators with different state
types are different types. Their `toStream`s are compared instead.)

**Three ways to prove a stream equation,** all probed:

1. *By computing,* when both sides are built from `map`, `tail`, `cons`,
   `iterate`, `unfold`, `zipWith` and the law is an unfolding:
   `iterateTail`, `mapTail`, `unfoldTail` in
   [Corec.sw](streams/src/Probe/Corec.sw).
2. *By position:* `Stream.ext`, then a fact about `Nat`. This is
   `map f (iterate f x) = iterate f (f x)`: at position n both sides are
   `f` applied n+1 times, std's `Nat.iterateSuccLast`. It is how Mathlib
   proves `map_iterate` and how agda-stdlib states `lookup-iterate`.
3. *By bisimulation:* name a relation, show it is kept by head and tail.
   The same theorem, in [Bisim.sw](streams/src/Probe/Bisim.sw):

   ```
   def Related (f: a → a) (s t: Stream a): Prop :=
     ∃ (y: a) => s = (Stream.iterate f y).map f ∧ t = Stream.iterate f (f y)

   theorem Related.step …: Related f s t → s.head = t.head ∧ Related f s.tail t.tail :=
     match h with
       | Witness y (Both hs ht) =>
         rewrite hs, ht then
         Both byComputing (Witness (f y) (Both byComputing byComputing))
   ```

   The step is three `byComputing`s because the tail laws compute. This is
   the style to reach for when no closed form by position exists (streams
   defined by `unfold` over an awkward state).

**What std should carry** (stage S1): `ext`, `bisim`, and a variant
`bisimOn` that takes the two streams as functions of a shared seed (`∀ x,
u x` and `v x` have equal heads, and their tails are `u x'` and `v x'` for
some `x'`), which is Mathlib's `bisim'` and removes the `∃` boilerplate
above; `at`/`head`/`tail` lemmas for every constructor function;
`take`/`drop` lemmas (`(s.take n).length = n`, `s.take n ++ (s.drop
n).take m = s.take (n + m)`); `map`'s functor laws, `zipWith` with `map`,
`iterate` with `map` and `drop`, `unfold`'s uniqueness (any `h` with
`(h x).head = (step x).fst` and `(h x).tail = h (step x).snd` is `unfold
step`: the "final coalgebra" fact, which makes every later equation a
corollary).

**A coinduction tactic?** Not yet. With `ext`, `bisimOn` and laws that
compute, the proofs above are a line or a short lemma; and the lesson of
21 Nov (proof tools over-predicted) says to pilot by hand first. If the
dogfood stage shows the relation being written out repeatedly, the tactic
to build is one that takes the goal `u x = v x`, uses the goal itself as
the relation (as `bisimOn` does), and leaves the head and tail goals:
`byBisimulation`. An elaborator tactic over a std theorem, no kernel
change.

**Up-to techniques and Paco-style reasoning** matter when the coinductive
fact is a *predicate* built up incrementally (weak bisimulation of
processes). For those: `Gfp` (§1.5) in std with `coinduct`, `unfold`, and
the parameterised form (`Gfp` of `r => f (r ∨ known)`) with Paco's
accumulation lemma. On demand only; no stream law in §4.1 needs it.

## 6. Plan

End state: `Std.Stream` and `Std.Stream.Gen` in std with their laws and a
guide section; the termination error pointing at them; no kernel change.
Estimates are agent time, from this week's work log (Sonnet std and
elaborator lanes 5 to 27 min; Opus lanes 17 to 23 min; paper reviews 6 to
10 min).

| Stage | What | Model | Est. | Needs |
|---|---|---|---|---|
| S1 | `Std.Stream`: the type, about 15 functions, `ext`, `bisim`, `bisimOn`, `unfold`'s uniqueness, about 40 lemmas, tests; guide section in `docs/guide/` and a line in `docs/syntax.md` | Sonnet; the orchestrator checks statements (D2436) | 35 min | D3770 |
| S2 | `Stream.Gen`: the type, `map`, `zipWith`, `take`, `foldFirst`, `find` with fuel, `toStream` and the linking theorems; the n² against n measurement recorded in the performance log | Sonnet | 30 min | D3772, S1 |
| S3 | `E-TERMINATION`'s note, when the result type is a `Stream`, says "build it with `Stream.unfold` or `Stream.iterate`"; a feature-tour page (`web/guide/`) | DeepSeek, then Sonnet for the page | 20 min | S1 |
| S4 | Dogfood: one AoC day that iterates a step until something repeats, or the roguelike's random numbers, rewritten on `Stream`/`Gen`, with friction notes; decides whether `byBisimulation`, `Colist` or the memoising native (§4.4) are worth a ticket | Opus (AoC rule, D2427) | 30 min | S1, S2 |
| on demand | `Colist` (20 min, Sonnet); `Gfp` with the Paco lemmas (30 min, Opus); M-types (a note first) | | | a program that wants them |
| not planned | Kernel coinductive types; a memoising native | | | D3771; a measured need |

## 7. Decisions for Matt

**D3770: add streams to std as a library, reversing the library half of
D1911? [rec: yes]**

- *The problem.* Stitchwort has no type for an endless sequence. D1911
  said "no streams" in October because they were assumed to need kernel
  coinduction.
- *The change.* `Std.Stream` as a function from position to value (§4.1),
  with its laws proved; stage S1, about 35 minutes of a Sonnet lane. No
  kernel change, no new axiom.
- *What it should do.* Users write `Stream.iterate`, `Stream.unfold`,
  `s.map f`, `s.take 5`, and prove laws such as `map f (iterate f x) =
  iterate f (f x)` as real equalities in a line (checked today, §1.1).
  Rocq and Agda need an axiom or cubical mode for that equality.

**D3771: keep coinductive types out of the kernel? [rec: yes, keep them
out]**

- *The problem.* The textbook way to get streams is a kernel feature:
  coinductive types, copatterns, a productivity checker.
- *The change.* None: D1911's kernel half stands. Revisit only if a
  program needs mixed inductive-coinductive data that an M-type library
  can't give.
- *What it should do.* Spare the kernel its largest and riskiest trusted
  addition. Elsewhere this feature broke type preservation (Rocq), is
  unsound in one variant (Agda's sized types) and is documented as not to
  be relied on (Idris). Here it would also clash with record eta and
  leave stream equality weaker than the library's (§4.2). What is given
  up: `ones = 1 :: ones` written directly (use `Stream.repeat 1`), and
  lazy sharing.

**D3772: how should streams run fast? (a) `Stream.Gen`, a state and a
step function, proved to agree with `Stream`; (b) a trusted memoising
native behind `Stream`; (c) both. [rec: (a)]**

- *The problem.* Walking the first n values of an unfolded `Stream` takes
  n² steps (measured: 4,000 values 1.16 s; a state machine, 20,000 in
  0.11 s).
- *The change.* (a) adds a second small type for running, whose state
  type shows in signatures (as Lean's `Stream` class and Rust's iterators
  do), with theorems carrying facts across; stage S2, about 30 minutes.
  (b) keeps one type but adds trusted runtime code with hidden state in
  three runtimes.
- *What it should do.* (a): linear-time stream programs with no trusted
  code, at the price of two types to learn. If S4's dogfood finds the two
  types awkward, (b) is still open, behind a measurement.

## 8. What was verified, and what wasn't

- **Run today** (main checkout's release binary, copied): every Stitchwort
  claim in §1 and §5; the files are in [streams/](streams/). Timings are
  single runs on a busy machine: good for "quadratic against linear", not
  for the constants.
- **Read today at a pinned tag:** every quotation in §3.1 to §3.5 (Agda
  v2.9.0, agda-stdlib v2.4.1, Idris2 v0.8.0, lean4 and mathlib4 v4.36.0,
  rocq V9.3.0, paco v4.2.3, GHC `ghc-9.12.2-release`, vector
  `313568c7ac1f`), and Agda issue #1201's state.
- **Not checked:** how Agda and Idris run coinductive values (the
  "shared" column); cubical Agda's stream equality; Haskell's `Stream`
  package; Unison, Koka, F\*; the release in which Lean's `coinductive`
  first shipped (research/inductives.md says 4.25; the source file is
  there at 4.36); Hyvernat's paper, taken from research/inductives.md's
  reading. The M-type plan for Stitchwort (§4.1) is argued from Mathlib's
  construction, not prototyped. That kernel coinduction would clash with
  record eta is argued from Agda's and Rocq's manuals, not tested against
  Stitchwort's conversion.
