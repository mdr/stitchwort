# Proposal: streams you can recurse on with head and tail

**Status:** draft 1, 28 November 2026. Ticket SW-4993 (Fable, paper). The
third look at streams, after [streams.md](streams.md) (SW-4962) and
[streams-one-type.md](streams-one-type.md) (SW-4988). A design note only:
nothing in the compiler or std changes. One decision for Matt in
[§7](#7-decisions-for-matt) (D3775), and a second to keep on the shelf
(D3776). The probes are new files in [streams/](streams/), checked and run
with a copy of the main checkout's release binary; the worktree is at `8ac5c7a30`.

## 0. Summary

**The problem, in Matt's words:** "that's probably my first intuition I'd
have about a stream, is it's something I could recurse on with head and
tail". The three-field `Stream` of SW-4988 is fast for every walk except
that one: a loop that calls `s.tail` each time round is quadratic (20,000
values: 33 s, measured), and the only help offered was a warning.

**What this note found.**

1. **The loop can be made linear with no trusted code and no kernel
   change.** SW-4988 argued that a one-step `tail` needs an infinite value.
   That is true of a `tail` that is one step *every* time; it is not true of
   one that is one step *on average*. A stream can carry a finite stretch of
   cells in front of it and, when they run out, walk again from the start
   for twice the distance. Probed with its proofs
   ([Seq.sw](streams/src/Probe/Seq.sw)): the head/tail loop reads 20,000
   values in 0.14 s and 2,000,000 in 2.3 s in constant memory; streams equal
   at every position are still `=`; the only axiom is `Quot.sound`, as
   before.
2. **A lazy `Thunk` on its own does not fix the loop**, in any encoding I
   could find ([§3.2](#32-b-a-trusted-lazy-runtime)): sharing saves
   computing the *same* suspended value twice, and the k-th tail of a stream
   is a different closure each time.
3. **The trusted-runtime option has a smaller form than a lazy runtime:**
   the runtimes keep a stream as `unfold`'s step function and current state
   (no cache, no mutable cell), and `head` and `tail` become the two
   equations std already proves by computing. The plain one-field `Stream`
   of the first note comes back, with every law by computing. It is the
   fastest option (2,000,000 values 0.8 s, simulated) and the simplest type,
   and it costs runtime code in three or four places that no proof checks.
4. **Kernel coinduction does make the loop linear without sharing**, which
   the first note didn't say. Its case against otherwise stands, with one
   point weaker than it looked (record eta) ([§3.4](#34-d-kernel-coinduction)).

**Recommendation.** Make std's `Stream` the type of finding 1 (option E
below), behind a pilot stage that builds the first few functions and
measures the proof load before the rest. Keep finding 3 (option C) as the
upgrade if E's constant factor or its proof load turns out to matter: the
user-facing API is the same, so the choice can be changed later without
breaking programs. D3771 (no coinductive types in the kernel) stands.

## 1. The problem

```
def firstWhere (s: Stream a) (p: a → Bool) (fuel: Nat): Option a := match fuel with
  | Zero => None
  | Succ k => if p s.head then Some s.head else firstWhere s.tail p k
```

On the three-field type, `s.tail` wraps `s` in one more closure, and
reading the head of a stream k tails deep goes through all k. The fast
form in SW-4988 loops over `s.walk fuel` instead. That is a second thing to
learn, and the slow form is the one people write first. The goal here:
the loop above, as written, is linear.

## 2. The options in one table

Timings are for the head/tail loop summing the first n values of
`iterate (+ 1) 0`, fast runtime, single runs ([§4](#4-timings)).

| | Design | Head/tail loop | Other walks | Trusted code, and where | Kernel change | Equality | Laws by computing | Memory | Lane time (agent) |
|---|---|---|---|---|---|---|---|---|---|
| A | Three-field `Stream` with a warning (SW-4988, the baseline) | n²: 20,000 in 33 s | n, over `s.walk` | none | none | `=`, by `Quot.sound` | builders' tail laws: yes, no axiom. Unknown stream: one-line `ext` | constant | 100 min (its plan, without the dogfood) |
| B1 | A lazy `Thunk` with sharing, std builds the rest | n² still (argued, §3.2) | n | a memo cell, 4 places | none | `=` | as A | a held stream keeps its cells | 2 h, for nothing here |
| B2 | A lazy runtime stream: cells computed once and kept, each stream primitive native | n, one step each | n; a second walk is free | a mutable cell and about 6 natives, 4 places | none | `=` | all, as the first note | a held stream keeps every cell read | 3 to 4 h, after a note and review |
| C | The runtimes keep a stream as step and state | n, one step each: 2,000,000 in 0.8 s (simulated) | n by head/tail; `s.at i` in a loop is n² | about 5 pure natives, 3 or 4 places; each is a proved equation | none | `=` | all, as the first note | constant | 2 to 3 h, after a note and review |
| D1 | Coinductive types in the kernel | n, without sharing | n | the kernel: declarations, a guard check, new evaluation rules | large | bisimilarity; `=` only by a new axiom | unfolding under an observation only | constant (cells kept if shared) | days |
| D2 | One primitive `Stream` with a corecursor in the kernel | n | n | the kernel: 4 constants, 2 rules, 1 axiom | small, the size of `Quot` | `=` only by a new axiom | head and tail of an `unfold`: yes. `s.tail.cons s.head = s`: no | constant | 4 h with review |
| **E** | **A stream that keeps its reader's place, behind a quotient (new)** | **n on average: 20,000 in 0.14 s, 2,000,000 in 2.3 s** | **n, over the walk as in A** | **none** | **none** | **`=`, by `Quot.sound`** | **closed streams compute. Whole-stream laws: one-line `ext`. `tail` of an unknown stream: by one lemma, not by computing** | **constant (measured)** | **135 min** |

"4 places" are the fast runtime (`crates/rt`), JS (`crates/js`), native
code (`crates/native`, through the fast runtime's natives) and the
checker's own evaluator when it runs tests (`crates/core`).

## 3. The options

### 3.1 A: the three-field stream with a warning

As SW-4988 left it. Re-measured: the tail loop takes 0.18 s, 1.29 s and
33.2 s for 1,000, 4,000 and 20,000 values (5.2 s for 20,000 with `--js`).
A warning on the natural form tells the user their first idea was wrong
after they have had it.

### 3.2 B: a trusted lazy runtime

**What Stitchwort's trust rules allow.** A native is bound to one
declaration by content hash and must compute what it computes
(docs/core.md, "Numbers", Trust). The float natives are the model for a
run-time-only one: they "fire only while a program or test runs
(`Erasure::program_running`), never while checking: conversion, and so
`byComputing`, always computes them through their definitions, so no
float native is in the kernel's trusted base" (docs/core.md, "Float"). The
fast runtime as a whole is "untrusted ... Its output can be wrong, but a
proof never depends on it" (docs/core.md, "Evaluation and conversion").
So any option here is trusted only for *programs running as proved*, never
for proofs, and the kernel keeps evaluating by the definitions. There are
precedents for a value kept in another form than its declaration says:
`Nat` as one big number, text literals as a range of an array, and
`Array` in the runtimes (`rt/natives.rs`, pinned by `ARRAY_DATA_HASH`;
docs/proposals/backend-trust.md §3.1).

**B1: is one primitive enough?** Lean's is the model: `Thunk` is to the
kernel an ordinary structure with one field, `fn : Unit → α`, and the
caching is only in compiled code ([§5](#5-prior-art)). The Stitchwort
equivalent would be `type Thunk a = { force: Unit → a }` with natives for
its constructor and `get`. What the runtime must guarantee is small and
needs no pin on any other definition: calling a pure function twice gives
the same value, so returning the kept one is right.

But it doesn't fix the loop. In the logic `Thunk (Cells a)` is `Unit →
Cells a`, so every type built from it has the values it had before:
finite ones. With thunked cells, `s.walk n` and `s.walk (n + 1)` are
still two different walks sharing nothing, and `s.tail` is still a new
closure around `s`: the loop asks each of k different closures for its
head once, and no value is ever forced twice, so there is nothing for the
cache to save. A memoised function from positions (`at` backed by a
table) fails the same way one level up: k tails are k closures each
adding one to the position. I found no encoding where `Thunk` alone
gives a one-step tail, and Lean has none either: no `Thunk`-based stream
with theorems exists in Lean, Batteries or Mathlib at v4.36.0. This is
an argument from the encodings tried, not a proof. A `Thunk` would still
do one useful thing for option E ([§3.5](#35-e-a-stream-that-keeps-its-readers-place)).

**B2: a lazy stream in the runtimes.** The logic keeps `Stream = { at: Nat
→ a }`; at run time a stream is a chain of cells, each computed once and
kept. Since any code may build `{ at = f }` or read `.at`, the runtimes
must take over the record itself (its constructor and projection) and
`unfold`, `head`, `tail` and `cons`: about six natives, each in every
runtime, plus the cell with its hidden update. A wrong cache gives wrong
output that no proof catches. Memory is Haskell's: a stream that is still
referenced keeps every cell read so far, so a named `fibs` walked to a
million holds a million values; Scala's docs warn of exactly this, and it
can't be bounded without giving up the sharing (Idris's weak cells let
the collector drop them, which makes speed unpredictable instead). The
one thing B2 has that nothing else here does is that a second walk of the
same stream is free.

### 3.3 C: the runtimes keep a stream as step and state

The universe problem that sinks the state machine as a *type* (`Machine`
stores its state type, so it lives in `Type 1`) doesn't exist at run
time: the runtimes are untyped. So keep the first note's one-field
`Stream`, and let the runtimes represent a stream as either `unfold`'s
step and state or a function of the position with an offset:

| Native | Does | The equation it relies on |
|---|---|---|
| `Stream.unfold step st` | keeps `step` and `st` | (the representation) |
| `head` | `(step st).fst` | `unfoldHead`, `byComputing` in Corec.sw |
| `tail` | keeps `step` and `(step st).snd`; for a position function, adds one to the offset | `unfoldTail`, `byComputing` |
| `{ at = f }` | keeps `f` and offset 0 | `fromFnIsUnfold`, proved in [ByUnfold.sw](streams/src/Probe/ByUnfold.sw) |
| `.at n` | n tails, then head; for a position function, one call | `tailsHead`, proved there |

None has hidden state; each is a pure function of its arguments, and each
is an equation std proves about the pinned definitions. That is Lean's
`@[csimp]` idea with a change of representation added, and SW-4992
(proved compiler swaps) is the general mechanism it would sit on.

For the loop to be one step per tail, std's functions must be written as
unfolds whose state is the stream they read: `map` as `unfold (t => (f
t.head, t.tail)) s`. Probed on the plain stream: `(s.mapU f).tail =
s.tail.mapU f` and the head law are still `byComputing` with no axiom,
and `(s.mapU f).at n = f (s.at n)` is a two-line induction.

- **Speed.** Simulated with the `Machine` type, which does at source
  level what the runtime would: 20,000 values 0.12 s, 2,000,000 in 0.82 s,
  constant memory.
- **The trap moves** to reading by position in a loop (`s.at 0`, `s.at
  1`, …), which is n² on an unfolded stream. That is the trap every list
  has (`xs !! i`), and not the first thing anyone writes for a stream.
- **Cost.** Natives in `crates/rt` and `crates/js` (and what
  `crates/native` takes from them), with pins and differential tests; and
  in the checker's evaluator too if `stitchwort test` is to run long loops
  fast, since tests run there. I did not check how `Array`'s natives
  behave under `test`.
- **Not prototyped**: it needs a build. How the runtimes' erased IR
  recognises one record type's constructor and projection is the part to
  design first.

### 3.4 D: kernel coinduction

**Does it make the loop linear without sharing? Yes.** A stream built by
a guarded definition is a closure over its state; `tail` unfolds the
definition once and gives the closure over the next state. One step, and
no cache involved. Rocq's kernel does exactly this: a cofix unfolds when
it meets a match or projection, and the result is not memoised (its
bytecode machine and OCaml extraction do cache). The first note listed
"lazy sharing" as what coinduction would add at run time; it should have
said that head/tail recursion is linear by construction, which is the
property Matt asked about. That is a real point in its favour.

**The case against, re-read.**

- *Record eta: weaker than it looked.* The note called it a clash. It is
  a constraint: a coinductive type would simply be declared without eta,
  as one-constructor data types already are in Stitchwort (`MkWrap w.n =
  w` is `E-REFL` today, docs/syntax.md). What is lost is `s.tail.cons
  s.head = s` by computing, which then falls under the next point.
- *Equality only by axiom: stands.* Rocq's manual and Agda (outside
  cubical mode) were read for the first note; nothing found since changes
  it. Bisimilar streams would be `=` only with a second axiom beside
  `Quot.sound`.
- *Soundness record: stands*, for the general feature (D1).
- *Size: smaller in one form.* D2 is a single primitive `Stream` with a
  corecursor, `head`, `tail` and two computation rules: no declaration
  form, no guard checker, no positivity question, about the size of
  `Quot` in the kernel. It still needs the axiom, and what it buys over C
  is that the checker's evaluator is fast too. Its runtime behaviour is
  C's.

So D3771 stands, but its reason is now "E and C get the loop without it",
not "nothing needs what it gives".

### 3.5 E: a stream that keeps its reader's place

**Testing SW-4988's argument.** "A `tail` that costs one step however
many came before must hand back a stream holding the current state", and
a hidden state in `Type` means an infinite value. Each half holds. But
the loop only needs n tails to cost about n steps *in total*. A finite
stretch of cells is a finite value, and it is enough for a while.

**The type** ([Seq.sw](streams/src/Probe/Seq.sw), 150 lines, called `Seq`
there to sit beside the three-field `Stream` it is built on):

```
type Front (a: Type) (at: Nat → a) = {
  origin: Stream a,         -- the stream the reader started from
  offset: Nat,              -- how many tails since
  cells: Cells a,           -- the values from here on, for some count
  shifted: ∀ (n: Nat) => at n = origin.at (offset + n),
  ok: ∃ (m: Nat) => cells = Cells.fromAt (j => origin.at (offset + j)) 0 m
}

type Seq (a: Type) = { base: Stream a, front: Quot (Front a base.at) Front.same }
```

- `base` is what the stream *is* (SW-4988's three fields, so every other
  walk is as fast as there).
- `front` is where a reader has got to. `tail` moves one cell along; when
  the cells run out it walks the origin again for twice the distance and
  skips to its place, so n tails cost about 4n steps in all. `head` reads
  the first cell.
- `Front.same` relates every two fronts, so the quotient forgets which
  one a stream has: the front adds speed and no information. That is what
  SW-4988's `agrees` field did for the walk, done here with a quotient
  because a front depends on the reader's history and can't be pinned to
  one value by an equation.
- The tail is rebuilt from the origin (`origin.drop (offset + 1)`, one
  closure), so a stream holds nothing of the streams before it.

**What holds** (checked; `stitchwort axioms` gave the last column):

| Fact | Proof in the probe | Axioms |
|---|---|---|
| `Seq.ext`: equal at every position gives `q = r` | `Stream.ext` on the bases, then any two fronts are equal (`Quot.ind`, `Quot.sound`) | `Quot.sound` |
| `Seq.headIs`: `q.head = q.base.at 0` | `Quot.ind`, then a two-case match | none |
| `Seq.tailAt`: `q.tail.base.at n = q.base.at (Succ n)` | `Quot.ind`, then the `shifted` field | `Quot.sound` |
| `(Seq.iterate f x).tail = Seq.iterate f (f x)` | `Seq.ext _ _ (n => byComputing)` | `Quot.sound` |
| `(q.map f).tail = q.tail.map f` | `Seq.ext`, then `Seq.tailAt` | `Quot.sound` |
| `(Seq.iterate f x).tail.head = f x` | `byComputing` | none |
| `Seq (Seq Nat)` | works; the type is in `Type` | |
| The loop under `stitchwort test` (the checker's evaluator), 20,000 values | passes; the file's 9 tests take 2.1 s uncached | |

**What gives, against A.**

1. `(iterate f x).tail = iterate f (f x)` as a whole-stream equation is
   no longer bare `byComputing` (`E-REFL`, checked): the two sides have
   different fronts. It is the one-line `ext` above, and uses
   `Quot.sound` where A used nothing. Facts about closed streams still
   compute.
2. `tail` of an *unknown* stream doesn't compute at all (`E-REFL`,
   checked): `Quot.lift` is stuck on an unknown front. Laws go through
   `Seq.tailAt` and `Seq.headIs` by `rewrite`. The first note's
   bisimulation proof, three `byComputing`s, would be three rewrites.
3. The loop is about 3.5 times slower than the cells loop at large n
   (2.3 s against 0.66 s for 2,000,000), from the repeated walks.
4. One step *on average*, for a reader that moves forward. A program that
   takes the tail of the *same* stream many times, at a point where its
   cells have just run out, pays the re-walk each time (k steps at depth
   k). The textbook remedy is laziness (Okasaki's, from memory, not looked
   up): with a memo `Thunk` (B1) the re-walk
   would be shared. Not needed for the loop; a reason B1 might come back.
   Argued, not measured.
5. `tail` does its work when called, not when read (Stitchwort is
   strict), so an unused `s.tail` costs a step.
6. Std's functions each choose what happens to the front. The probe's
   `map` starts the result afresh (`Seq.of (q.base.map f)`), which is
   right but makes the first read after `q.tail.map f` cost the offset.
   Carrying the front through (`map` over the cells) is possible and
   means a "respects the quotient" proof per function.

**How it went.** Seq.sw's proofs checked on the first run apart from one
naming problem (findings, in the lane report); about 15 minutes for the
type, `head`, `tail`, `ext`, `iterate`, `map` and their laws. A first
version without the origin, wrapping the stream once per tail, was as
fast but held 1.07 GB at 2,000,000 values; the origin and offset brought
that to 79 MB, the process's floor.

## 4. Timings

`sum` of the first n values of `iterate (+ 1) 0` by a head/tail loop
(`acc + s.head`, recurse on `s.tail`), from
[RunTail.sw](streams/src/Probe/RunTail.sw). Wall clock, including about
0.11 s of start-up and cached checking. Single runs; load average 4 to 10.
Good for the shape, not the constants.

| n | A: three-field | E: `Seq`, with proofs | C simulated: `Machine` | Not a tail loop: cells loop over `s.walk n` |
|---|---|---|---|---|
| 1,000 | 0.18 s | 0.12 s | 0.11 s | 0.11 s |
| 4,000 | 1.29 s | 0.12 s | 0.12 s | 0.11 s |
| 20,000 | 33.24 s | 0.14 s | 0.12 s | 0.11 s |
| 200,000 | not run | 0.35 s | 0.18 s | not run |
| 2,000,000 | not run | 2.32 s, 79 MB | 0.82 s, 79 MB | 0.66 s, 79 MB |
| 20,000, `--js` | 5.19 s | 0.35 s | 0.19 s | 0.20 s |
| 200,000, `--js` | not run | 0.22 s | 0.20 s | 0.21 s |

B and D can't be run without building them. The cells loop is what B2's
loop would do per value at best (it adds a cell update); `Machine` is
what C and D2 would do. E without proofs
([Cursor.sw](streams/src/Probe/Cursor.sw)) ran the same as E with them:
the quotient and proof fields are erased.

## 5. Prior art

Read today at the tag given, by a research subagent that quoted file and
line for each; what it could not check is in [§8](#8-what-was-verified-and-what-wasnt).

- **Lean 4 `v4.36.0`.** `Thunk` is a structure, `fn : Unit → α`
  (`src/Init/Core.lean` L116-126), with `Thunk.mk`, `pure` and `get`
  tagged `extern` (`lean_mk_thunk`, `lean_thunk_pure`,
  `lean_thunk_get_own`); "The Lean runtime has special support for the
  `Thunk` type in order to implement the caching behavior" (L113). The
  kernel knows nothing of it: no "thunk" in any top-level file of
  `src/kernel/`. The cache is in `src/include/lean/lean.h` L1587-1590 and
  `src/runtime/object.cpp` L525-538, which takes the closure, runs it and
  stores `m_value`. `Thunk.get`'s logical body is `x.fn ()`, and
  `Thunk.ext` is a theorem (`src/Init/Ext.lean` L90). So B1 is exactly
  Lean's design: in the compiler and runtime, not the kernel. No
  `Thunk`-based stream with theorems exists: Mathlib deprecated
  `LazyList` in July 2024, Batteries' `MLList` is `unsafe` behind an
  `opaque` with no theorems, and Mathlib's proved `Stream'` is `ℕ → α`.
  `@[csimp]` "must prove a statement `@f = @g` ... any occurrence of `f`
  is replaced with `g` in compiled code, but not in the type theory"
  (`src/Lean/Compiler/CSimpAttr.lean` L63-66); `implemented_by` "is not
  checked", which "makes it possible to prove `False` with
  `native_decide`". C is the `csimp` kind.
- **Idris 2 `v0.8.0`.** `Lazy` and `Inf` are a plain lambda, run again at
  every force, on Chez and Racket by default
  (`src/Compiler/Scheme/Common.idr` L324-333), on RefC and on
  JavaScript (`src/Compiler/ES/ToAst.idr` L172-176); Gambit never caches.
  The opt-in `weakMemo` caches through a weak pair the collector may
  clear (`support/chez/support.ss` L24-32). So Idris's streams are, by
  default, C's kind (a closure over the state, one step per tail, nothing
  kept; forcing the same tail twice computes it twice), not Haskell's.
- **Agda `v2.8.0`.** Coinductive constructor fields are lazy Haskell
  fields (`src/full/Agda/Compiler/MAlonzo/Compiler.hs` L1153-1156), and
  copattern clauses compile to a record constructor
  (`src/full/Agda/Compiler/ToTreeless.hs` L272-273, L504). So each field
  is a GHC thunk, shared per value. That last step is inferred from the
  code; no Agda document says it.
- **Rocq `V9.0.0`.** The kernel's lazy machine unfolds a cofix only under
  a match or projection and does not keep the result
  (`kernel/cClosure.ml` L1883-1893; "not kept" is the subagent's reading).
  `vm_compute` does: "the application of the cofix is evaluated only once
  (it simulates a lazy evaluation)" (`kernel/vmbytegen.ml` L82-86).
  Extraction to OCaml emits `lazy` and `Lazy.force`
  (`plugins/extraction/ocaml.ml` L269, L301).
- **OCaml `5.4.0`.** A forced `lazy` releases its closure and is
  overwritten with the result (`stdlib/camlinternalLazy.ml` L47-51);
  "[Lazy.force] is not concurrency-safe". `Seq` is not memoised unless
  asked: "[memoize xs] is persistent: even if it is queried several
  times, [xs] is queried at most once" (`stdlib/seq.mli` L554-563).
- **Scala `v2.13.18`.** `LazyList`: "Elements are memoized"; "Memoization
  can be a source of memory leaks ... if a reference to the head is
  retained unintentionally, then all elements will be retained"
  (`LazyList.scala` L29, L121-123).
- **Haskell (GHC `ghc-9.12.2-release`).** "Dynamic thunks are overwritten
  with normal indirections `IND` when evaluated" (GHC commentary,
  `rts/storage/heap-objects`; code in `rts/Updates.h`).
- **Koka `v3.2.9`.** `delayed` hides its mutable cell from the effect
  type with an unsafe cast (`lib/std/core/delayed.kk`).
- **F\* `v2026.11.22`.** No stream, lazy or memo module in `ulib/`.

Three patterns: sharing in the runtime under a pure logical type (Lean,
Koka, GHC); no sharing, a closure per step (Idris by default, Rocq's
kernel, OCaml's `Seq`); and nobody found who proves things about a
runtime-shared stream. E's doubling re-walk is the usual amortised-array
argument; I did not look for it in the literature.

## 6. What changes in the earlier notes

- **D3770** (streams in std as a library): stands. The type changes shape
  once more: `Stream` is E's type, with SW-4988's three-field record as
  its internal `base`. Users see `head`, `tail`, `at`, `take`, `map`,
  `ext`, `bisim` as before.
- **D3771** (no coinductive types in the kernel): stands. Two corrections
  to its argument: coinduction would make head/tail loops linear (not
  only add sharing), and record eta is a constraint on such types, not a
  clash. Neither changes the recommendation while E or C does the job.
- **D3772 (revised, SW-4988)**: replaced by D3775. The three-field type
  survives inside E. `W-STREAM-TAIL-LOOP` is dropped: there is no slow
  loop left to warn about.
- **streams.md §4.4** (the memoising native): still not planned. B1 is
  worth a ticket only if S4 finds E's amortisation biting (§3.5 item 4).
- **Plan.** Estimates in agent time, from the probes.

| Stage | What changes | Model | Est. |
|---|---|---|---|
| S0 (new, the pilot) | `Std.Stream` as E's type with `Cells`, the internal three-field base, `head`, `tail`, `cons`, `iterate`, `unfold`, `map`, `take`, `ext`, `headIs`, `tailAt`, `bisim`; the timings of §4 again; a count of proof lines per function, against this note's 150 lines for six. Stops and reports if a function needs more than about 30 lines of proof | Opus (a hard invariant: the quotient) | 45 min |
| S1 | The rest: `zipWith`, `drop`, `interleave`, `repeat`, `scan`, `fromFn`, `find`, `fold`, the laws for each through `tailAt` and `headIs`, `bisimOn`, `unfold`'s uniqueness; guide section teaching head/tail recursion first and `walk` for long folds | Sonnet; the orchestrator checks statements (D2436) | 50 min |
| S2 | `findRepeat`, `foldUntil`; the timings in the performance log | Sonnet | 20 min |
| S3 | `E-TERMINATION`'s note pointing at `Stream.unfold`; feature-tour page. No warning | DeepSeek, Sonnet for the page | 20 min |
| S4 | Dogfood, unchanged; its notes also judge the proof style (rewriting with `tailAt`) and whether the re-walk shows | Opus | 30 min |
| on the shelf | C, as a design note first, on SW-4992's mechanism | Fable note, Opus build | 2 to 3 h |

## 7. Decisions for Matt

**D3775: make std's `Stream` the type that keeps its reader's place
(option E), so head/tail recursion is linear as written, with no trusted
code? [rec: yes, starting with the pilot stage S0]**

- *The problem.* On the three-field stream a loop over `s.tail`, the
  first thing a newcomer writes, is quadratic (20,000 values: 33 s,
  measured), and the remedy was a warning.
- *The change.* A stream also carries, behind a quotient, a stretch of
  cells in front of its reader, and re-walks from the start for twice
  the distance when they run out. No kernel change, no native, no new
  axiom. Replaces the revised D3772.
- *What it should do.* The same loop reads 20,000 values in 0.14 s and
  2,000,000 in 2.3 s in constant memory (measured, with the proofs).
  Streams equal everywhere are still `=`. What it costs: the loop is
  about 3.5 times slower than the hand-written cells loop at large sizes
  (measured); `tail` laws are proved by rewriting with one std lemma
  instead of by computing; and std's stream functions take more proof
  (estimated 35 minutes more lane time; the pilot measures it).

**D3776 (for later, not needed to start): if the pilot or the dogfood
shows E too slow or too heavy to prove with, switch to option C, the
runtimes keeping a stream as step and state? [rec: decide then; C is the
fallback, not kernel coinduction]**

- *The problem.* E's speed is an average and its type is intricate
  inside.
- *The change.* The plain one-field `Stream` of the first note, with
  about five natives in each runtime, each a proved equation.
- *What it should do.* One step per tail always (2,000,000 values 0.8 s,
  simulated), every law by computing. It adds runtime code no proof
  checks, of the kind `Array` already is; a wrong one gives wrong program
  output, never a wrong theorem.

## 8. What was verified, and what wasn't

- **Run today** (a copy of the main checkout's release binary, worktree at `8ac5c7a30`;
  `STITCHWORT_JOBS=2`): everything in §3.5's table, §4, and the laws
  quoted in §3.3. `stitchwort check` passes all 14 namespaces of the
  probe project and `stitchwort test` passes its 17 tests. New files:
  [Seq.sw](streams/src/Probe/Seq.sw) (E with proofs),
  [Cursor.sw](streams/src/Probe/Cursor.sw) (E without, two variants),
  [ByUnfold.sw](streams/src/Probe/ByUnfold.sw) (C's equations),
  [RunTail.sw](streams/src/Probe/RunTail.sw) and
  [N.sw](streams/src/Probe/N.sw) (the timing loops). The three `E-REFL`s
  in §3.5 were checked in a scratch file, not kept. Timings are single
  runs on a loaded machine; the `--js` memory figures were not taken
  (the measurement covered the compiler process, not Node).
- **Read today:** docs/core.md ("Numbers", "Text", "Float", "Evaluation
  and conversion", "Partial computations"), docs/proposals/backend-trust.md
  §3.1, `crates/core/src/native.rs` (`register_native` and its pin), and
  where one float native appears in `crates/rt` (`natives.rs`, `prims.rs`,
  `wire.rs`) and `crates/js` (`expr.rs`). §5's sources, by the subagent.
- **Not checked.** B and C were not built: B1's failure to fix the loop
  is an argument from the encodings tried; C's speed is the `Machine`
  simulation; how the erased IR would recognise the `Stream` record, how
  `Array`'s natives behave under `stitchwort test`, and the native-code
  runtime (`--native`) were not looked at. C's and B's lane times are
  estimates with nothing similar measured. E: `cons`, `unfold`,
  `zipWith`, `bisim` and a front-carrying `map` were not written; item 4
  of §3.5 (repeated tails of one stream) was argued, not measured; "4n
  steps" is from the doubling, not counted. D: that a kernel cofix
  re-unfolds at each match is the subagent's reading of Rocq's code;
  cubical Agda was not re-read. Prior art not verified: that the Haskell
  2010 report leaves sharing unspecified; the Mathlib commit that removed
  `LazyList`; Agda's JS backend; Racket's weak-memo support beyond an
  excerpt; Lean's kernel subfolders. From memory only, a lead and not a
  source: Isabelle's code generator has data
  refinement of C's kind (a logical type run as another representation);
  I did not look it up.
