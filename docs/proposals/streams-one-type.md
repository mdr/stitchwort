# Proposal: one stream type that is fast to walk

**Status:** draft 1, 28 November 2026. Ticket SW-4988 (Fable, paper), D3774.
A follow-up to [streams.md](streams.md) (SW-4962), after Matt turned down
D3772(a), its second type for speed: "having two types, one with a
performance trap waiting to bite you, feels wrong to me". A design note
only: nothing in the compiler or std changes. One decision for Matt in
[§6](#6-decision-for-matt) (a revised D3772), and D3770's type changes
shape. The probe, [streams/src/Probe/Walk.sw](streams/src/Probe/Walk.sw),
was checked and run with the main checkout's release binary at
`a9e92441a`.

## 0. Summary

**Recommendation.** One type, a record of three fields:

```
type Stream (a: Type) = {
  at: Nat → a,                                       -- what the stream is
  walk: Nat → Cells a,                               -- how to read it in order, fast
  agrees: ∀ (n: Nat) => walk n = Cells.fromAt at 0 n -- the two never disagree
}
```

`Cells a` is a lazy finite list (`Done | Cell (value: a) (rest: Unit →
Cells a)`): `walk n` gives up to `n` values, each computed only when the
reader asks for the next. Every builder (`iterate`, `unfold`, `map`,
`cons`, `tail`, …) fills in a walk that carries its state forward, with a
proof that it agrees with `at`; every consumer in std (`take`, `find`,
`fold`, `findRepeat`) reads the walk. So a stream is fast to walk however
it was built, and there is nothing to switch to.

Probed (§3), with no kernel change and no trusted code:

- **Speed.** 20,000 values of `Stream.iterate (+ 1) 0`: 0.11 s, against
  26.35 s for the earlier note's `Stream`; 2,000,000 values in 0.67 s
  without building a list.
- **Equality is still `=`.** `Stream.ext` (equal at every position gives
  `s = t`) and `Stream.bisim` hold, stated exactly as before. The walk
  adds speed and no information: every stream equals the plain one with
  the same `at` (`Stream.canonical`).
- **The unfolding laws of the builders still compute.**
  `(Stream.iterate f x).tail = Stream.iterate f (f x)`, `(Stream.unfold
  step st).tail = Stream.unfold step (step st).snd` and `(s.cons x).tail =
  s` are `byComputing`, with no axiom. The earlier note's bisimulation
  proof checks unchanged.
- **The type stays in `Type`**: `Stream (Stream Nat)` works.

**What gives.**

1. A law about an *unknown* stream, such as `(s.map f).tail = s.tail.map
   f`, is no longer bare `byComputing`: it is `Stream.ext _ _ (n =>
   byComputing)`, one line, and so uses `Quot.sound` where it used
   nothing. Std proves these once; users `rewrite` with them as before.
2. Each std function is written twice (its `at` and its walk) with a
   lemma that they agree: 2 to 7 lines of proof each in the probe.
3. One slow pattern remains, and no design inside the kernel's present
   rules removes it ([§4](#4-what-is-left-of-the-trap)): a hand-written
   loop that calls `s.tail` each time round. It is as slow as before
   (4,000 values 1.37 s). The fast loop, over `s.walk fuel`, is also the
   easier one to write, since it needs no fuel argument of its own; a
   warning can catch the slow one.

## 1. The problem

A stream as a function of the position (`at: Nat → a`) is the right
*meaning*: it gives real equality and laws that compute. But `at n` of an
`iterate` or `unfold` starts from the beginning every time, so reading the
first n values in order costs n² steps. The state reached at position n is
thrown away, because a function from `Nat` has nowhere to keep it. The
earlier note kept the state in a second type, `Gen s a`; that leaves the
slow type as the main one, and the user has to know to change. The goal
here is one type with no such choice.

## 2. The options

Sources are in [§7](#7-what-was-verified-and-what-wasnt).

| | Design | One type | Walk n values | Equality is `=` | Laws compute | Trusted code | Universe | Verdict |
|---|---|---|---|---|---|---|---|---|
| A | `Stream` + `Gen s a` (earlier D3772(a)) | no | n² / n | yes (`Stream`) | yes | none | `Type` | turned down |
| B | A memoising native behind `iterate`/`unfold` | yes | n | yes | yes, all | new: a cache with hidden state, in three runtimes | `Type` | not recommended |
| **C** | **`{ at, walk, agrees }`, a lazy walk with a proof** | **yes** | **n** | **yes** | **builders' yes; unknown streams by one-line `ext`** | **none** | **`Type`** | **recommended** |
| C′ | `{ at, prefix: Nat → List a, prefixAgrees }` (the orchestrator's idea) | yes | n, but all of it | yes | as C | none | `Type` | C is the same idea, better |
| D | A quotient of state machines by "same output" | yes | n | yes | no (`Quot.sound` every time) | none | `Type 1` | ruled out |
| E | State in the type: `Stream s a` (Lean's iterators, Rust) | yes | n | no: different states are different types | yes | none | `Type` | ruled out |
| F | Coinductive types in the kernel | yes | n | no, or an axiom | partly | large | `Type` | D3771: no |

**B, the memoising native.** `Stream.unfold` would get a native
implementation that remembers computed states. To the kernel nothing
changes, since a native computes what its pinned definition computes. But
the trusted natives today are number and float operations: pure functions
of their arguments (docs/core.md, "Trust"). This would be the first with
hidden mutable state, three times over (fast runtime, JS, native code),
and a wrong cache gives wrong answers that no proof catches. Other
languages do take this trade: Lean's `Thunk` is "a function `Unit → α`"
to the logic and a caching cell in the runtime ("The Lean runtime has
special support for the `Thunk` type"), and Koka's `delayed` hides a
mutable reference behind `unsafe-total`. They also document the cost:
Scala's `LazyList` warns that "if a reference to the head is retained
unintentionally, then all elements will be retained", and a top-level
`def fibs: Stream Nat` is exactly such a reference, so a long walk of a
named stream would hold every state. C gets the same speed with no
trusted code and constant memory. B also leaves §4's slow pattern in
place: k `tail`s are k nested closures in front of the cache.

**C′, a strict prefix.** `prefix: Nat → List a` passes the same checks as
C (the same proofs, with `List` for `Cells`). But Stitchwort is strict, so
`prefix fuel` computes all `fuel` values before a consumer sees the
first: `find` with a generous fuel does all the work even when the answer
is at position 3, and a fold over a million values builds a million-item
list. Lazy cells stop when the reader stops and use constant memory.
OCaml's `Seq` (`type 'a t = unit -> 'a node`) is the same shape as
`Cells`, for the same reason.

**D, a quotient of machines.** `Machine a` stores its state type, so it
lives in `Type 1`, and so would its quotient: no `List (Stream Nat)`, no
`Stream (Stream a)`, and std's `Quot.funext` (at `Type` only) doesn't
reach it. Stitchwort's `Type` is not impredicative, so nothing hides the
state type for free; a fixed universe of state codes can't hold a user's
own state type. Lean's new iterators met the same wall and put the state
in the type instead; their file says a universe fix "needs to wait for a
language feature", and `Shrink`, meant to move a small type down a
universe, "is just a wrapper" today. Even in `Type`, every law would need
`Quot.sound`, since two machines with the same output are different
terms.

**E, state in the type.** Lean's `Iter {α} β`, Rust's `Iterator`. Fast,
one type, but `Stream.iterate f x` and `Stream.unfold …` would have
different types, "these two streams are equal" could not be stated
between them, and the state shows in every signature. It is `Gen` without
`Stream`. Stream fusion's `data Stream a = forall s. Stream (s → Step a
s) s` hides the state with an existential, which is D.

**Why C works where D fails.** A closure hides its state without an
existential. `walk: Nat → Cells a` for `Stream.unfold step start` is a
closure over `step` and `start`, and each cell's `rest` is a closure over
the next state; the type mentions only `a`. The price is that a cell
list must be finite (an inductive type has no infinite values), which is
why the walk takes a count, and that price is what §4 is about.

## 3. The recommended design, as probed

[Walk.sw](streams/src/Probe/Walk.sw), 211 lines: the type, `head`, `tail`,
`cons`, `map`, `iterate`, `unfold`, `fromFn`, `take`, `find`, `ext`,
`bisim` and the laws below. `stitchwort check` passes and its 6 tests
pass.

**Builders carry the state in the walk.**

```
def Stream.iterateCells (f: a → a) (x: a) (n: Nat): Cells a := match n with
  | Zero => Done
  | Succ k => Cell x (u => Stream.iterateCells f (f x) k)

def Stream.iterate (f: a → a) (x: a): Stream a := {
  at = n => Nat.iterate n f x,
  walk = n => Stream.iterateCells f x n,
  agrees = n => Stream.iterateAgrees f n x
}

def Stream.tail (s: Stream a): Stream a := {
  at = n => s.at (Succ n),
  walk = n => (s.walk (Succ n)).tail,
  agrees = n => Stream.tailAgrees s n
}
```

**Consumers read the walk**, and recurse on the cells, which the
termination checker accepts as structural (a function field's result is
smaller), so they need no fuel argument of their own:

```
def Cells.find (c: Cells a) (p: a → Bool): Option a := match c with
  | Done => None
  | Cell x rest => if p x then Some x else (rest ()).find p

def Stream.find (s: Stream a) (p: a → Bool) (fuel: Nat): Option a := (s.walk fuel).find p

test "find" := (Stream.iterate (+ 1) 0).find (n => n * n > 50) 1000000000000 == Some 8
```

The last line passes at once: the fuel is a bound, not work done.

**What holds, and how.**

| Fact | Proof in the probe | Axioms |
|---|---|---|
| `Stream.ext`: equal at every position gives `s = t` | `s = fromFn s.at` (`canonical`), then `Quot.funext` on `at` | `Quot.sound` |
| `Stream.canonical`: `s = Stream.fromFn s.at` | `agrees` and `Quot.funext` make the walks equal; the two `agrees` proofs are equal by proof irrelevance (`byComputing`) | `Quot.sound` |
| `Stream.bisim` | as in the earlier note, word for word | `Quot.sound` |
| `(iterate f x).tail = iterate f (f x)` | `byComputing` | none |
| `(unfold step st).tail = unfold step (step st).snd` | `byComputing` | none |
| `(s.cons x).tail = s` | `byComputing` | none |
| `((iterate f x).map f).tail = (iterate f (f x)).map f` | `byComputing` | none |
| `(s.map f).tail = s.tail.map f` | `Stream.ext _ _ (n => byComputing)` | `Quot.sound` |
| `(iterate f x).map f = iterate f (f x)` | by position, one line, as before; by bisimulation, Bisim.sw's proof unchanged | `Quot.sound` |
| `Stream (Stream Nat)` | works; the type is in `Type` | |

The builders' laws compute because the walk's first cell is a
constructor: `(Cell x (u => iterateCells f (f x) n)).tail` reduces to
`iterateCells f (f x) n`, and the two `agrees` proofs need no comparing
(the kernel's proof irrelevance). The law about an unknown `s` doesn't,
because `s.walk (Succ n)` is stuck and `tail (map …)` against `map (tail
…)` needs a case split; on the `at` field it still computes, which is
all `ext` asks for.

**What each std function costs.** Its walk, and a lemma that the walk is
`Cells.fromAt at 0 n`. In the probe: `tail` 1 line of proof, `iterate`
5, `map` 2 plus a 4-line lemma about `Cells.map`, `unfold` 5, `cons` 5,
all by induction on the count with one shared lemma (`Cells.fromAtShift`,
3 lines). A function with no better walk uses `Stream.fromFn f`, whose
proof is `byComputing`. The `at` field may be whichever definition makes
proofs easiest, since the walk carries the speed: `interleave` can keep
the earlier note's `unfold`-based `at` (tail law by computing) beside a
direct walk over the two streams' cells.

**Timings.** `(s.take n).sum` for `s = Stream.iterate (+ 1) 0`, fast
runtime, wall clock including about 0.11 s of start-up and cached
checking. Single runs, load average about 6: good for the shape, not the
constants.

| n | Earlier `Stream` (Fn.sw) | New `Stream` (Walk.sw) | `Machine` (Mach.sw) |
|---|---|---|---|
| 1,000 | 0.17 s | 0.11 s | |
| 2,000 | 0.36 s | 0.11 s | |
| 4,000 | 1.13 s | 0.11 s | |
| 20,000 | 26.35 s | 0.11 s (0.32 s with `--js`) | 0.12 s |
| 200,000 | not run | 0.19 s | |
| 2,000,000, summing the cells with no list | | 0.67 s | |

## 4. What is left of the trap

A loop written with `head` and `tail`,

```
def sumByTail (s: Stream Nat) (n acc: Nat): Nat := match n with
  | Zero => acc
  | Succ k => sumByTail s.tail k (acc + s.head)
```

is still quadratic on the new type: 0.19 s, 0.42 s, 1.37 s for 1,000,
2,000, 4,000. After k `tail`s the stream is k closures around the
original, and its head is read through all of them.

This can't be fixed inside the present kernel. A `tail` that costs one
step however many came before must hand back a stream holding the
*current state*. In a type that hides the state and is in `Type`, that
is a value containing a suspended copy of itself, without end: an
infinite value, which an inductive type doesn't have (`{ head: a, rest:
Unit → Stream a }` as an inductive type is empty). Storing the state
openly is D or E. So the choices are coinductive types (D3771), a lazy
runtime representation behind natives (B, grown to cover every stream
function), or accepting it. This is an argument, not a proved theorem.

What makes it acceptable:

- Nothing in std walks that way; `take`, `find`, `fold`, `findRepeat`,
  `zipWith`, `drop` (one closure for any count) all use the walk.
- A user's own loop must already end somehow. The slow loop above needs
  a fuel argument; the fast one is shorter, because recursion on cells
  is structural: `match cells with | Cell x rest => … go (rest ()) |
  Done => …`. The guide teaches that form.
- The slow form is easy to recognise: a recursive call whose stream
  argument is `s.tail`. A warning (`W-STREAM-TAIL-LOOP`, say: "this
  loop reads through one more `tail` each time round; loop over `s.walk
  n` instead") can name it. Proposed as part of S3.

So the trap goes from "any stream built step by step, in every consumer"
to "one hand-written loop shape, with a warning".

## 5. What changes in the earlier note

- **D3770** (streams in std as a library): stands, but the type changes
  shape, from `{ at: Nat → a }` to `{ at, walk, agrees }`, with `Cells`
  beside it. Users see the difference in two places: a stream built from
  a bare function is `Stream.fromFn f`, not a record literal, and loops
  are written over cells. `s.at n`, `ext`, `bisim` and the laws read the
  same.
- **D3771** (no coinductive types in the kernel): unchanged, and §4 is
  now the clearest statement of what that costs.
- **D3772**: replaced by [§6](#6-decision-for-matt). `Stream.Gen` is
  dropped.
- **§4.4** (the memoising native): still "not planned"; with C there is
  no measured need left for it.
- **Plan.** Estimates in agent time, from the probe (the whole of
  Walk.sw took about 10 minutes here, proofs included).

| Stage | What changes | Model | Est. |
|---|---|---|---|
| S1 | `Std.Stream` on the three-field type, with `Cells` (`map`, `tail`, `take`, `drop`, `zipWith`, `find`, `fold`, `toList`, `fromAt` and its lemmas), each stream function's walk and agreement lemma, `ext`, `canonical`, `bisim`, `bisimOn`; the tail laws stated for every function, `byComputing` where they compute; guide section teaching the cells loop | Sonnet; the orchestrator checks statements (D2436) | 50 min (was 35) |
| S2 | Was `Gen`; now the consumers that need care: `findRepeat` (cycle finding) over cells, `foldUntil`, and the timings above in the performance log | Sonnet | 20 min (was 30) |
| S3 | As before, plus the `W-STREAM-TAIL-LOOP` warning | DeepSeek, Sonnet for the page | 30 min (was 20) |
| S4 | Dogfood, unchanged; its friction notes now also judge whether writing a walk for a new stream function is too much work for users | Opus | 30 min |

## 6. Decision for Matt

**D3772 (revised): make `Stream` one three-field type, `{ at, walk,
agrees }`, fast to walk however it was built, with no second type and no
trusted code? [rec: yes]**

- *The problem.* The earlier `Stream` was slow to walk when built step
  by step (20,000 values: 26 s, measured), and the fix offered was a
  second type the user had to know to switch to.
- *The change.* A stream carries, beside its meaning (`at`), a lazy walk
  that keeps the builder's state, and a proof that the two agree. Std's
  builders fill it in and std's consumers read it. This changes D3770's
  type from one field to three. No kernel change, no native, no new
  axiom.
- *What it should do.* The same 20,000 values in 0.11 s (measured), and
  2,000,000 in 0.67 s in constant memory, for every stream. Streams
  equal everywhere are still `=`, and the builders' tail laws still
  compute (checked). What it costs: laws about an unknown stream are a
  one-line `ext` in std instead of `byComputing`; std's stream functions
  each need a short agreement proof (about 15 minutes more lane time);
  and a hand-written loop over `s.tail` stays slow, which a warning
  would flag, since only kernel coinduction or a trusted lazy runtime
  could remove it.

If the remaining `tail` loop is not acceptable even with a warning, the
alternative to bring back is B (a trusted lazy representation), not A.

## 7. What was verified, and what wasn't

- **Run today** (release binary at `a9e92441a`, copied; `STITCHWORT_JOBS=2`):
  everything in §3 and §4. `stitchwort check Probe.Walk` passes,
  `stitchwort test Probe.Walk` passes 6 tests, and `stitchwort axioms`
  gave the axioms column. Timings are single runs on a loaded machine.
- **Read today at a pinned tag** (by a research subagent; quotations are
  from its report, which gave file and tag for each):
  - Lean `v4.36.0`: `src/Init/Data/Iterators/Basic.lean` (`structure
    Iter {α : Type w} (β : Type w) where internalState : α`; `Shrink`'s
    docstring), `src/Std/Data/Iterators.lean` (the planned universe
    change), `src/Init/Core.lean` (`Thunk`).
  - Mathlib `v4.36.0`, `Mathlib/Data/Stream/Defs.lean`: `Stream'` is `ℕ
    → α`, `corec` is `map f (iterate g a)`, and no `implemented_by`,
    `csimp` or memoisation was found in `Init.lean` or the first 140
    lines of `Defs.lean`; so Mathlib's stream has this note's n² problem
    and no answer to it. Batteries `v4.36.0` `MLList`: an `opaque` type
    over a private `unsafe` implementation, about which nothing can be
    proved.
  - `stream-fusion-0.1.2.5` `Data/Stream.hs` and `vector`
    (`vector-stream-0.1.0.1`): the existential state.
  - OCaml `5.4.0` `stdlib/seq.mli`: `type 'a t = unit -> 'a node`, not
    memoised unless `Seq.memoize` is called.
  - Scala `v2.13.18` `LazyList.scala`: memoised, with the retention
    warning quoted.
  - Koka `v3.2.9` `lib/std/core/delayed.kk`: a cached delay over a
    hidden mutable reference.
  - Idris 2 `v0.8.0` `src/Compiler/Scheme/Common.idr`: `Inf` and `Lazy`
    compile to a plain lambda by default, re-run on every force
    (`lazy=weakMemo` opts in to weak caching). So Idris's streams are
    not shared at run time by default, which answers part of the
    earlier note's unchecked "shared" column.
  - Agda `v2.9.0` `MAlonzo/RTE.hs`: musical `∞` is a lazy Haskell field
    (`data Inf a = Sharp { flat :: a }`), so GHC shares it; this is
    inferred from the definition, not stated by Agda's docs.
  - Rust `1.90.0` `iterator.rs`: the state is the implementing type.
- **Not checked:** the stream fusion paper itself (only the packages);
  whether Lean has a type-erased iterator (none found by file name);
  how Agda compiles coinductive *record* fields; Idris's other backends;
  Unison; F\* (no stream file found by name in `ulib/`); `Box<dyn
  Iterator>`. C′ was not probed (argued from C's proofs and strict
  evaluation). `zipWith`, `drop`, `interleave` and `findRepeat` on the
  new type were not written; their costs are estimated from the five
  functions that were. The claim in §4 that no in-kernel design gives a
  one-step `tail` is an argument, not a proof. The native-code runtime
  (`--native`) was not tried, only the fast runtime and `--js`.
