--| The parts `Stream` (Stream/Stream.sw) is built from: `Stream.Cells`, a
--| finite run of values computed as they are read; `Stream.Base`, what a
--| stream's values are and how to walk them; and `Stream.Front`, where a
--| reader has got to. Programs use `Stream` and its functions, not these.
-- docs/proposals/streams-head-tail.md §3.5; the base is
-- docs/proposals/streams-one-type.md's three-field stream.
-- Calls between these types are written in full (`Stream.Cells.map c f`,
-- not `c.map f`): a dot call could mean any type's function of that name,
-- which ties the types and functions of one file into a cycle.

import Std (Eq)
import Stream.Cells (Done, Cell)

--| A finite run of values, each one after the first computed only when it
--| is asked for: `Cell 1 (u => Cell 2 (u => Done))` is 1 then 2. A stream
--| hands its values out as cells.
type Stream.Cells (a: Type) =
  | Done
  | Cell (value: a) (rest: Unit → Stream.Cells a)

--| The cells after the first, or none if there are none.
def Stream.Cells.tail (c: Stream.Cells a): Stream.Cells a := match c with
  | Done => Done
  | Cell x rest => rest ()

--| The cells after the first `n`.
def Stream.Cells.skip (c: Stream.Cells a) (n: Nat): Stream.Cells a := match n with
  | Zero => c
  | Succ k => (Stream.Cells.tail c).skip k

--| `f` of each value, computed as each is read.
def Stream.Cells.map (c: Stream.Cells a) (f: a → b): Stream.Cells b := match c with
  | Done => Done
  | Cell x rest => Cell (f x) (u => Stream.Cells.map (rest ()) f)

--| Every value, in order.
def Stream.Cells.toList (c: Stream.Cells a): List a := match c with
  | Done => []
  | Cell x rest => [x, ..(rest ()).toList]

--| `n` values of `f`, at positions `i`, `i + 1`, …: what a stream's walk of
--| `n` values must equal, for `i` = 0.
@[noReceiver]
def Stream.Cells.fromAt (f: Nat → a) (i n: Nat): Stream.Cells a := match n with
  | Zero => Done
  | Succ k => Cell (f i) (u => Stream.Cells.fromAt f (Succ i) k)

--| Starting one position on is reading the function one position on.
theorem Stream.Cells.fromAtShift ∀ (g: Nat → a) (k i: Nat):
    Stream.Cells.fromAt g (Succ i) k = Stream.Cells.fromAt (j => g (Succ j)) i k :=
  match k with
    | Zero => byComputing
    | Succ m => Eq.cong (r => Cell (g (Succ i)) (u => r)) (Stream.Cells.fromAtShift g m (Succ i))

--| Mapping the values of `g` is reading `f` of `g`.
theorem Stream.Cells.mapFromAt ∀ (g: Nat → a) (f: a → b) (n i: Nat):
    Stream.Cells.map (Stream.Cells.fromAt g i n) f = Stream.Cells.fromAt (j => f (g j)) i n :=
  match n with
    | Zero => byComputing
    | Succ k => Eq.cong (r => Cell (f (g i)) (u => r)) (Stream.Cells.mapFromAt g f k (Succ i))

--| What a stream is, without a reader's place: its value at each position
--| (`at`), a way to read the first `n` values in `n` steps (`walk`), and a
--| proof that the walk reads the values of `at` (`agrees`). Every
--| `Stream` has one as its `base`; programs use `Stream` itself.
type Stream.Base (a: Type) = {
  at: Nat → a,
  walk: Nat → Stream.Cells a,
  agrees: ∀ (n: Nat) => walk n = Stream.Cells.fromAt at 0 n
}

--| A walk of `n + 1` values, less its first, is the `n` values from position 1.
theorem Stream.Base.tailAgrees ∀ (s: Stream.Base a) (n: Nat):
    Stream.Cells.tail (s.walk (Succ n)) = Stream.Cells.fromAt (k => s.at (Succ k)) 0 n :=
  rewrite s.agrees (Succ n) then Stream.Cells.fromAtShift s.at n 0

--| The base from position 1 on.
def Stream.Base.tail (s: Stream.Base a): Stream.Base a :=
  { at = n => s.at (Succ n), walk = n => Stream.Cells.tail (s.walk (Succ n)), agrees = n => Stream.Base.tailAgrees s n }

--| A walk of `k + n` values from a base, less its first `k`, is the `n`
--| values from position `k`.
theorem Stream.Base.dropAgrees ∀ (k: Nat) (s: Stream.Base a) (n: Nat):
    (s.walk (k + n)).skip k = Stream.Cells.fromAt (j => s.at (k + j)) 0 n :=
  match k with
    | Zero => s.agrees n
    | Succ m => Stream.Base.dropAgrees m (Stream.Base.tail s) n

--| The base from position `k` on, as one closure whatever `k` is.
def Stream.Base.drop (s: Stream.Base a) (k: Nat): Stream.Base a :=
  { at = j => s.at (k + j), walk = n => (s.walk (k + n)).skip k, agrees = n => Stream.Base.dropAgrees k s n }

--| The base whose only walk is reading each position.
@[noReceiver]
def Stream.Base.fromFn (f: Nat → a): Stream.Base a :=
  { at = f, walk = n => Stream.Cells.fromAt f 0 n, agrees = n => byComputing }

--| Two bases with the same `at` and walks equal as functions are equal,
--| whatever their `agrees` proofs.
theorem Stream.Base.walkIrrelevant ∀ (f: Nat → a) (w v: Nat → Stream.Cells a)
    (hw: w = v)
    (p: ∀ (n: Nat) => w n = Stream.Cells.fromAt f 0 n):
    ∀ (q: ∀ (n: Nat) => v n = Stream.Cells.fromAt f 0 n) => ({ at = f, walk = w, agrees = p }: Stream.Base a)
      = { at = f, walk = v, agrees = q } :=
  J
    (v' hw' =>
      ∀ (q': ∀ (n: Nat) => v' n = Stream.Cells.fromAt f 0 n) => ({ at = f, walk = w, agrees = p }: Stream.Base a)
        = { at = f, walk = v', agrees = q' })
    (q' => byComputing)
    hw

--| Every base is the plain one with the same values: the walk adds speed,
--| not information.
theorem Stream.Base.canonical ∀ (s: Stream.Base a): s = Stream.Base.fromFn s.at :=
  Stream.Base.walkIrrelevant s.at s.walk
    (n => Stream.Cells.fromAt s.at 0 n)
    (Quot.funext Nat (n => Stream.Cells a) s.walk (n => Stream.Cells.fromAt s.at 0 n) s.agrees)
    s.agrees
    (n => byComputing)

--| Two bases with the same value at every position are equal.
theorem Stream.Base.ext ∀ (s t: Stream.Base a) (h: ∀ (n: Nat) => s.at n = t.at n): s = t := calc s
  _ = Stream.Base.fromFn s.at := Stream.Base.canonical s
  _ = Stream.Base.fromFn t.at := Eq.cong (f => Stream.Base.fromFn f) (Quot.funext Nat (n => a) s.at t.at h)
  _ = t := (Stream.Base.canonical t).flipped

--| `n` values of `x`, `f x`, `f (f x)`, ….
@[noReceiver]
def Stream.Base.iterateCells (f: a → a) (x: a) (n: Nat): Stream.Cells a := match n with
  | Zero => Done
  | Succ k => Cell x (u => Stream.Base.iterateCells f (f x) k)

--| Iterating reads `Nat.iterate` at each position.
theorem Stream.Base.iterateAgrees ∀ (f: a → a) (n: Nat) (x: a):
    Stream.Base.iterateCells f x n = Stream.Cells.fromAt (j => Nat.iterate j f x) 0 n :=
  match n with
    | Zero => byComputing
    | Succ k =>
      rewrite Stream.Cells.fromAtShift (j => Nat.iterate j f x) k 0 then
        Eq.cong (r => Cell x (u => r)) (Stream.Base.iterateAgrees f k (f x))

--| `x`, `f x`, `f (f x)`, … as a base.
@[noReceiver]
def Stream.Base.iterate (f: a → a) (x: a): Stream.Base a := {
  at = n => Nat.iterate n f x,
  walk = n => Stream.Base.iterateCells f x n,
  agrees = n => Stream.Base.iterateAgrees f n x
}

--| Mapping a walk reads `f` of each value.
theorem Stream.Base.mapAgrees ∀ (s: Stream.Base a) (f: a → b) (n: Nat):
    Stream.Cells.map (s.walk n) f = Stream.Cells.fromAt (j => f (s.at j)) 0 n :=
  rewrite s.agrees n then Stream.Cells.mapFromAt s.at f n 0

--| `f` of each value of a base.
def Stream.Base.map (s: Stream.Base a) (f: a → b): Stream.Base b :=
  { at = n => f (s.at n), walk = n => Stream.Cells.map (s.walk n) f, agrees = n => Stream.Base.mapAgrees s f n }

--| `n` values unfolded from `state` by `step`.
@[noReceiver]
def Stream.Base.unfoldCells [s: Type] (step: s → Pair a s) (state: s) (n: Nat): Stream.Cells a := match n with
  | Zero => Done
  | Succ k =>
    let p := step state
    Cell p.fst (u => Stream.Base.unfoldCells step p.snd k)

--| Unfolding reads, at position `j`, the value `step` gives from the `j`th state.
theorem Stream.Base.unfoldAgrees ∀ (s: Type) (step: s → Pair a s) (n: Nat) (state: s):
    Stream.Base.unfoldCells step state n
      = Stream.Cells.fromAt (j => (step (Nat.iterate j (st => (step st).snd) state)).fst) 0 n :=
  match n with
    | Zero => byComputing
    | Succ k =>
      rewrite Stream.Cells.fromAtShift (j => (step (Nat.iterate j (st => (step st).snd) state)).fst) k 0 then
        Eq.cong (r => Cell (step state).fst (u => r)) (Stream.Base.unfoldAgrees s step k (step state).snd)

--| The values `step` gives from `start`, then from each next state, as a base.
@[noReceiver]
def Stream.Base.unfold [s: Type] (step: s → Pair a s) (start: s): Stream.Base a := {
  at = n => (step (Nat.iterate n (st => (step st).snd) start)).fst,
  walk = n => Stream.Base.unfoldCells step start n,
  agrees = n => Stream.Base.unfoldAgrees s step n start
}

--| `x` at position 0, then the base's values.
def Stream.Base.consAt (s: Stream.Base a) (x: a) (n: Nat): a := match n with
  | Zero => x
  | Succ m => s.at m

--| `n` values of `x` followed by the base.
def Stream.Base.consWalk (s: Stream.Base a) (x: a) (n: Nat): Stream.Cells a := match n with
  | Zero => Done
  | Succ m => Cell x (u => s.walk m)

--| Walking `x` then the base reads `consAt`.
theorem Stream.Base.consAgrees ∀ (s: Stream.Base a) (x: a) (n: Nat):
    s.consWalk x n = Stream.Cells.fromAt (s.consAt x) 0 n :=
  match n with
    | Zero => byComputing
    | Succ m =>
      rewrite s.agrees m then Eq.cong (r => Cell x (u => r)) (Stream.Cells.fromAtShift (s.consAt x) m 0).flipped

--| `x`, then the base's values.
def Stream.Base.cons (s: Stream.Base a) (x: a): Stream.Base a :=
  { at = s.consAt x, walk = s.consWalk x, agrees = Stream.Base.consAgrees s x }

--| A reader's place in a stream whose values are `at`: the stream it
--| started from (`origin`), how many tails it has taken since (`offset`),
--| and the next few values (`cells`), for some number of them.
type Stream.Front (a: Type) (at: Nat → a) = {
  origin: Stream.Base a,
  offset: Nat,
  cells: Stream.Cells a,
  shifted: ∀ (n: Nat) => at n = origin.at (offset + n),
  ok: ∃ (m: Nat) => cells = Stream.Cells.fromAt (j => origin.at (offset + j)) 0 m
}

--| Every two fronts are related: which one a stream has is forgotten.
def Stream.Front.same [at: Nat → a] (x y: Stream.Front a at): Prop := True = True

--| The first cell, or position 0 of `at` when the cells have run out. It
--| takes `at`, not `at 0`, so that a stream with cells left doesn't read
--| the slow way.
def Stream.Cells.headOr (c: Stream.Cells a) (at: Nat → a): a := match c with
  | Done => at 0
  | Cell x rest => x

--| `headOr` of the cells of `g` is `g 0`.
theorem Stream.Cells.headOrFromAt ∀ (g: Nat → a) (c: Stream.Cells a) (m: Nat)
    (h: c = Stream.Cells.fromAt g 0 m):
    c.headOr g = g 0 :=
  rewrite h then
    match m with
      | Zero => byComputing
      | Succ k => byComputing

--| The value a front is at.
def Stream.Front.head [at: Nat → a] (fr: Stream.Front a at): a :=
  Stream.Cells.headOr fr.cells (j => fr.origin.at (fr.offset + j))

--| A front is at position 0 of its values.
theorem Stream.Front.headIs ∀ (at: Nat → a) (fr: Stream.Front a at): Stream.Front.head fr = at 0 :=
  (Exists.elim fr.ok (m h => Stream.Cells.headOrFromAt (j => fr.origin.at (fr.offset + j)) fr.cells m h)).trans
    (fr.shifted 0).flipped

--| The cells themselves, or when they have run out a fresh walk from the
--| origin, twice as far as the reader has come, skipped to its place.
def Stream.Cells.refill (c: Stream.Cells a) (origin: Stream.Base a) (offset: Nat): Stream.Cells a := match c with
  | Done => Stream.Cells.skip (origin.walk (offset + (offset + 2))) offset
  | Cell x rest => Cell x rest

--| A front's cells one step on are again cells of the origin.
theorem Stream.Front.nextOk ∀ (origin: Stream.Base a) (offset: Nat) (c: Stream.Cells a) (m: Nat)
    (h: c = Stream.Cells.fromAt (j => origin.at (offset + j)) 0 m):
    ∃ (i: Nat) => Stream.Cells.tail (Stream.Cells.refill c origin offset)
      = Stream.Cells.fromAt (j => origin.at (offset + 1 + j)) 0 i :=
  rewrite h then
    match m with
      | Zero =>
        Witness
          (Succ offset)
          (rewrite Stream.Base.dropAgrees offset origin (offset + 2) then
            Stream.Cells.fromAtShift (j => origin.at (offset + j)) (Succ offset) 0)
      | Succ k => Witness k (Stream.Cells.fromAtShift (j => origin.at (offset + j)) k 0)
