namespace Probe.Seq

import Std (Quot, Nat, Eq, Exists)
import Probe.Walk (Stream, Cells)

-- A stream whose `tail` is one step (amortised) however it was built, with
-- no trusted code. A `Seq` is a three-field stream (`base`: what it is) plus a
-- `front`: where a reader has got to. The front holds the stream the reader
-- started from, the count of tails since, and the cells from here on for some
-- number of values. `tail` steps along the cells; when they run out it walks
-- again from the start for twice the distance. Which front a `Seq` has is
-- forgotten (the quotient relates every two), so it adds speed and no
-- information: two `Seq`s with the same values are `=` (`Seq.ext`).

def Cells.skip (c: Cells a) (n: Nat): Cells a := match n with
  | Zero => c
  | Succ k => Cells.skip (Cells.tail c) k

theorem Stream.dropAgrees ∀ (k: Nat) (s: Stream a) (n: Nat):
    Cells.skip (s.walk (k + n)) k = Cells.fromAt (j => s.at (k + j)) 0 n :=
  match k with
    | Zero => s.agrees n
    | Succ m => Stream.dropAgrees m (Stream.tail s) n

-- The stream from position `k` on: one closure for any `k`.
def Stream.drop (s: Stream a) (k: Nat): Stream a :=
  { at = j => s.at (k + j), walk = n => Cells.skip (s.walk (k + n)) k, agrees = n => Stream.dropAgrees k s n }

-- The first value, or position 0 read from `at` when the cells have run out. It takes `at`, not
-- `at 0`: arguments are computed before a call, and reading a position of the origin is slow.
def Cells.headOr (c: Cells a) (at: Nat → a): a := match c with
  | Done => at 0
  | Cell x rest => x

-- The cells themselves, or when they have run out a fresh walk from the origin, twice as far.
def Cells.refill (c: Cells a) (origin: Stream a) (offset: Nat): Cells a := match c with
  | Done => Cells.skip (origin.walk (offset + (offset + 2))) offset
  | Cell x rest => Cell x rest

type Front (a: Type) (at: Nat → a) = {
  origin: Stream a,
  offset: Nat,
  cells: Cells a,
  shifted: ∀ (n: Nat) => at n = origin.at (offset + n),
  ok: ∃ (m: Nat) => cells = Cells.fromAt (j => origin.at (offset + j)) 0 m
}

def Front.same [at: Nat → a] (x y: Front a at): Prop := True = True

type Seq (a: Type) = {
  base: Stream a,
  front: Quot (Front a base.at) Front.same
}

@[noReceiver]
def Seq.of (s: Stream a): Seq a := {
  base = s,
  front = Quot.mk { origin = s, offset = 0, cells = Done, shifted = n => byComputing, ok = Witness 0 byComputing }
}

theorem Front.allEqual ∀ (at: Nat → a) (x y: Quot (Front a at) Front.same): x = y :=
  Quot.ind
    [p := x' => x' = y]
    (fx => Quot.ind [p := y' => Quot.mk fx = y'] (fy => Quot.sound (byComputing: Front.same fx fy)) y)
    x

theorem Seq.sameBase ∀ (b c: Stream a)
    (h: b = c)
    (x: Quot (Front a b.at) Front.same):
    ∀ (y: Quot (Front a c.at) Front.same) => ({ base = b, front = x }: Seq a) = { base = c, front = y } :=
  J
    (c' h' => ∀ (y': Quot (Front a c'.at) Front.same) => ({ base = b, front = x }: Seq a) = { base = c', front = y' })
    (y' => Eq.cong (f => ({ base = b, front = f }: Seq a)) (Front.allEqual b.at x y'))
    h

-- Two `Seq`s with the same value at every position are equal.
theorem Seq.ext ∀ (q r: Seq a) (h: ∀ (n: Nat) => q.base.at n = r.base.at n): q = r :=
  Seq.sameBase q.base r.base (Stream.ext q.base r.base h) q.front r.front

theorem Cells.headOrFromAt ∀ (g: Nat → a) (c: Cells a) (m: Nat) (h: c = Cells.fromAt g 0 m): c.headOr g = g 0 :=
  rewrite h then
    match m with
      | Zero => byComputing
      | Succ k => byComputing

def Front.head [at: Nat → a] (fr: Front a at): a := fr.cells.headOr (j => fr.origin.at (fr.offset + j))

theorem Front.headIs ∀ (at: Nat → a) (fr: Front a at): fr.head = at 0 :=
  (Exists.elim fr.ok (m h => Cells.headOrFromAt (j => fr.origin.at (fr.offset + j)) fr.cells m h)).trans
    (fr.shifted 0).flipped

def Seq.head (q: Seq a): a :=
  Quot.lift (fr => fr.head) (x y same => (Front.headIs q.base.at x).trans (Front.headIs q.base.at y).flipped) q.front

theorem Front.nextOk ∀ (origin: Stream a) (offset: Nat) (c: Cells a) (m: Nat)
    (h: c = Cells.fromAt (j => origin.at (offset + j)) 0 m):
    ∃ (i: Nat) => Cells.tail (Cells.refill c origin offset) = Cells.fromAt (j => origin.at (offset + 1 + j)) 0 i :=
  rewrite h then
    match m with
      | Zero =>
        Witness
          (Succ offset)
          (rewrite Stream.dropAgrees offset origin (offset + 2) then
            Cells.fromAtShift (j => origin.at (offset + j)) (Succ offset) 0)
      | Succ k => Witness k (Cells.fromAtShift (j => origin.at (offset + j)) k 0)

-- One step on: the `Seq` of the tail, built from the origin, so that it holds nothing of the `Seq` before it.
def Front.step [at: Nat → a] (fr: Front a at): Seq a := {
  base = Stream.drop fr.origin (fr.offset + 1),
  front = Quot.mk {
    origin = fr.origin,
    offset = fr.offset + 1,
    cells = Cells.tail (Cells.refill fr.cells fr.origin fr.offset),
    shifted = n => byComputing,
    ok = Exists.elim fr.ok (m h => Front.nextOk fr.origin fr.offset fr.cells m h)
  }
}

theorem Front.stepAt ∀ (at: Nat → a) (fr: Front a at) (n: Nat): fr.step.base.at n = at (Succ n) :=
  (fr.shifted (Succ n)).flipped

def Seq.tail (q: Seq a): Seq a :=
  Quot.lift
    (fr => fr.step)
    (x y same => Seq.ext x.step y.step (n => (Front.stepAt q.base.at x n).trans (Front.stepAt q.base.at y n).flipped))
    q.front

test "seq" := (Seq.of (Stream.iterate (* 2) 1)).tail.tail.tail.tail.tail.head == 32

theorem Seq.headIs ∀ (q: Seq a): q.head = q.base.at 0 :=
  Quot.ind [p := f => Seq.head { base = q.base, front = f } = q.base.at 0] (fr => Front.headIs q.base.at fr) q.front

-- What `tail` means, for any `Seq`: std would state every law through this and `Seq.headIs`.
theorem Seq.tailAt ∀ (q: Seq a) (n: Nat): q.tail.base.at n = q.base.at (Succ n) :=
  Quot.ind
    [p := f => (Seq.tail { base = q.base, front = f }).base.at n = q.base.at (Succ n)]
    (fr => Front.stepAt q.base.at fr n)
    q.front

@[noReceiver]
def Seq.iterate (f: a → a) (x: a): Seq a := Seq.of (Stream.iterate f x)

theorem Seq.iterateTail ∀ (f: a → a) (x: a): (Seq.iterate f x).tail = Seq.iterate f (f x) :=
  Seq.ext (Seq.iterate f x).tail (Seq.iterate f (f x)) (n => byComputing)

def Seq.map (q: Seq a) (f: a → b): Seq b := Seq.of (q.base.map f)

theorem Seq.mapTail ∀ (q: Seq a) (f: a → b): (q.map f).tail = q.tail.map f :=
  Seq.ext (q.map f).tail (q.tail.map f) (n => Eq.cong f (Seq.tailAt q n).flipped)

-- The loop a newcomer writes, here run by `stitchwort test` on the checker's own evaluator.
def Seq.sumFirst (q: Seq Nat) (k acc: Nat): Nat := match k with
  | Zero => acc
  | Succ j => Seq.sumFirst (Seq.tail q) j (acc + Seq.head q)

test "loop" := (Seq.iterate (+ 1) 0).sumFirst 20000 0 == 199990000

def nested: Seq (Seq Nat) := Seq.iterate (q => q.map (+ 1)) (Seq.iterate (* 2) 1)

test "nested" := nested.tail.tail.head.tail.head == 4
