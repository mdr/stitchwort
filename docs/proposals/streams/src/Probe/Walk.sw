namespace Probe.Walk

import Std (Quot, Nat, Eq)

-- A finite run of values, each next one computed only when asked for.
type Cells (a: Type) = | Done | Cell (value: a) (rest: Unit → Cells a)

def Cells.tail (c: Cells a): Cells a := match c with
  | Done => Done
  | Cell x rest => rest ()

def Cells.map (c: Cells a) (f: a → b): Cells b := match c with
  | Done => Done
  | Cell x rest => Cell (f x) (u => Cells.map (rest ()) f)

def Cells.toList (c: Cells a): List a := match c with
  | Done => []
  | Cell x rest => [x, ..(rest ()).toList]

def Cells.sum (c: Cells Nat) (acc: Nat): Nat := match c with
  | Done => acc
  | Cell x rest => (rest ()).sum (acc + x)

-- The values of `f` at positions `i`, `i + 1`, …, `n` of them: what a walk must equal.
@[noReceiver]
def Cells.fromAt (f: Nat → a) (i n: Nat): Cells a := match n with
  | Zero => Done
  | Succ k => Cell (f i) (u => Cells.fromAt f (Succ i) k)

theorem Cells.fromAtShift ∀ (g: Nat → a) (k i: Nat): Cells.fromAt g (Succ i) k = Cells.fromAt (j => g (Succ j)) i k :=
  match k with
    | Zero => byComputing
    | Succ m => Eq.cong (r => Cell (g (Succ i)) (u => r)) (Cells.fromAtShift g m (Succ i))

type Stream (a: Type) = {
  at: Nat → a,
  walk: Nat → Cells a,
  agrees: ∀ (n: Nat) => walk n = Cells.fromAt at 0 n
}

def Stream.head (s: Stream a): a := s.at 0

def Stream.take (s: Stream a) (n: Nat): List a := (s.walk n).toList

theorem Stream.tailAgrees ∀ (s: Stream a) (n: Nat): (s.walk (Succ n)).tail = Cells.fromAt (k => s.at (Succ k)) 0 n :=
  rewrite s.agrees (Succ n) then Cells.fromAtShift s.at n 0

def Stream.tail (s: Stream a): Stream a :=
  { at = n => s.at (Succ n), walk = n => (s.walk (Succ n)).tail, agrees = n => Stream.tailAgrees s n }

@[noReceiver]
def Stream.iterateCells (f: a → a) (x: a) (n: Nat): Cells a := match n with
  | Zero => Done
  | Succ k => Cell x (u => Stream.iterateCells f (f x) k)

theorem Stream.iterateAgrees ∀ (f: a → a) (n: Nat) (x: a):
    Stream.iterateCells f x n = Cells.fromAt (j => Nat.iterate j f x) 0 n :=
  match n with
    | Zero => byComputing
    | Succ k =>
      rewrite Cells.fromAtShift (j => Nat.iterate j f x) k 0 then
        Eq.cong (r => Cell x (u => r)) (Stream.iterateAgrees f k (f x))

@[noReceiver]
def Stream.iterate (f: a → a) (x: a): Stream a :=
  { at = n => Nat.iterate n f x, walk = n => Stream.iterateCells f x n, agrees = n => Stream.iterateAgrees f n x }

theorem iterateTail ∀ (f: a → a) (x: a): (Stream.iterate f x).tail = Stream.iterate f (f x) := byComputing

test "take" := (Stream.iterate (* 2) 1).take 5 == [1, 2, 4, 8, 16]
test "tail" := (Stream.iterate (* 2) 1).tail.tail.take 3 == [4, 8, 16]

-- The stream with no better walk than reading each position.
@[noReceiver]
def Stream.fromFn (f: Nat → a): Stream a := { at = f, walk = n => Cells.fromAt f 0 n, agrees = n => byComputing }

theorem Stream.walkIrrelevant ∀ (f: Nat → a) (w v: Nat → Cells a)
    (hw: w = v)
    (p: ∀ (n: Nat) => w n = Cells.fromAt f 0 n):
    ∀ (q: ∀ (n: Nat) => v n = Cells.fromAt f 0 n) => ({ at = f, walk = w, agrees = p }: Stream a)
      = { at = f, walk = v, agrees = q } :=
  J
    (v' hw' =>
      ∀ (q': ∀ (n: Nat) => v' n = Cells.fromAt f 0 n) => ({ at = f, walk = w, agrees = p }: Stream a)
        = { at = f, walk = v', agrees = q' })
    (q' => byComputing)
    hw

-- Every stream is the plain one with the same values: the walk adds speed, not information.
theorem Stream.canonical ∀ (s: Stream a): s = Stream.fromFn s.at :=
  Stream.walkIrrelevant s.at s.walk
    (n => Cells.fromAt s.at 0 n)
    (Quot.funext Nat (n => Cells a) s.walk (n => Cells.fromAt s.at 0 n) s.agrees)
    s.agrees
    (n => byComputing)

theorem Stream.ext ∀ (s t: Stream a) (h: ∀ (n: Nat) => s.at n = t.at n): s = t := calc s
  _ = Stream.fromFn s.at := Stream.canonical s
  _ = Stream.fromFn t.at := Eq.cong (f => Stream.fromFn f) (Quot.funext Nat (n => a) s.at t.at h)
  _ = t := (Stream.canonical t).flipped

theorem Stream.bisimAt ∀ (r: Stream a → Stream a → Prop)
    (step: ∀ (s t: Stream a) => r s t → s.head = t.head ∧ r s.tail t.tail)
    (n: Nat) (s t: Stream a) (h: r s t):
    s.at n = t.at n :=
  match n with
    | Zero => (step s t h).left
    | Succ m => Stream.bisimAt r step m s.tail t.tail (step s t h).right

theorem Stream.bisim ∀ (r: Stream a → Stream a → Prop)
    (step: ∀ (s t: Stream a) => r s t → s.head = t.head ∧ r s.tail t.tail)
    (s t: Stream a) (h: r s t):
    s = t :=
  Stream.ext s t (n => Stream.bisimAt r step n s t h)

theorem Cells.mapFromAt ∀ (g: Nat → a) (f: a → b) (n i: Nat):
    (Cells.fromAt g i n).map f = Cells.fromAt (j => f (g j)) i n :=
  match n with
    | Zero => byComputing
    | Succ k => Eq.cong (r => Cell (f (g i)) (u => r)) (Cells.mapFromAt g f k (Succ i))

theorem Stream.mapAgrees ∀ (s: Stream a) (f: a → b) (n: Nat): (s.walk n).map f = Cells.fromAt (j => f (s.at j)) 0 n :=
  rewrite s.agrees n then Cells.mapFromAt s.at f n 0

def Stream.map (s: Stream a) (f: a → b): Stream b :=
  { at = n => f (s.at n), walk = n => (s.walk n).map f, agrees = n => Stream.mapAgrees s f n }

theorem mapTail ∀ (s: Stream a) (f: a → b): (s.map f).tail = s.tail.map f :=
  Stream.ext (s.map f).tail (s.tail.map f) (n => byComputing)

theorem mapIterateTail ∀ (f: a → a) (x: a): ((Stream.iterate f x).map f).tail = (Stream.iterate f (f x)).map f :=
  byComputing

theorem Stream.mapIterate ∀ (f: a → a) (x: a): (Stream.iterate f x).map f = Stream.iterate f (f x) :=
  Stream.ext ((Stream.iterate f x).map f) (Stream.iterate f (f x)) (n => (Nat.iterateSuccLast f n x).flipped)

@[noReceiver]
def Stream.unfoldCells [s: Type] (step: s → Pair a s) (state: s) (n: Nat): Cells a := match n with
  | Zero => Done
  | Succ k =>
    let p := step state
    Cell p.fst (u => Stream.unfoldCells step p.snd k)

theorem Stream.unfoldAgrees ∀ (s: Type) (step: s → Pair a s) (n: Nat) (state: s):
    Stream.unfoldCells step state n = Cells.fromAt (j => (step (Nat.iterate j (st => (step st).snd) state)).fst) 0 n :=
  match n with
    | Zero => byComputing
    | Succ k =>
      rewrite Cells.fromAtShift (j => (step (Nat.iterate j (st => (step st).snd) state)).fst) k 0 then
        Eq.cong (r => Cell (step state).fst (u => r)) (Stream.unfoldAgrees s step k (step state).snd)

@[noReceiver]
def Stream.unfold [s: Type] (step: s → Pair a s) (start: s): Stream a := {
  at = n => (step (Nat.iterate n (st => (step st).snd) start)).fst,
  walk = n => Stream.unfoldCells step start n,
  agrees = n => Stream.unfoldAgrees s step n start
}

theorem unfoldTail ∀ (s: Type) (step: s → Pair a s) (start: s):
    (Stream.unfold step start).tail = Stream.unfold step (step start).snd :=
  byComputing

def fibs: Stream Nat := Stream.unfold (p => (p.fst, (p.snd, p.fst + p.snd))) (0, 1)

def nested: Stream (Stream Nat) := Stream.iterate (s => s.map (+ 1)) fibs

test "fibs" := fibs.take 8 == [0, 1, 1, 2, 3, 5, 8, 13]
test "nested" := (nested.at 2).take 3 == [2, 3, 3]
test "map" := ((Stream.iterate (+ 1) 0).map (* 3)).tail.take 3 == [3, 6, 9]

-- The first value within `fuel` that satisfies `p`: stops reading as soon as it is found.
def Cells.find (c: Cells a) (p: a → Bool): Option a := match c with
  | Done => None
  | Cell x rest => if p x then Some x else (rest ()).find p

def Stream.find (s: Stream a) (p: a → Bool) (fuel: Nat): Option a := (s.walk fuel).find p

test "find" := (Stream.iterate (+ 1) 0).find (n => n * n > 50) 1000000000000 == Some 8

def Stream.consAt (s: Stream a) (x: a) (n: Nat): a := match n with
  | Zero => x
  | Succ m => s.at m

def Stream.consWalk (s: Stream a) (x: a) (n: Nat): Cells a := match n with
  | Zero => Done
  | Succ m => Cell x (u => s.walk m)

theorem Stream.consAgrees ∀ (s: Stream a) (x: a) (n: Nat): s.consWalk x n = Cells.fromAt (s.consAt x) 0 n :=
  match n with
    | Zero => byComputing
    | Succ m => rewrite s.agrees m then Eq.cong (r => Cell x (u => r)) (Cells.fromAtShift (s.consAt x) m 0).flipped

def Stream.cons (s: Stream a) (x: a): Stream a :=
  { at = s.consAt x, walk = s.consWalk x, agrees = Stream.consAgrees s x }

theorem consTail ∀ (s: Stream a) (x: a): (s.cons x).tail = s := byComputing

-- The bisimulation proof of the earlier note's Bisim.sw, unchanged, on this type.
def Related (f: a → a) (s t: Stream a): Prop := ∃ (y: a) => s = (Stream.iterate f y).map f ∧ t = Stream.iterate f (f y)

theorem Related.step ∀ (f: a → a) (s t: Stream a) (h: Related f s t): s.head = t.head ∧ Related f s.tail t.tail :=
  match h with
    | Witness y (Both hs ht) => rewrite hs, ht then Both byComputing (Witness (f y) (Both byComputing byComputing))

theorem mapIterateBisim ∀ (f: a → a) (x: a): (Stream.iterate f x).map f = Stream.iterate f (f x) :=
  Stream.bisim
    (Related f)
    (Related.step f)
    ((Stream.iterate f x).map f)
    (Stream.iterate f (f x))
    (Witness x (Both byComputing byComputing))
