--| `Stream a`: an infinite sequence of values, read one at a time with
--| `head` and `tail`, at any position with `at`, or the first few with
--| `take`. `Stream.iterate (* 2) 1` is 1, 2, 4, 8, …; its `tail` is
--| 2, 4, 8, … and `(Stream.iterate (* 2) 1).take 4` is `[1, 2, 4, 8]`.
--|
--| A loop that recurses on `s.tail`, reading `s.head` each time round, takes
--| time in proportion to how far it reads, as it would over a list. Two
--| streams with the same value at every position are equal
--| ([`Stream.ext`]), and [`Stream.bisim`] proves that from a relation kept by
--| `head` and `tail`. State facts about a stream through `at`: a law about
--| `tail` or `head` is proved by rewriting with [`Stream.tailAt`] and
--| [`Stream.headIs`], since `tail` of an unknown stream doesn't compute.
--|
--| How it is built (docs/proposals/streams-head-tail.md, §3.5): a stream is a
--| `Stream.Base`, which says what the values are and how to walk them, plus
--| a `Stream.Front`, where a reader has got to: the next few values as
--| `Stream.Cells`, ready to read. `tail` steps along those cells, and when
--| they run out walks again from where the reader started for twice the
--| distance, so n tails cost about 4n steps in all. The front sits behind a
--| quotient that relates every two fronts, so it adds speed and no
--| information. The only axiom is `Quot.sound`.

import Std (Eq)
import Stream.Cells (Done, Cell)

--| An infinite sequence of values (see this file's header): what the values
--| are (`base`), and where a reader has got to (`front`), which only makes
--| `tail` fast.
type Stream (a: Type) = {
  base: Stream.Base a,
  front: Quot (Stream.Front a (Stream.Base.at base)) Stream.Front.same
}

--| The stream of a base, with a reader at its start.
@[noReceiver]
def Stream.ofBase (s: Stream.Base a): Stream a := {
  base = s,
  front = Quot.mk { origin = s, offset = 0, cells = Done, shifted = n => byComputing, ok = Witness 0 byComputing }
}

--| The value at position `n`, counting from 0: `(Stream.iterate (* 2) 1).at 3`
--| is 8. It may take `n` steps or more each time, so to read many values in
--| order use `head` and `tail`, or `take`.
def Stream.at (s: Stream a) (n: Nat): a := s.base.at n

--| Any two fronts for the same values are equal.
theorem Stream.Front.allEqual ∀ (at: Nat → a) (x y: Quot (Stream.Front a at) Stream.Front.same): x = y :=
  Quot.ind
    [p := x' => x' = y]
    (fx => Quot.ind [p := y' => Quot.mk fx = y'] (fy => Quot.sound (byComputing: Stream.Front.same fx fy)) y)
    x

--| Two streams with equal bases are equal, whatever their fronts.
theorem Stream.sameBase ∀ (b c: Stream.Base a)
    (h: b = c)
    (x: Quot (Stream.Front a b.at) Stream.Front.same):
    ∀ (y: Quot (Stream.Front a c.at) Stream.Front.same) => ({ base = b, front = x }: Stream a)
      = { base = c, front = y } :=
  J
    (c' h' =>
      ∀ (y': Quot (Stream.Front a c'.at) Stream.Front.same) => ({ base = b, front = x }: Stream a)
        = { base = c', front = y' })
    (y' => Eq.cong (f => ({ base = b, front = f }: Stream a)) (Stream.Front.allEqual b.at x y'))
    h

--| Two streams with the same value at every position are equal.
theorem Stream.ext ∀ (s t: Stream a) (h: ∀ (n: Nat) => s.at n = t.at n): s = t :=
  Stream.sameBase s.base t.base (Stream.Base.ext s.base t.base h) s.front t.front

--| The first value: `(Stream.iterate (* 2) 1).head` is 1. One step, after
--| any number of `tail`s.
def Stream.head (s: Stream a): a :=
  Quot.lift
    (fr => Stream.Front.head fr)
    (x y same => (Stream.Front.headIs s.base.at x).trans (Stream.Front.headIs s.base.at y).flipped)
    s.front

--| The stream one step on from a front, built from the origin so that it
--| holds nothing of the stream before it.
def Stream.Front.step [at: Nat → a] (fr: Stream.Front a at): Stream a := {
  base = Stream.Base.drop fr.origin (fr.offset + 1),
  front = Quot.mk {
    origin = fr.origin,
    offset = fr.offset + 1,
    cells = Stream.Cells.tail (fr.cells.refill fr.origin fr.offset),
    shifted = n => byComputing,
    ok = Exists.elim fr.ok (m h => Stream.Front.nextOk fr.origin fr.offset fr.cells m h)
  }
}

--| A front's step reads the values from position 1.
theorem Stream.Front.stepAt ∀ (at: Nat → a) (fr: Stream.Front a at) (n: Nat): fr.step.at n = at (Succ n) :=
  (fr.shifted (Succ n)).flipped

--| Every value after the first: `(Stream.iterate (* 2) 1).tail` is 2, 4, 8,
--| …. One step on average: a loop that takes `n` tails in turn takes about
--| `4n` steps in all.
def Stream.tail (s: Stream a): Stream a :=
  Quot.lift
    (fr => fr.step)
    (x y same =>
      Stream.ext x.step y.step (n =>
        (Stream.Front.stepAt s.base.at x n).trans (Stream.Front.stepAt s.base.at y n).flipped))
    s.front

--| `head` is the value at position 0.
theorem Stream.headIs ∀ (s: Stream a): s.head = s.at 0 :=
  Quot.ind
    [p := f => Stream.head { base = s.base, front = f } = s.base.at 0]
    (fr => Stream.Front.headIs s.base.at fr)
    s.front

--| `tail` reads every value one position on. With [`Stream.headIs`], this
--| is how to prove a law about `head` and `tail`.
theorem Stream.tailAt ∀ (s: Stream a) (n: Nat): s.tail.at n = s.at (Succ n) :=
  Quot.ind
    [p := f => (Stream.tail { base = s.base, front = f }).at n = s.base.at (Succ n)]
    (fr => Stream.Front.stepAt s.base.at fr n)
    s.front

--| A relation `r` on streams whose related pairs have the same `head` and
--| related `tail`s relates streams equal at position `n`.
theorem Stream.bisimAt ∀ (r: Stream a → Stream a → Prop)
    (step: ∀ (s t: Stream a) => r s t → s.head = t.head ∧ r s.tail t.tail)
    (n: Nat) (s t: Stream a) (h: r s t):
    s.at n = t.at n :=
  match n with
    | Zero =>
      calc s.at 0
        _ = s.head := (Stream.headIs s).flipped
        _ = t.head := (step s t h).left
        _ = t.at 0 := Stream.headIs t
    | Succ m =>
      calc s.at (Succ m)
        _ = s.tail.at m := (Stream.tailAt s m).flipped
        _ = t.tail.at m := Stream.bisimAt r step m s.tail t.tail (step s t h).right
        _ = t.at (Succ m) := Stream.tailAt t m

--| Bisimulation: streams related by a relation whose related pairs have the
--| same `head` and related `tail`s are equal. To prove `s = t`, pick a
--| relation holding of `s` and `t` that `head` and `tail` keep.
theorem Stream.bisim ∀ (r: Stream a → Stream a → Prop)
    (step: ∀ (s t: Stream a) => r s t → s.head = t.head ∧ r s.tail t.tail)
    (s t: Stream a) (h: r s t):
    s = t :=
  Stream.ext s t (n => Stream.bisimAt r step n s t h)

--| The first `n` values, in `n` steps: `(Stream.iterate (+ 1) 0).take 3` is
--| `[0, 1, 2]`.
def Stream.take (s: Stream a) (n: Nat): List a := Stream.Cells.toList (s.base.walk n)

--| `x`, `f x`, `f (f x)`, …: `Stream.iterate (* 2) 1` is 1, 2, 4, 8, ….
@[noReceiver]
def Stream.iterate (f: a → a) (x: a): Stream a := Stream.ofBase (Stream.Base.iterate f x)

--| The tail of `x`, `f x`, … starts from `f x`.
theorem Stream.iterateTail ∀ (f: a → a) (x: a): (Stream.iterate f x).tail = Stream.iterate f (f x) :=
  Stream.ext (Stream.iterate f x).tail (Stream.iterate f (f x)) (n => byComputing)

--| The values `step` gives, starting from the state `start`: `step` returns
--| a value and the next state. `Stream.unfold (p => (p.fst, (p.snd, p.fst +
--| p.snd))) (0, 1)` is the Fibonacci numbers 0, 1, 1, 2, 3, 5, ….
@[noReceiver]
def Stream.unfold [s: Type] (step: s → Pair a s) (start: s): Stream a := Stream.ofBase (Stream.Base.unfold step start)

--| An unfold's first value is the one `step` gives from `start`.
theorem Stream.unfoldHead ∀ (s: Type) (step: s → Pair a s) (start: s):
    (Stream.unfold step start).head = (step start).fst :=
  byComputing

--| An unfold's tail is the unfold from the next state.
theorem Stream.unfoldTail ∀ (s: Type) (step: s → Pair a s) (start: s):
    (Stream.unfold step start).tail = Stream.unfold step (step start).snd :=
  Stream.ext (Stream.unfold step start).tail (Stream.unfold step (step start).snd) (n => byComputing)

--| `f` of each value: `(Stream.iterate (+ 1) 0).map (* 3)` is 0, 3, 6, ….
def Stream.map (s: Stream a) (f: a → b): Stream b := Stream.ofBase (Stream.Base.map s.base f)

--| Mapping, then taking the tail, is taking the tail, then mapping.
theorem Stream.mapTail ∀ (s: Stream a) (f: a → b): (s.map f).tail = s.tail.map f :=
  Stream.ext (s.map f).tail (s.tail.map f) (n => Eq.cong f (Stream.tailAt s n).flipped)

--| `x`, then the values of `s`: `Stream.cons 0 (Stream.iterate (* 2) 1)` is
--| 0, 1, 2, 4, ….
@[noReceiver]
def Stream.cons (x: a) (s: Stream a): Stream a := Stream.ofBase (Stream.Base.cons s.base x)

--| The first value of `Stream.cons x s` is `x`.
theorem Stream.consHead ∀ (x: a) (s: Stream a): (Stream.cons x s).head = x := byComputing

--| The tail of `Stream.cons x s` is `s`.
theorem Stream.consTail ∀ (x: a) (s: Stream a): (Stream.cons x s).tail = s :=
  Stream.ext (Stream.cons x s).tail s (n => byComputing)

--| `f` of each value, read at a position: `(s.map f).at n` is `f (s.at n)`.
theorem Stream.mapAt ∀ (s: Stream a) (f: a → b) (n: Nat): (s.map f).at n = f (s.at n) := byComputing

--| `Stream.iterate f x` at position `n` is `f` applied `n` times to `x`.
theorem Stream.iterateAt ∀ (f: a → a) (x: a) (n: Nat): (Stream.iterate f x).at n = Nat.iterate n f x := byComputing

--| `Stream.cons x s` at position 0 is `x`.
theorem Stream.consAtZero ∀ (x: a) (s: Stream a): (Stream.cons x s).at 0 = x := byComputing

--| `Stream.cons x s` at position `n + 1` is `s` at position `n`.
theorem Stream.consAtSucc ∀ (x: a) (s: Stream a) (n: Nat): (Stream.cons x s).at (Succ n) = s.at n := byComputing

--| The first `n` values are the walk's cells, read as a list of the values at positions 0, 1, ….
theorem Stream.takeCells ∀ (s: Stream a) (n: Nat): s.take n = (Stream.Cells.fromAt s.at 0 n).toList :=
  Eq.cong (c => c.toList) (s.base.agrees n)

--| No values taken is the empty list.
theorem Stream.takeZero ∀ (s: Stream a): s.take 0 = [] := Stream.takeCells s 0

--| One more value taken is the head, then the tail's values.
theorem Stream.takeSucc ∀ (s: Stream a) (n: Nat): s.take (Succ n) = [s.head, ..s.tail.take n] := calc s.take (Succ n)
  _ = (Stream.Cells.fromAt s.at 0 (Succ n)).toList := Stream.takeCells s (Succ n)
  _ = [s.at 0, ..(Stream.Cells.fromAt s.at 1 n).toList] := byComputing
  _ = [s.at 0, ..(Stream.Cells.fromAt (j => s.at (Succ j)) 0 n).toList] :=
    Eq.cong (c => [s.at 0, ..c.toList]) (Stream.Cells.fromAtShift s.at n 0)
  _ = [s.at 0, ..(Stream.Cells.fromAt s.tail.at 0 n).toList] :=
    Eq.cong
      (g => [s.at 0, ..(Stream.Cells.fromAt g 0 n).toList])
      (Quot.funext Nat (j => a) (j => s.at (Succ j)) s.tail.at (j => (Stream.tailAt s j).flipped))
  _ = [s.head, ..(Stream.Cells.fromAt s.tail.at 0 n).toList] :=
    Eq.cong (x => [x, ..(Stream.Cells.fromAt s.tail.at 0 n).toList]) (Stream.headIs s).flipped
  _ = [s.head, ..s.tail.take n] := Eq.cong (c => [s.head, ..c]) (Stream.takeCells s.tail n).flipped

--| The first `n + 1` values of an iterated stream are its seed, then the first `n` iterated from the next value.
theorem Stream.iterateTakeSucc ∀ (f: a → a) (x: a) (n: Nat):
    (Stream.iterate f x).take (Succ n) = [x, ..(Stream.iterate f (f x)).take n] :=
  byComputing

--| `Stream.iterate f x` at position `n + 1` is the stream iterated from `f x`, at position `n`. It does not compute `f`.
theorem Stream.iterateAtSucc ∀ (f: a → a) (x: a) (n: Nat):
    (Stream.iterate f x).at (Succ n) = (Stream.iterate f (f x)).at n :=
  byComputing

--| `take n` has `n` values.
theorem Stream.takeLength ∀ (s: Stream a) (n: Nat): (s.take n).length = n := match n with
  | Zero => Eq.cong (xs => xs.length) (Stream.takeZero s)
  | Succ k =>
    (Eq.cong (xs => xs.length) (Stream.takeSucc s k)).trans (Eq.cong (m => Succ m) (Stream.takeLength s.tail k))

--| The value at index `k` of the first `n` values, for `k < n`, is the value at position `k`.
theorem Stream.takeGet ∀ (s: Stream a) (n k: Nat) (h: k < n): (s.take n).get k = Some (s.at k) := match n, k with
  | Succ m, Zero => (Eq.cong (xs => xs.get 0) (Stream.takeSucc s m)).trans (Eq.cong (x => Some x) (Stream.headIs s))
  | Succ m, Succ j =>
    calc (s.take (Succ m)).get (Succ j)
      _ = (s.tail.take m).get j := Eq.cong (xs => xs.get (Succ j)) (Stream.takeSucc s m)
      _ = Some (s.tail.at j) := Stream.takeGet s.tail m j arithmetic
      _ = Some (s.at (Succ j)) := Eq.cong (x => Some x) (Stream.tailAt s j)

--| `s` with its first `n` values removed: `(Stream.iterate (+ 1) 0).drop 5` is 5, 6, 7, …. It takes `n` tails,
--| so about `4n` steps.
def Stream.drop (s: Stream a) (n: Nat): Stream a := Nat.iterate n Stream.tail s

--| `drop` by one more is `drop` of the tail.
theorem Stream.dropSucc ∀ (s: Stream a) (n: Nat): s.drop (Succ n) = s.tail.drop n := byComputing

--| Dropping `n` values from an iterated stream iterates from `f` applied `n` times to the seed. By induction on `n`,
--| for every seed, since each drop is a `tail`, which iterates from the next value.
theorem Stream.iterateDrop ∀ (f: a → a) (x: a) (n: Nat):
    (Stream.iterate f x).drop n = Stream.iterate f (Nat.iterate n f x) :=
  match n with
    | Zero => byComputing
    | Succ m =>
      calc (Stream.iterate f x).drop (Succ m)
        _ = (Stream.iterate f x).tail.drop m := Stream.dropSucc (Stream.iterate f x) m
        _ = (Stream.iterate f (f x)).drop m := Eq.cong (t => t.drop m) (Stream.iterateTail f x)
        _ = Stream.iterate f (Nat.iterate m f (f x)) := Stream.iterateDrop f (f x) m
        _ = Stream.iterate f (Nat.iterate (Succ m) f x) := byComputing

--| Dropping `n` values moves every position on by `n`.
theorem Stream.dropAt ∀ (s: Stream a) (n k: Nat): (s.drop n).at k = s.at (n + k) := match n with
  | Zero => byComputing
  | Succ m => (Stream.dropAt s.tail m k).trans (Stream.tailAt s (m + k))

--| The first value after dropping `n` is the value at position `n`.
theorem Stream.dropHead ∀ (s: Stream a) (n: Nat): (s.drop n).head = s.at n :=
  (Stream.headIs (s.drop n)).trans (Stream.dropAt s n 0)

--| One step of `Stream.cycle`: the next value of the list's elements still to come, or, with none left, the list's
--| first element and then its other elements to come.
@[noReceiver]
def Stream.cycleStep (xs: NonEmptyList a) (rest: List a): Pair a (List a) := match rest with
  | [] => (xs.head, xs.tail)
  | [y, ..ys] => (y, ys)

--| The list's elements in order, then again, forever: `(Stream.cycle [1, 2, 3]).take 7` is `[1, 2, 3, 1, 2, 3, 1]`.
--| Each value takes constant time, as it does for `iterate`: the state is the part of the list still to come.
@[noReceiver]
def Stream.cycle (xs: NonEmptyList a): Stream a := Stream.unfold (Stream.cycleStep xs) []

--| A cycle starts with the list's first element.
theorem Stream.cycleHead ∀ (xs: NonEmptyList a): (Stream.cycle xs).head = xs.head := byComputing

--| After the first element, a cycle goes on with the rest of the list.
theorem Stream.cycleTail ∀ (xs: NonEmptyList a): (Stream.cycle xs).tail = Stream.unfold (Stream.cycleStep xs) xs.tail :=
  Stream.unfoldTail _ _ _

--| After the elements still to come, an unfold of `cycleStep` is the cycle.
theorem Stream.cycleDropFrom ∀ (xs: NonEmptyList a) (rest: List a):
    (Stream.unfold (Stream.cycleStep xs) rest).drop rest.length = Stream.cycle xs :=
  match rest with
    | [] => byComputing
    | [y, ..ys] =>
      calc (Stream.unfold (Stream.cycleStep xs) [y, ..ys]).drop (Succ ys.length)
        _ = (Stream.unfold (Stream.cycleStep xs) [y, ..ys]).tail.drop ys.length :=
          Stream.dropSucc (Stream.unfold (Stream.cycleStep xs) [y, ..ys]) ys.length
        _ = (Stream.unfold (Stream.cycleStep xs) ys).drop ys.length :=
          Eq.cong (t => t.drop ys.length) (Stream.unfoldTail _ _ _)
        _ = Stream.cycle xs := Stream.cycleDropFrom xs ys

--| Dropping one lap of a cycle, as many values as the list has, leaves the cycle.
theorem Stream.cycleDrop ∀ (xs: NonEmptyList a): (Stream.cycle xs).drop xs.length = Stream.cycle xs :=
  calc (Stream.cycle xs).drop (Succ xs.tail.length)
    _ = (Stream.cycle xs).tail.drop xs.tail.length := Stream.dropSucc (Stream.cycle xs) xs.tail.length
    _ = (Stream.unfold (Stream.cycleStep xs) xs.tail).drop xs.tail.length :=
      Eq.cong (t => t.drop xs.tail.length) (Stream.cycleTail xs)
    _ = Stream.cycle xs := Stream.cycleDropFrom xs xs.tail

--| A lap on, a cycle has the same value: `at (xs.length + n)` is `at n`.
theorem Stream.cycleAtLap ∀ (xs: NonEmptyList a) (n: Nat):
    (Stream.cycle xs).at (xs.length + n) = (Stream.cycle xs).at n :=
  calc (Stream.cycle xs).at (xs.length + n)
    _ = ((Stream.cycle xs).drop xs.length).at n := (Stream.dropAt (Stream.cycle xs) xs.length n).flipped
    _ = (Stream.cycle xs).at n := Eq.cong (s => s.at n) (Stream.cycleDrop xs)

--| `q` laps on, a cycle has the same value. By induction on `q`, a lap at a time.
theorem Stream.cycleAtLaps ∀ (xs: NonEmptyList a) (q r: Nat):
    (Stream.cycle xs).at (q * xs.length + r) = (Stream.cycle xs).at r :=
  match q with
    | Zero => byComputing
    | Succ p =>
      calc (Stream.cycle xs).at (Succ p * xs.length + r)
        _ = (Stream.cycle xs).at (xs.length + (p * xs.length + r)) := Eq.cong (m => (Stream.cycle xs).at m) arithmetic
        _ = (Stream.cycle xs).at (p * xs.length + r) := Stream.cycleAtLap xs (p * xs.length + r)
        _ = (Stream.cycle xs).at r := Stream.cycleAtLaps xs p r

--| Within the elements still to come, an unfold of `cycleStep` has them in order.
theorem Stream.cycleStepGet ∀ (xs: NonEmptyList a) (rest: List a) (k: Nat)
    (h: k < rest.length):
    rest.get k = Some ((Stream.unfold (Stream.cycleStep xs) rest).at k) :=
  match rest, k with
    | [y, ..ys], Zero => byComputing
    | [y, ..ys], Succ j =>
      calc [y, ..ys].get (Succ j)
        _ = ys.get j := byComputing
        _ = Some ((Stream.unfold (Stream.cycleStep xs) ys).at j) := Stream.cycleStepGet xs ys j arithmetic
        _ = Some ((Stream.unfold (Stream.cycleStep xs) [y, ..ys]).tail.at j) :=
          Eq.cong (s => Some (s.at j)) (Stream.unfoldTail (List a) (Stream.cycleStep xs) [y, ..ys]).flipped
        _ = Some ((Stream.unfold (Stream.cycleStep xs) [y, ..ys]).at (Succ j)) :=
          Eq.cong (x => Some x) (Stream.tailAt (Stream.unfold (Stream.cycleStep xs) [y, ..ys]) j)

--| The values of the first lap are the list's elements.
theorem Stream.cycleAtLt ∀ (xs: NonEmptyList a) (k: Nat) (h: k < xs.length): xs.get k = Some ((Stream.cycle xs).at k) :=
  match k with
    | Zero => byComputing
    | Succ j =>
      calc xs.get (Succ j)
        _ = xs.tail.get j := byComputing
        _ = Some ((Stream.unfold (Stream.cycleStep xs) xs.tail).at j) := Stream.cycleStepGet xs xs.tail j arithmetic
        _ = Some ((Stream.cycle xs).tail.at j) := Eq.cong (s => Some (s.at j)) (Stream.cycleTail xs).flipped
        _ = Some ((Stream.cycle xs).at (Succ j)) := Eq.cong (x => Some x) (Stream.tailAt (Stream.cycle xs) j)

--| The value of a cycle at position `n` is the list's element at `n % xs.length`, which always exists.
theorem Stream.cycleAt ∀ (xs: NonEmptyList a) (n: Nat): xs.get (n % xs.length) = Some ((Stream.cycle xs).at n) :=
  calc xs.get (n % xs.length)
    _ = Some ((Stream.cycle xs).at (n % xs.length)) :=
      Stream.cycleAtLt xs (n % xs.length) (Nat.modLess n xs.length arithmetic)
    _ = Some ((Stream.cycle xs).at (n / xs.length * xs.length + n % xs.length)) :=
      Eq.cong (x => Some x) (Stream.cycleAtLaps xs (n / xs.length) (n % xs.length)).flipped
    _ = Some ((Stream.cycle xs).at n) := Eq.cong (m => Some ((Stream.cycle xs).at m)) (Nat.divModEq n xs.length).flipped

--| The left fold of the cells' values.
@[tailrec]
def Stream.Cells.foldLeft (c: Stream.Cells a) (init: b) (f: b → a → b): b := match c with
  | Done => init
  | Cell x rest => Stream.Cells.foldLeft (rest ()) (f init x) f

--| Folding the cells is folding their values as a list.
theorem Stream.Cells.foldLeftToList ∀ (c: Stream.Cells a) (init: b) (f: b → a → b):
    Stream.Cells.foldLeft c init f = (Stream.Cells.toList c).foldLeft init f :=
  match c with
    | Done => byComputing
    | Cell x rest => Stream.Cells.foldLeftToList (rest ()) (f init x) f

--| The first value among the cells that satisfies `p`.
@[tailrec]
def Stream.Cells.find (c: Stream.Cells a) (p: a → Bool): Option a := match c with
  | Done => None
  | Cell x rest => if p x then Some x else Stream.Cells.find (rest ()) p

--| Finding in the cells is finding in their values as a list.
theorem Stream.Cells.findToList ∀ (c: Stream.Cells a) (p: a → Bool):
    Stream.Cells.find c p = (Stream.Cells.toList c).find p :=
  match c with
    | Done => byComputing
    | Cell x rest =>
      calc Stream.Cells.find (Cell x rest) p
        _ = (if p x then Some x else Stream.Cells.find (rest ()) p) := byComputing
        _ = (if p x then Some x else (Stream.Cells.toList (rest ())).find p) :=
          Eq.cong (r => if p x then Some x else r) (Stream.Cells.findToList (rest ()) p)
        _ = (Stream.Cells.toList (Cell x rest)).find p := byComputing

--| The left fold of the first `n` values: `(Stream.iterate (+ 1) 1).fold 4 0 (+)` is 10. It reads the walk's cells
--| once, so it takes `n` steps and calls the stream's step `n` times.
def Stream.fold (s: Stream a) (n: Nat) (init: b) (f: b → a → b): b := Stream.Cells.foldLeft (s.base.walk n) init f

--| `fold` over the first `n` values is a fold of `take n`.
theorem Stream.foldTake ∀ (s: Stream a) (n: Nat) (init: b) (f: b → a → b):
    s.fold n init f = (s.take n).foldLeft init f :=
  Stream.Cells.foldLeftToList (s.base.walk n) init f

--| `fold` is a fold of the cells at positions 0, 1, ….
theorem Stream.foldAgrees ∀ (s: Stream a) (n: Nat) (init: b) (f: b → a → b):
    s.fold n init f = Stream.Cells.foldLeft (Stream.Cells.fromAt s.at 0 n) init f :=
  Eq.cong (c => Stream.Cells.foldLeft c init f) (s.base.agrees n)

--| Folding no values is the initial value.
theorem Stream.foldZero ∀ (s: Stream a) (init: b) (f: b → a → b): s.fold 0 init f = init :=
  (Stream.foldTake s 0 init f).trans (Eq.cong (xs => xs.foldLeft init f) (Stream.takeZero s))

--| One more value folded is the head folded in, then the tail's values.
theorem Stream.foldSucc ∀ (s: Stream a) (n: Nat) (init: b) (f: b → a → b):
    s.fold (Succ n) init f = s.tail.fold n (f init s.head) f :=
  calc s.fold (Succ n) init f
    _ = (s.take (Succ n)).foldLeft init f := Stream.foldTake s (Succ n) init f
    _ = [s.head, ..s.tail.take n].foldLeft init f := Eq.cong (xs => xs.foldLeft init f) (Stream.takeSucc s n)
    _ = (s.tail.take n).foldLeft (f init s.head) f := byComputing
    _ = s.tail.fold n (f init s.head) f := (Stream.foldTake s.tail n (f init s.head) f).flipped

--| The first of the first `n` values to satisfy `p`, or `None`: `(Stream.iterate (+ 1) 0).find 100 (n => n * n > 50)`
--| is `Some 8`. It reads the walk's cells once and stops at the first match.
def Stream.find (s: Stream a) (n: Nat) (p: a → Bool): Option a := Stream.Cells.find (s.base.walk n) p

--| `find` in the first `n` values is a `find` in `take n`.
theorem Stream.findTake ∀ (s: Stream a) (n: Nat) (p: a → Bool): s.find n p = (s.take n).find p :=
  Stream.Cells.findToList (s.base.walk n) p

--| The values of `f` at 0, 1, 2, …: `(Stream.fromFn (n => n * n)).take 4` is `[0, 1, 4, 9]`.
@[noReceiver]
def Stream.fromFn (f: Nat → a): Stream a := Stream.ofBase (Stream.Base.fromFn f)

--| `fromFn f` at position `n` is `f n`.
theorem Stream.fromFnAt ∀ (f: Nat → a) (n: Nat): (Stream.fromFn f).at n = f n := byComputing

--| The first value of `fromFn f` is `f 0`.
theorem Stream.fromFnHead ∀ (f: Nat → a): (Stream.fromFn f).head = f 0 := Stream.headIs (Stream.fromFn f)

--| The tail of `fromFn f` is `fromFn` of `f` one position on.
theorem Stream.fromFnTail ∀ (f: Nat → a): (Stream.fromFn f).tail = Stream.fromFn (n => f (Succ n)) :=
  Stream.ext (Stream.fromFn f).tail (Stream.fromFn (n => f (Succ n))) (n => byComputing)

--| `x` forever: `(Stream.repeat 7).take 3` is `[7, 7, 7]`.
@[noReceiver]
def Stream.repeat (x: a): Stream a := Stream.fromFn (n => x)

--| Every value of `Stream.repeat x` is `x`.
theorem Stream.repeatAt ∀ (x: a) (n: Nat): (Stream.repeat x).at n = x := byComputing

--| The first value of `Stream.repeat x` is `x`.
theorem Stream.repeatHead ∀ (x: a): (Stream.repeat x).head = x := Stream.headIs (Stream.repeat x)

--| The tail of `Stream.repeat x` is `Stream.repeat x`.
theorem Stream.repeatTail ∀ (x: a): (Stream.repeat x).tail = Stream.repeat x :=
  Stream.ext (Stream.repeat x).tail (Stream.repeat x) (n => byComputing)

--| `f` of the values of `s` and `t` in step: `(Stream.iterate (+ 1) 0).zipWith (Stream.iterate (* 2) 1) (+)` is 1, 3,
--| 6, 11, ….
def Stream.zipWith (s: Stream a) (t: Stream b) (f: a → b → c): Stream c :=
  Stream.unfold (st => (f (Stream.head st.fst) (Stream.head st.snd), (Stream.tail st.fst, Stream.tail st.snd))) (s, t)

--| The first value of `zipWith` is `f` of the first values.
theorem Stream.zipWithHead ∀ (s: Stream a) (t: Stream b) (f: a → b → c): (s.zipWith t f).head = f s.head t.head :=
  byComputing

--| The tail of `zipWith` is `zipWith` of the tails.
theorem Stream.zipWithTail ∀ (s: Stream a) (t: Stream b) (f: a → b → c):
    (s.zipWith t f).tail = s.tail.zipWith t.tail f :=
  Stream.unfoldTail _ _ _

--| `zipWith` at position `n` is `f` of the values at position `n`.
theorem Stream.zipWithAt ∀ (s: Stream a) (t: Stream b) (f: a → b → c) (n: Nat):
    (s.zipWith t f).at n = f (s.at n) (t.at n) :=
  match n with
    | Zero =>
      calc (s.zipWith t f).at 0
        _ = (s.zipWith t f).head := (Stream.headIs (s.zipWith t f)).flipped
        _ = f s.head t.head := Stream.zipWithHead s t f
        _ = f (s.at 0) (t.at 0) := Eq.cong2 f (Stream.headIs s) (Stream.headIs t)
    | Succ m =>
      calc (s.zipWith t f).at (Succ m)
        _ = (s.zipWith t f).tail.at m := (Stream.tailAt (s.zipWith t f) m).flipped
        _ = (s.tail.zipWith t.tail f).at m := Eq.cong (r => r.at m) (Stream.zipWithTail s t f)
        _ = f (s.tail.at m) (t.tail.at m) := Stream.zipWithAt s.tail t.tail f m
        _ = f (s.at (Succ m)) (t.at (Succ m)) := Eq.cong2 f (Stream.tailAt s m) (Stream.tailAt t m)

--| The values of `s` and `t` alternately: `Stream.interleave (Stream.repeat 0) (Stream.repeat 1)` is 0, 1, 0, 1, ….
--| Its state is the stream to read next and the other one, so the tail is the interleave the other way round.
def Stream.interleave (s t: Stream a): Stream a :=
  Stream.unfold (st => (Stream.head st.fst, (st.snd, Stream.tail st.fst))) (s, t)

--| The first value of `interleave s t` is the first of `s`.
theorem Stream.interleaveHead ∀ (s t: Stream a): (Stream.interleave s t).head = s.head := byComputing

--| The tail of `interleave s t` is `t` interleaved with the tail of `s`.
theorem Stream.interleaveTail ∀ (s t: Stream a): (Stream.interleave s t).tail = Stream.interleave t s.tail :=
  Stream.unfoldTail _ _ _

--| `interleave` at an even position `2 * n` is `s` at position `n`.
theorem Stream.interleaveAtEven ∀ (s t: Stream a) (n: Nat): (Stream.interleave s t).at (2 * n) = s.at n := match n with
  | Zero =>
    calc (Stream.interleave s t).at 0
      _ = (Stream.interleave s t).head := (Stream.headIs (Stream.interleave s t)).flipped
      _ = s.head := Stream.interleaveHead s t
      _ = s.at 0 := Stream.headIs s
  | Succ m =>
    calc (Stream.interleave s t).at (2 * Succ m)
      _ = (Stream.interleave s t).tail.tail.at (2 * m) :=
        ((Stream.tailAt (Stream.interleave s t).tail (2 * m)).trans
          (Stream.tailAt (Stream.interleave s t) (Succ (2 * m)))).flipped
      _ = (Stream.interleave s.tail t.tail).at (2 * m) :=
        Eq.cong
          (r => r.at (2 * m))
          ((Eq.cong (r => r.tail) (Stream.interleaveTail s t)).trans (Stream.interleaveTail t s.tail))
      _ = s.tail.at m := Stream.interleaveAtEven s.tail t.tail m
      _ = s.at (Succ m) := Stream.tailAt s m

--| `interleave` at an odd position `2 * n + 1` is `t` at position `n`.
theorem Stream.interleaveAtOdd ∀ (s t: Stream a) (n: Nat): (Stream.interleave s t).at (2 * n + 1) = t.at n :=
  calc (Stream.interleave s t).at (2 * n + 1)
    _ = (Stream.interleave s t).tail.at (2 * n) := (Stream.tailAt (Stream.interleave s t) (2 * n)).flipped
    _ = (Stream.interleave t s.tail).at (2 * n) := Eq.cong (r => r.at (2 * n)) (Stream.interleaveTail s t)
    _ = t.at n := Stream.interleaveAtEven t s.tail n

--| The running folds of `s`, the initial value first: `(Stream.iterate (+ 1) 1).scan 0 (+)` is 0, 1, 3, 6, 10, ….
def Stream.scan (s: Stream a) (init: b) (f: b → a → b): Stream b :=
  Stream.unfold (st => (st.fst, (f st.fst (Stream.head st.snd), Stream.tail st.snd))) (init, s)

--| The first value of `scan` is the initial value.
theorem Stream.scanHead ∀ (s: Stream a) (init: b) (f: b → a → b): (s.scan init f).head = init := byComputing

--| The tail of `scan` is the `scan` of the tail, from the initial value folded with the first value.
theorem Stream.scanTail ∀ (s: Stream a) (init: b) (f: b → a → b):
    (s.scan init f).tail = s.tail.scan (f init s.head) f :=
  Stream.unfoldTail _ _ _

--| `scan` at position `n` is the fold of the first `n` values.
theorem Stream.scanAt ∀ (s: Stream a) (init: b) (f: b → a → b) (n: Nat): (s.scan init f).at n = s.fold n init f :=
  match n with
    | Zero => (Stream.foldZero s init f).flipped
    | Succ m =>
      calc (s.scan init f).at (Succ m)
        _ = (s.scan init f).tail.at m := (Stream.tailAt (s.scan init f) m).flipped
        _ = (s.tail.scan (f init s.head) f).at m := Eq.cong (r => r.at m) (Stream.scanTail s init f)
        _ = s.tail.fold m (f init s.head) f := Stream.scanAt s.tail (f init s.head) f m
        _ = s.fold (Succ m) init f := (Stream.foldSucc s m init f).flipped

--| Streams that are functions of a shared seed, with equal heads and tails that are again those functions of
--| some seed, are equal: `u x = v x` for every `x`. The relation `bisim` uses is "are `u z` and `v z` for some `z`".
theorem Stream.bisimOn ∀ (u v: x → Stream a)
    (heads: ∀ (seed: x) => (u seed).head = (v seed).head)
    (tails: ∀ (seed: x) => ∃ (later: x) => (u seed).tail = u later ∧ (v seed).tail = v later) (seed: x):
    u seed = v seed :=
  Stream.bisim
    (s t => ∃ (z: x) => s = u z ∧ t = v z)
    (s t related =>
      Exists.elim related (z e =>
        Both
          (calc s.head
            _ = (u z).head := Eq.cong (r => r.head) e.left
            _ = (v z).head := heads z
            _ = t.head := Eq.cong (r => r.head) e.right.flipped)
          (Exists.elim (tails z) (later g =>
            Witness later
              (Both ((Eq.cong (r => r.tail) e.left).trans g.left) ((Eq.cong (r => r.tail) e.right).trans g.right))))))
    (u seed)
    (v seed)
    (Witness seed (Both byComputing byComputing))

--| `Stream.unfold step` is the only function `h` from states to streams whose head is what `step` gives and whose
--| tail is `h` of the next state.
theorem Stream.unfoldUnique ∀ (s: Type) (step: s → Pair a s) (h: s → Stream a)
    (heads: ∀ (state: s) => (h state).head = (step state).fst)
    (tails: ∀ (state: s) => (h state).tail = h (step state).snd) (start: s):
    h start = Stream.unfold step start :=
  Stream.bisimOn h
    (Stream.unfold step)
    (state => (heads state).trans (Stream.unfoldHead s step state).flipped)
    (state => Witness (step state).snd (Both (tails state) (Stream.unfoldTail s step state)))
    start

--| The first position, counting from `i`, of a value satisfying `p`.
@[tailrec]
def Stream.Cells.findIndex (c: Stream.Cells a) (i: Nat) (p: a → Bool): Option Nat := match c with
  | Done => None
  | Cell x rest => if p x then Some i else Stream.Cells.findIndex (rest ()) (i + 1) p

--| A position found in the cells of `g` from `i` is at least `i`, within the `n` cells, holds a value satisfying `p`,
--| and no position between `i` and it does.
theorem Stream.Cells.findIndexSome ∀ (g: Nat → a) (p: a → Bool) (n i k: Nat):
    Stream.Cells.findIndex (Stream.Cells.fromAt g i n) i p = Some k
      → i ≤ k ∧ k < i + n ∧ p (g k) ∧ ∀ (j: Nat) => i ≤ j → j < k → p (g j) = False :=
  match n with
    | Zero => found => (Option.noneNotSome k found).impossible
    | Succ m =>
      match e: p (g i) with
        | True => found =>
          (let ik: i = k := Option.someInjective found;
           rewrite <- ik then
             Both arithmetic
               (Both arithmetic (Both e (j h1 h2 => Void.impossible (Nat.lessIrrefl i (arithmetic: i < i))))))
        | False => found =>
          (let r := Stream.Cells.findIndexSome g p m (Succ i) k found;
           Both arithmetic
             (Both arithmetic
               (Both r.right.right.left (j h1 h2 =>
                 if h: j = i then (rewrite h then e) else r.right.right.right j arithmetic h2))))

--| No position among the `n` cells of `g` from `i` has a value satisfying `p` when none is found.
theorem Stream.Cells.findIndexNone ∀ (g: Nat → a) (p: a → Bool) (n i: Nat):
    Stream.Cells.findIndex (Stream.Cells.fromAt g i n) i p = None → ∀ (j: Nat) => i ≤ j → j < i + n → p (g j) = False :=
  match n with
    | Zero => found => (j h1 h2 => Void.impossible (Nat.lessIrrefl i (arithmetic: i < i)))
    | Succ m =>
      match e: p (g i) with
        | True => found => (Option.noneNotSome i found.flipped).impossible
        | False => found =>
          (j h1 h2 =>
            if h: j = i then (rewrite h then e)
            else Stream.Cells.findIndexNone g p m (Succ i) found j arithmetic arithmetic)

--| The first position below `n` whose value satisfies `p`, or `None`:
--| `(Stream.iterate (+ 1) 0).findIndex 100 (x => x * x > 50)` is `Some 8`. It reads the walk's cells once and stops at
--| the first match.
def Stream.findIndex (s: Stream a) (n: Nat) (p: a → Bool): Option Nat := Stream.Cells.findIndex (s.base.walk n) 0 p

--| A position found is below the limit, holds a value satisfying `p`, and no earlier position does.
theorem Stream.findIndexSome ∀ (s: Stream a) (n k: Nat) (p: a → Bool):
    s.findIndex n p = Some k → k < n ∧ p (s.at k) = True ∧ ∀ (j: Nat) => j < k → p (s.at j) = False :=
  found =>
    (let r := Stream.Cells.findIndexSome s.at p n 0 k
       ((Eq.cong (c => Stream.Cells.findIndex c 0 p) (s.base.agrees n)).flipped.trans found);
     Both (arithmetic: k < n) (Both r.right.right.left (j h => r.right.right.right j arithmetic h)))

--| When none is found, no position below the limit holds a value satisfying `p`.
theorem Stream.findIndexNone ∀ (s: Stream a) (n: Nat) (p: a → Bool):
    s.findIndex n p = None → ∀ (j: Nat) => j < n → p (s.at j) = False :=
  found =>
    (j h =>
      Stream.Cells.findIndexNone s.at p n 0
        ((Eq.cong (c => Stream.Cells.findIndex c 0 p) (s.base.agrees n)).flipped.trans found)
        j
        arithmetic
        arithmetic)

--| Counting from one more position finds one more.
theorem Stream.Cells.findIndexShift ∀ (g: Nat → a) (p: a → Bool) (n j i: Nat):
    Stream.Cells.findIndex (Stream.Cells.fromAt g j n) (i + 1) p
      = (Stream.Cells.findIndex (Stream.Cells.fromAt g j n) i p).map (k => k + 1) :=
  match n with
    | Zero => byComputing
    | Succ m =>
      match e: p (g j) with
        | True => byComputing
        | False => Stream.Cells.findIndexShift g p m (j + 1) (i + 1)

--| `findIndex` with one more position of limit is 0 if the head satisfies `p`, and otherwise one more than the tail's.
theorem Stream.findIndexSucc ∀ (s: Stream a) (n: Nat) (p: a → Bool):
    s.findIndex (Succ n) p = if p s.head then Some 0 else (s.tail.findIndex n p).map (j => j + 1) :=
  calc s.findIndex (Succ n) p
    _ = Stream.Cells.findIndex (Stream.Cells.fromAt s.at 0 (Succ n)) 0 p :=
      Eq.cong (c => Stream.Cells.findIndex c 0 p) (s.base.agrees (Succ n))
    _ = (if p (s.at 0) then Some 0 else Stream.Cells.findIndex (Stream.Cells.fromAt s.at 1 n) 1 p) := byComputing
    _ = (if p (s.at 0) then Some 0 else (Stream.Cells.findIndex (Stream.Cells.fromAt s.at 1 n) 0 p).map (k => k + 1)) :=
      Eq.cong (r => if p (s.at 0) then Some 0 else r) (Stream.Cells.findIndexShift s.at p n 1 0)
    _ = (if p (s.at 0) then Some 0
         else (Stream.Cells.findIndex (Stream.Cells.fromAt (j => s.at (Succ j)) 0 n) 0 p).map (k => k + 1)) :=
      Eq.cong
        (c => if p (s.at 0) then Some 0 else (Stream.Cells.findIndex c 0 p).map (k => k + 1))
        (Stream.Cells.fromAtShift s.at n 0)
    _ = (if p (s.at 0) then Some 0
         else (Stream.Cells.findIndex (Stream.Cells.fromAt s.tail.at 0 n) 0 p).map (k => k + 1)) :=
      Eq.cong
        (g => if p (s.at 0) then Some 0 else (Stream.Cells.findIndex (Stream.Cells.fromAt g 0 n) 0 p).map (k => k + 1))
        (Quot.funext Nat (j => a) (j => s.at (Succ j)) s.tail.at (j => (Stream.tailAt s j).flipped))
    _ = (if p s.head then Some 0 else (s.tail.findIndex n p).map (k => k + 1)) :=
      rewrite Stream.headIs s then
        Eq.cong
          (c => if p (s.at 0) then Some 0 else (Stream.Cells.findIndex c 0 p).map (k => k + 1))
          (s.tail.base.agrees n).flipped

--| The first position below `n + 1` of an iterated stream whose value satisfies `p` is 0 if the seed does, and
--| otherwise one more than the first position below `n` of the stream iterated from the next value.
theorem Stream.iterateFindIndexSucc ∀ (f: a → a) (x: a) (n: Nat) (p: a → Bool):
    (Stream.iterate f x).findIndex (Succ n) p
      = if p x then Some 0 else ((Stream.iterate f (f x)).findIndex n p).map (j => j + 1) :=
  calc (Stream.iterate f x).findIndex (Succ n) p
    _ = (if p (Stream.iterate f x).head then Some 0 else ((Stream.iterate f x).tail.findIndex n p).map (j => j + 1)) :=
      Stream.findIndexSucc (Stream.iterate f x) n p
    _ = (if p x then Some 0 else ((Stream.iterate f (f x)).findIndex n p).map (j => j + 1)) :=
      rewrite Stream.iterateTail f x

--| The cells' fold until the accumulator satisfies `stop`, from position `i`: the accumulator and the position
--| it stopped at.
@[tailrec]
def Stream.Cells.foldUntil (c: Stream.Cells a) (i: Nat) (acc: b) (f: b → a → b) (stop: b → Bool): (b, Nat) :=
  match c with
    | Done => (acc, i)
    | Cell x rest => if stop acc then (acc, i) else Stream.Cells.foldUntil (rest ()) (i + 1) (f acc x) f stop

--| `foldUntil` over `n` cells of `g` from `j` is a fold of some `m ≤ n` of them, which stopped there: it read all
--| `n` or `stop` held.
theorem Stream.Cells.foldUntilFromAt ∀ (g: Nat → a) (n j i: Nat) (acc: b) (f: b → a → b) (stop: b → Bool):
    ∃ (m: Nat) => m ≤ n
      ∧ Stream.Cells.foldUntil (Stream.Cells.fromAt g j n) i acc f stop
        = (Stream.Cells.foldLeft (Stream.Cells.fromAt g j m) acc f, i + m)
      ∧ (m < n → stop (Stream.Cells.foldLeft (Stream.Cells.fromAt g j m) acc f)) :=
  match n with
    | Zero => Witness 0 (Both arithmetic (Both byComputing (h => (Nat.lessIrrefl 0 h).impossible)))
    | Succ k =>
      match e: stop acc with
        | True => Witness 0 (Both arithmetic (Both byComputing (h => e)))
        | False => Exists.elim (Stream.Cells.foldUntilFromAt g k (Succ j) (i + 1) (f acc (g j)) f stop) (m h =>
          Witness
            (Succ m)
            (Both arithmetic
              (Both
                (rewrite h.right.left then
                  Eq.cong
                    (x => (Stream.Cells.foldLeft (Stream.Cells.fromAt g j (Succ m)) acc f, x))
                    (arithmetic: i + 1 + m = i + Succ m))
                (d => h.right.right arithmetic))))

--| Fold the first values with `f` until the accumulator satisfies `stop` or `n` values are read, and give the
--| accumulator and how many values were folded: `(Stream.iterate (+ 1) 1).foldUntil 100 0 (+) (total => total > 20)` is
--| `(21, 6)`. It reads the walk's cells once.
def Stream.foldUntil (s: Stream a) (n: Nat) (init: b) (f: b → a → b) (stop: b → Bool): (b, Nat) :=
  Stream.Cells.foldUntil (s.base.walk n) 0 init f stop

--| `foldUntil` is a `fold` over some number of the first values, at most `n`, and it stopped there: it read all `n` or
--| `stop` held.
theorem Stream.foldUntilFold ∀ (s: Stream a) (n: Nat) (init: b) (f: b → a → b) (stop: b → Bool):
    ∃ (m: Nat) => m ≤ n ∧ s.foldUntil n init f stop = (s.fold m init f, m) ∧ (m < n → stop (s.fold m init f)) :=
  Exists.elim (Stream.Cells.foldUntilFromAt s.at n 0 0 init f stop) (m h =>
    Witness m
      (Both h.left
        (Both
          (calc s.foldUntil n init f stop
            _ = Stream.Cells.foldUntil (Stream.Cells.fromAt s.at 0 n) 0 init f stop :=
              Eq.cong (c => Stream.Cells.foldUntil c 0 init f stop) (s.base.agrees n)
            _ = (Stream.Cells.foldLeft (Stream.Cells.fromAt s.at 0 m) init f, 0 + m) := h.right.left
            _ = (s.fold m init f, m) :=
              Eq.cong2 (x y => (x, y)) (Stream.foldAgrees s m init f).flipped (arithmetic: 0 + m = m))
          (d => rewrite Stream.foldAgrees s m init f then h.right.right d))))

--| A repeat in a stream: the value, the position it was first at, and the position it is at again.
type Stream.Repeat (a: Type) = { value: a, first: Nat, again: Nat }

--| The first value among the cells that is one seen before, as the repeat: the value, the position it was first at and
--| the position of the repeat. `i` is the position of the first cell, and `seen` maps each value met so far to the
--| position it was first at.
@[tailrec]
def Stream.Cells.findRepeat [auto ord: Ord a] (c: Stream.Cells a) (i: Nat) (seen: Map a Nat):
    Option (Stream.Repeat a) :=
  match c with
    | Done => None
    | Cell x rest =>
      match Map.get seen x with
        | Some j => Some { value = x, first = j, again = i }
        | None => Stream.Cells.findRepeat (rest ()) (i + 1) (Map.insert seen x i)

--| What a seen-map keeps true when `x`, the value at position `i`, is added at `i`: every value in it is at its position.
theorem Stream.seenInsert ∀ [auto ord: Ord a] (g: Nat → a) (i: Nat) (x: a) (seen: Map a Nat)
    (here: g i = x)
    (inv: ∀ (y: a) (j: Nat) => Map.get seen y = Some j → j < i ∧ g j = y)
    (y: a) (j: Nat)
    (got: Map.get (Map.insert seen x i) y = Some j):
    j < i + 1 ∧ g j = y :=
  if h: y = x then
    (rewrite h at got then
      (rewrite h then
        (rewrite Map.getInsert x i seen at got then (rewrite <- Option.someInjective got then Both arithmetic here))))
  else (rewrite Map.getInsertOther x i y h seen at got then (let r := inv y j got; Both arithmetic r.right))

--| What the seen-map of `findRepeat` holds before position `i`: each value in it is at the position it maps to, which
--| is its first; every value at a position below `i` is in it; and no two positions below `i` hold the same value.
def Stream.SeenOk [auto ord: Ord a] (g: Nat → a) (i: Nat) (seen: Map a Nat): Prop :=
  (∀ (y: a) (j: Nat) => Map.get seen y = Some j → j < i ∧ g j = y)
    ∧ (∀ (y: a) (j: Nat) => Map.get seen y = Some j → ∀ (k: Nat) => k < j → g k ≠ y)
    ∧ (∀ (k: Nat) => k < i → ∃ (m: Nat) => Map.get seen (g k) = Some m)
    ∧ (∀ (x y: Nat) => x < y → y < i → g x ≠ g y)

--| The empty map is `SeenOk` before position 0.
theorem Stream.seenOkEmpty ∀ [auto ord: Ord a] (g: Nat → a): Stream.SeenOk g 0 Map.empty :=
  Both
    (y j got => (Option.noneNotSome j ((Map.getEmpty y).flipped.trans got)).impossible)
    (Both
      (y j got => (Option.noneNotSome j ((Map.getEmpty y).flipped.trans got)).impossible)
      (Both (k h => (Nat.lessIrrefl 0 arithmetic).impossible) (x y h1 h2 => (Nat.lessIrrefl 0 arithmetic).impossible)))

--| Adding the value at position `i`, which the map lacks, keeps `SeenOk`, now before `i + 1`.
theorem Stream.seenOkInsert ∀ [auto ord: Ord a] (g: Nat → a) (i: Nat) (seen: Map a Nat)
    (ok: Stream.SeenOk g i seen)
    (miss: Map.get seen (g i) = None):
    Stream.SeenOk g (i + 1) (Map.insert seen (g i) i) :=
  Both
    (Stream.seenInsert g i (g i) seen byComputing ok.left)
    (Both
      (y j got k hk =>
        if h: y = g i then
          (rewrite h at got then
            (rewrite Map.getInsert (g i) i seen at got then
              (rewrite <- Option.someInjective got at hk then
                (h2 =>
                  (let c := ok.right.right.left k hk;
                   Exists.elim c (m cm =>
                     Option.noneNotSome m
                       (miss.flipped.trans (rewrite h at h2 then (rewrite h2 at cm then cm))))).impossible))))
        else (rewrite Map.getInsertOther (g i) i y h seen at got then ok.right.left y j got k hk))
      (Both
        (k hk =>
          if h: g k = g i then (rewrite h then Witness i (Map.getInsert (g i) i seen))
          else
            Exists.elim (ok.right.right.left k (if hh: k = i then (h (rewrite hh)).impossible else arithmetic)) (m cm =>
              Witness m ((Map.getInsertOther (g i) i (g k) h seen).trans cm)))
        (x y hxy hy h2 =>
          if h: y = i then
            (let hx: x < i := arithmetic;
             Exists.elim (ok.right.right.left x hx) (m cm =>
               Option.noneNotSome m (miss.flipped.trans (rewrite h at h2 then (rewrite h2 at cm then cm)))))
          else ok.right.right.right x y hxy arithmetic h2)))

--| A repeat found among the `n` cells of `g` from position `i` is a first position before the second, which is within the
--| `n` cells, holding the same value; no two positions before the second hold the same value, and no position before the
--| first holds it; and the repeat's value is the one at the second position. `seen` is `SeenOk`. By induction on `n`: a hit in the map is `SeenOk`'s facts at the head; a miss
--| adds the head and goes on.
theorem Stream.Cells.findRepeatSome ∀ [auto ord: Ord a] (g: Nat → a) (n i: Nat) (seen: Map a Nat)
    (ok: Stream.SeenOk g i seen) (r: Stream.Repeat a):
    Stream.Cells.findRepeat (Stream.Cells.fromAt g i n) i seen = Some r
      → r.first < r.again
        ∧ r.again < i + n
        ∧ g r.first = g r.again
        ∧ (∀ (x y: Nat) => x < y → y < r.again → g x ≠ g y)
        ∧ (∀ (k: Nat) => k < r.first → g k ≠ g r.again)
        ∧ r.value = g r.again :=
  match n with
    | Zero => found => (Option.noneNotSome r found).impossible
    | Succ k =>
      match e: Map.get seen (g i) with
        | Some j => found =>
          (let h := ok.left (g i) j e;
           rewrite <- Option.someInjective found then
             Both h.left
               (Both arithmetic
                 (Both h.right (Both ok.right.right.right (Both (ok.right.left (g i) j e) byComputing)))))
        | None => found =>
          (let h := Stream.Cells.findRepeatSome g k
             (i + 1)
             (Map.insert seen (g i) i)
             (Stream.seenOkInsert g i seen ok e)
             r
             found;
           Both h.left (Both arithmetic h.right.right))

--| When no repeat is found among the `n` cells of `g` from position `i`, no two positions below `i + n` hold the same
--| value. `seen` is `SeenOk`.
theorem Stream.Cells.findRepeatNone ∀ [auto ord: Ord a] (g: Nat → a) (n i: Nat) (seen: Map a Nat)
    (ok: Stream.SeenOk g i seen):
    Stream.Cells.findRepeat (Stream.Cells.fromAt g i n) i seen = None → ∀ (x y: Nat) => x < y → y < i + n → g x ≠ g y :=
  match n with
    | Zero => found => (x y h1 h2 => ok.right.right.right x y h1 arithmetic)
    | Succ k =>
      match e: Map.get seen (g i) with
        | Some j => found => (Option.noneNotSome { value = g i, first = j, again = i } found.flipped).impossible
        | None => found =>
          (x y h1 h2 =>
            Stream.Cells.findRepeatNone g k
              (i + 1)
              (Map.insert seen (g i) i)
              (Stream.seenOkInsert g i seen ok e)
              found
              x
              y
              h1
              arithmetic)

--| The first repeated value among the first `n` values, as the value and the position it was first at and the position it
--| repeats at, or `None`: `(Stream.iterate (n => (n * n + 1) % 7) 0).findRepeat 100` is
--| `Some { value = 5, first = 3, again = 4 }`. It reads the
--| walk's cells once and remembers the values seen in a `Map`, so it takes about `n` steps, each a map lookup.
def Stream.findRepeat [auto ord: Ord a] (s: Stream a) (n: Nat): Option (Stream.Repeat a) :=
  Stream.Cells.findRepeat (s.base.walk n) 0 Map.empty

--| A repeat found in the first `n` values: the first position is before the second, which is within the `n`, and the
--| two positions hold the same value, which is the repeat's value. It is the first repeat: no two positions before the
--| second hold the same value, and no position before the first holds that value.
theorem Stream.findRepeatSome ∀ [auto ord: Ord a] (s: Stream a) (n: Nat) (r: Stream.Repeat a):
    s.findRepeat n = Some r
      → r.first < r.again
        ∧ r.again < n
        ∧ s.at r.first = s.at r.again
        ∧ (∀ (x y: Nat) => x < y → y < r.again → s.at x ≠ s.at y)
        ∧ (∀ (k: Nat) => k < r.first → s.at k ≠ s.at r.again)
        ∧ r.value = s.at r.again :=
  found =>
    (let h := Stream.Cells.findRepeatSome s.at n 0 Map.empty
       (Stream.seenOkEmpty s.at)
       r
       ((Eq.cong (c => Stream.Cells.findRepeat c 0 Map.empty) (s.base.agrees n)).flipped.trans found);
     Both h.left (Both (arithmetic: r.again < n) h.right.right))

--| When no repeat is found in the first `n` values, no two of those positions hold the same value.
theorem Stream.findRepeatNone ∀ [auto ord: Ord a] (s: Stream a) (n: Nat):
    s.findRepeat n = None → ∀ (x y: Nat) => x < y → y < n → s.at x ≠ s.at y :=
  found =>
    (x y h1 h2 =>
      Stream.Cells.findRepeatNone s.at n 0 Map.empty
        (Stream.seenOkEmpty s.at)
        ((Eq.cong (c => Stream.Cells.findRepeat c 0 Map.empty) (s.base.agrees n)).flipped.trans found)
        x
        y
        h1
        arithmetic)

--| Steps that agree everywhere give the same stream.
theorem Stream.iterateCongr ∀ (f g: a → a) (h: ∀ (x: a) => f x = g x) (x: a): Stream.iterate f x = Stream.iterate g x :=
  Eq.cong (r => Stream.iterate r x) (Quot.funext a (y => a) f g h)
