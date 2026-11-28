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
import Stream.Cells (Done)

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
    (fr => fr.head)
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
def Stream.take (s: Stream a) (n: Nat): List a := (s.base.walk n).toList

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
def Stream.map (s: Stream a) (f: a → b): Stream b := Stream.ofBase (s.base.map f)

--| Mapping, then taking the tail, is taking the tail, then mapping.
theorem Stream.mapTail ∀ (s: Stream a) (f: a → b): (s.map f).tail = s.tail.map f :=
  Stream.ext (s.map f).tail (s.tail.map f) (n => Eq.cong f (Stream.tailAt s n).flipped)

--| `x`, then the values of `s`: `Stream.cons 0 (Stream.iterate (* 2) 1)` is
--| 0, 1, 2, 4, ….
@[noReceiver]
def Stream.cons (x: a) (s: Stream a): Stream a := Stream.ofBase (s.base.cons x)

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

--| Dropping `n` values moves every position on by `n`.
theorem Stream.dropAt ∀ (s: Stream a) (n k: Nat): (s.drop n).at k = s.at (n + k) := match n with
  | Zero => byComputing
  | Succ m => (Stream.dropAt s.tail m k).trans (Stream.tailAt s (m + k))

--| The first value after dropping `n` is the value at position `n`.
theorem Stream.dropHead ∀ (s: Stream a) (n: Nat): (s.drop n).head = s.at n :=
  (Stream.headIs (s.drop n)).trans (Stream.dropAt s n 0)

--| The left fold of the first `n` values: `(Stream.iterate (+ 1) 1).fold 4 0 (+)` is 10. It reads by `head` and
--| `tail`, so it takes `n` steps.
@[tailrec]
def Stream.fold (s: Stream a) (n: Nat) (init: b) (f: b → a → b): b := match n with
  | Zero => init
  | Succ k => Stream.fold s.tail k (f init s.head) f

--| `fold` over the first `n` values is a fold of `take n`.
theorem Stream.foldTake ∀ (s: Stream a) (n: Nat) (init: b) (f: b → a → b):
    s.fold n init f = (s.take n).foldLeft init f :=
  match n with
    | Zero => (Eq.cong (xs => xs.foldLeft init f) (Stream.takeZero s)).flipped
    | Succ k =>
      (Stream.foldTake s.tail k (f init s.head) f).trans
        (Eq.cong (xs => xs.foldLeft init f) (Stream.takeSucc s k)).flipped

--| The first of the first `n` values to satisfy `p`, or `None`: `(Stream.iterate (+ 1) 0).find 100 (n => n * n > 50)`
--| is `Some 8`. It reads by `head` and `tail` and stops at the first match.
@[tailrec]
def Stream.find (s: Stream a) (n: Nat) (p: a → Bool): Option a := match n with
  | Zero => None
  | Succ k => if p s.head then Some s.head else Stream.find s.tail k p

--| `find` in the first `n` values is a `find` in `take n`.
theorem Stream.findTake ∀ (s: Stream a) (n: Nat) (p: a → Bool): s.find n p = (s.take n).find p := match n with
  | Zero => (Eq.cong (xs => xs.find p) (Stream.takeZero s)).flipped
  | Succ k =>
    calc s.find (Succ k) p
      _ = (if p s.head then Some s.head else s.tail.find k p) := byComputing
      _ = (if p s.head then Some s.head else (s.tail.take k).find p) :=
        Eq.cong (r => if p s.head then Some s.head else r) (Stream.findTake s.tail k p)
      _ = [s.head, ..s.tail.take k].find p := byComputing
      _ = (s.take (Succ k)).find p := Eq.cong (xs => xs.find p) (Stream.takeSucc s k).flipped

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
  Stream.unfold (st => (f st.fst.head st.snd.head, (st.fst.tail, st.snd.tail))) (s, t)

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
def Stream.interleave (s t: Stream a): Stream a := Stream.unfold (st => (st.fst.head, (st.snd, st.fst.tail))) (s, t)

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
  Stream.unfold (st => (st.fst, (f st.fst st.snd.head, st.snd.tail))) (init, s)

--| The first value of `scan` is the initial value.
theorem Stream.scanHead ∀ (s: Stream a) (init: b) (f: b → a → b): (s.scan init f).head = init := byComputing

--| The tail of `scan` is the `scan` of the tail, from the initial value folded with the first value.
theorem Stream.scanTail ∀ (s: Stream a) (init: b) (f: b → a → b):
    (s.scan init f).tail = s.tail.scan (f init s.head) f :=
  Stream.unfoldTail _ _ _

--| `scan` at position `n` is the fold of the first `n` values.
theorem Stream.scanAt ∀ (s: Stream a) (init: b) (f: b → a → b) (n: Nat): (s.scan init f).at n = s.fold n init f :=
  match n with
    | Zero => byComputing
    | Succ m =>
      calc (s.scan init f).at (Succ m)
        _ = (s.scan init f).tail.at m := (Stream.tailAt (s.scan init f) m).flipped
        _ = (s.tail.scan (f init s.head) f).at m := Eq.cong (r => r.at m) (Stream.scanTail s init f)
        _ = s.tail.fold m (f init s.head) f := Stream.scanAt s.tail (f init s.head) f m

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
