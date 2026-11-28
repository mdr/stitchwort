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
  base = fr.origin.drop (fr.offset + 1),
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
