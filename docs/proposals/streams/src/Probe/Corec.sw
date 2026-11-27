namespace Probe.Corec

import Std (Nat)
import Probe.Fn (Stream)
import Probe.Mach (Machine)

@[noReceiver]
def Stream.unfold [s: Type] (step: s → Pair a s) (start: s): Stream a :=
  { at = n => (step (Nat.iterate n (st => (step st).snd) start)).fst }

theorem unfoldHead ∀ (s: Type) (step: s → Pair a s) (start: s): (Stream.unfold step start).head = (step start).fst :=
  byComputing

theorem unfoldTail ∀ (s: Type) (step: s → Pair a s) (start: s):
    (Stream.unfold step start).tail = Stream.unfold step (step start).snd :=
  byComputing

theorem iterateTail ∀ (f: a → a) (x: a): (Stream.iterate f x).tail = Stream.iterate f (f x) := byComputing

theorem mapTail ∀ (s: Stream a) (f: a → b): (s.map f).tail = s.tail.map f := byComputing

theorem consTail ∀ (s: Stream a) (x: a): (s.cons x).tail = s := byComputing

def fibs: Stream Nat := Stream.unfold (p => (p.fst, (p.snd, p.fst + p.snd))) (0, 1)

def nested: Stream (Stream Nat) := Stream.iterate (s => s.map (+ 1)) fibs

test "fibs" := fibs.take 8 == [0, 1, 1, 2, 3, 5, 8, 13]
test "nested" := (nested.at 2).take 3 == [2, 3, 3]

@[noReceiver]
def Stream.repeat (x: a): Stream a := { at = n => x }

theorem repeatTail ∀ (x: a): (Stream.repeat x).tail = Stream.repeat x := byComputing

-- Alternating two streams, defined by its observations: the head is `s`'s,
-- and the tail alternates the other way round.
def Stream.interleave (s t: Stream a): Stream a := Stream.unfold (p => (p.fst.head, (p.snd, p.fst.tail))) (s, t)

theorem interleaveTail ∀ (s t: Stream a): (s.interleave t).tail = t.interleave s.tail := byComputing

test "interleave" := ((Stream.repeat 0).interleave fibs).take 6 == [0, 0, 0, 1, 0, 1]
