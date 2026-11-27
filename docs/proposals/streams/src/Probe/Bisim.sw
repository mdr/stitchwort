namespace Probe.Bisim

import Std (Nat, Eq)
import Probe.Fn (Stream)

-- "`s` is `map f` of the iterates from some `y`, and `t` is the iterates from `f y`."
def Related (f: a → a) (s t: Stream a): Prop := ∃ (y: a) => s = (Stream.iterate f y).map f ∧ t = Stream.iterate f (f y)

-- The relation is a bisimulation: related streams have equal heads and related tails.
theorem Related.step ∀ (f: a → a) (s t: Stream a) (h: Related f s t): s.head = t.head ∧ Related f s.tail t.tail :=
  match h with
    | Witness y (Both hs ht) => rewrite hs, ht then Both byComputing (Witness (f y) (Both byComputing byComputing))

-- The same theorem as `Stream.mapIterate`, by bisimulation instead of by index.
theorem mapIterateBisim ∀ (f: a → a) (x: a): (Stream.iterate f x).map f = Stream.iterate f (f x) :=
  Stream.bisim
    (Related f)
    (Related.step f)
    ((Stream.iterate f x).map f)
    (Stream.iterate f (f x))
    (Witness x (Both byComputing byComputing))

-- Alternating two streams as a function of the position: its tail law is not
-- by computing (`E-REFL`), and needs an argument about parity. `Probe.Corec`
-- defines it through `unfold` instead, where the law computes.
def Stream.interleaveAt (s t: Stream a): Stream a := { at = n => if n % 2 == 0 then s.at (n / 2) else t.at (n / 2) }
