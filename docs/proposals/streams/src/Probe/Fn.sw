namespace Probe.Fn

import Std (Quot, Nat, Eq)

type Stream (a: Type) = { at: Nat → a }

def Stream.head (s: Stream a): a := s.at 0

def Stream.tail (s: Stream a): Stream a := { at = n => s.at (Succ n) }

def Stream.cons (s: Stream a) (x: a): Stream a := {
  at = n =>
    match n with
      | Zero => x
      | Succ m => s.at m
}

def Stream.map (s: Stream a) (f: a → b): Stream b := { at = n => f (s.at n) }

@[noReceiver]
def Stream.iterate (f: a → a) (x: a): Stream a := { at = n => Nat.iterate n f x }

def Stream.zipWith (s: Stream a) (t: Stream b) (f: a → b → c): Stream c := { at = n => f (s.at n) (t.at n) }

def Stream.take (s: Stream a) (n: Nat): List a := match n with
  | Zero => []
  | Succ m => [s.head, ..s.tail.take m]

theorem Stream.ext ∀ (s t: Stream a) (h: ∀ (n: Nat) => s.at n = t.at n): s = t :=
  Eq.cong (f => ({ at = f }: Stream a)) (Quot.funext Nat (n => a) s.at t.at h)

theorem Stream.mapIterate ∀ (f: a → a) (x: a): (Stream.iterate f x).map f = Stream.iterate f (f x) :=
  Stream.ext ((Stream.iterate f x).map f) (Stream.iterate f (f x)) (n => (Nat.iterateSuccLast f n x).flipped)

theorem Stream.consHeadTail ∀ (s: Stream a): s.tail.cons s.head = s := Stream.ext (s.tail.cons s.head) s (n =>
  match n with
    | Zero => byComputing
    | Succ m => byComputing)

-- Coinduction: any relation that is kept by head/tail (a bisimulation) is inside equality.
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

test "take" := (Stream.iterate (* 2) 1).take 5 == [1, 2, 4, 8, 16]
