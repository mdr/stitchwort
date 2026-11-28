namespace Probe.ByUnfold

import Std (Nat, Eq)
import Probe.Fn (Stream)
import Probe.Corec.Stream (unfold)

-- On the plain one-field stream: `map` written as an unfold whose state is
-- the stream being mapped, so that each `tail` is one step for a runtime
-- that keeps an unfold as its step and state. Its laws still compute.
def Stream.mapU (s: Stream a) (f: a → b): Stream b := unfold (t => (f t.head, t.tail)) s

theorem mapUTail ∀ (s: Stream a) (f: a → b): (s.mapU f).tail = s.tail.mapU f := byComputing

theorem mapUHead ∀ (s: Stream a) (f: a → b): (s.mapU f).head = f s.head := byComputing

theorem tailsHead ∀ (n: Nat) (s: Stream a): (Nat.iterate n (t => t.tail) s).head = s.at n := match n with
  | Zero => byComputing
  | Succ k => tailsHead k s.tail

theorem mapUAt ∀ (s: Stream a) (f: a → b) (n: Nat): (s.mapU f).at n = f (s.at n) := Eq.cong f (tailsHead n s)

-- A stream given by its positions, as an unfold over the position: what the
-- record constructor would become at run time.
theorem countUp ∀ (n i: Nat): Nat.iterate n (j => Succ j) i = i + n := match n with
  | Zero => byComputing
  | Succ k => countUp k (Succ i)

theorem fromFnIsUnfold ∀ (f: Nat → a) (n: Nat): (unfold (i => (f i, Succ i)) 0).at n = f n := Eq.cong f (countUp n 0)
