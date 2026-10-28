-- A recursive call of a definition with `decreasing` written with a dot,
-- passing its proof by name as the prefix form does.
import Std (Nat)

type Counter = { start: Nat }

def Counter.down (counter: Counter) (n: Nat): Nat
    decreasing n
:=
  match n with
    | Zero => counter.start
    | Succ k => counter.down k [decreasing := Nat.leRefl k]

def Counter.downIf (counter: Counter) (n: Nat): Nat
    decreasing n
:=
  if h: n = 0 then counter.start else counter.downIf (n - 1) [decreasing := omega]

-- Lexicographic, as `decreasing-lex.sw`'s `ack`.
def Counter.ack (counter: Counter) (m: Nat) (n: Nat): Nat
    decreasing (m, n)
:=
  match m, n with
    | Zero, n => n + 1
    | Succ k, Zero => counter.ack k 1 [decreasing := Nat.LexLess.First (Nat.leRefl k)]
    | Succ k, Succ j =>
      counter.ack k (counter.ack (Succ k) j [decreasing := Nat.LexLess.Second rfl (Nat.leRefl j)])
        [decreasing := Nat.LexLess.First (Nat.leRefl k)]

theorem downTwo: Counter.down { start = 5 } 2 = 5 := rfl

theorem ackTwo: Counter.ack { start = 0 } 2 3 = 9 := rfl
