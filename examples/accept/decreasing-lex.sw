-- Lexicographic measures (docs/proposals/well-founded-recursion.md, stage
-- 3d): `decreasing (m1, m2)` says that each recursive call makes `m1`
-- smaller, or keeps it the same and makes `m2` smaller. A call's proof is a
-- `Nat.LexLess`: `Nat.LexLess.First h` (the first got smaller) or
-- `Nat.LexLess.Second rfl h` (the first stayed put, the second got smaller);
-- `omega` finds either, and `auto` finds one from a guard in scope. The
-- compiler gives each measure a fuel of its own, so the kernel still sees
-- only structural recursion.
--
--   $ stitchwort run examples/accept/decreasing-lex.sw
--   ack: 9
--   gcd: 6
--   minutes: 150

import Std (IO, Nat)

-- Ackermann's function: the second argument can grow without bound, but
-- the first never does, and when the first stays put the second goes down.
-- The inner call is in the outer call's arguments.
def ack (m: Nat) (n: Nat): Nat
    decreasing (m, n)
:=
  match m, n with
    | Zero, n => n + 1
    | Succ k, Zero => ack k 1 [decreasing := Nat.LexLess.First (Nat.leRefl k)]
    | Succ k, Succ j =>
      ack k (ack (Succ k) j [decreasing := Nat.LexLess.Second rfl (Nat.leRefl j)]) [decreasing := Nat.LexLess.First (Nat.leRefl k)]

test "ack" := ack 2 3 == 9 ∧ ack 3 3 == 61 ∧ ack 0 7 == 8

-- Tests and `rfl` compute through the two fuels.
theorem ackByRfl: ack 2 3 = 9 := rfl

-- `ack.unfold` is the definition's own equation.
theorem ackStep (k: Nat) (j: Nat): ack (Succ k) (Succ j) = ack k (ack (Succ k) j) :=
  ack.unfold (Succ k) (Succ j)

-- A theorem recursing on the same pair: the proof makes the calls `ack`
-- makes, and `omega` finds each call's `Nat.LexLess`.
theorem ackAbove (m: Nat) (n: Nat): n < ack m n
    decreasing (m, n)
:=
  rewrite ack.unfold m n in
  match m, n with
    | Zero, n => omega
    | Succ k, Zero => omega [ackAbove k 1 [decreasing := omega]]
    | Succ k, Succ j =>
      omega [
        ackAbove (Succ k) j [decreasing := omega],
        ackAbove k (ack (Succ k) j) [decreasing := omega]
      ]

-- Euclid by subtraction: one call makes the first number smaller, the other
-- keeps it and makes the second smaller.
def gcd (a: Nat) (b: Nat): Nat
    decreasing (a, b)
:=
  if za: a = 0 then b
  else if zb: b = 0 then a
  else if bigger: b < a then gcd (a - b) b [decreasing := omega]
  else gcd a (b - a) [decreasing := omega]

test "gcd" := gcd 12 18 == 6 ∧ gcd 17 5 == 1 ∧ gcd 0 9 == 9 ∧ gcd 9 0 == 9

-- Two counters, guard style: count the minutes down a clock, minutes first,
-- then an hour, starting the minutes again at 59. Each `if` puts the
-- decrease in scope, and `auto` builds the pair's proof from it.
def minutesLeft (hours: Nat) (minutes: Nat): Nat
    decreasing (hours, minutes)
:=
  let earlierMinute := minutes - 1
  let earlierHour := hours - 1
  if fewerMinutes: earlierMinute < minutes then 1 + minutesLeft hours earlierMinute
  else if fewerHours: earlierHour < hours then 1 + minutesLeft earlierHour 59
  else 0

test "minutesLeft" := minutesLeft 2 30 == 150 ∧ minutesLeft 0 0 == 0

def main(): {IO} () :=
  IO.print ("ack: " ++ Nat.toText (ack 2 3))
  IO.print ("gcd: " ++ Nat.toText (gcd 12 18))
  IO.print ("minutes: " ++ Nat.toText (minutesLeft 2 30))
