-- A recursive call of a definition with `decreasing` needs no proof where
-- `omega`, from the facts in scope, shows the measure gets smaller: `auto`
-- tries it when nothing else proves the call's obligation, as Lean's
-- `decreasing_tactic` does.

import Std (List, Nat)

-- The measure's goal is `List.length rest < Succ (List.length rest)`.
def takeFirst (xs: List Nat) (count: Nat): List Nat
    decreasing xs.length
:=
  match xs with
    | Nil => Nil
    | Cons x rest =>
      match count with
        | Zero => Nil
        | Succ fewer => Cons x (takeFirst rest fewer)

test "takeFirst" := takeFirst [1, 2, 3] 2 == [1, 2] ∧ takeFirst [1, 2, 3] 5 == [1, 2, 3]

-- `n / 10 < n` from `big`.
def digitsOnto (n: Nat) (acc: List Nat): List Nat
    decreasing n
:=
  if big: Nat.leq n 9 = False
  then digitsOnto (n / 10) (Cons (n % 10) acc)
  else Cons n acc

test "digits" := digitsOnto 1234 Nil == [1, 2, 3, 4]
