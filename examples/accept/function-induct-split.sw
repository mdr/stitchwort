-- `f.induct` for lifted `match`es whose alternatives need more than one split
-- of the scrutinee: a nested pattern on a type with several constructors
-- (`Next count None` and `Next count (Some value)`), number literals (`0` is
-- `Zero`, `1` is `Succ Zero`) with a catch-all after them, and an alternative
-- that follows an overlapping one (`Some n` after `Some 0`, with `n ≠ 0`).
import Std (Eq, List, Nat, Option, Void)

type Step = | Halt | Next (count: Nat) (printed: Option Nat)

-- The values printed before a halt, newest first, within `fuel` steps.
def collect (step: Nat → Step) (printed: List Nat): (fuel: Nat) → List Nat
  | Zero => printed
  | Succ fuel =>
    match step fuel with
      | Halt => printed
      | Next count None => collect step printed fuel
      | Next count (Some value) => collect step [value, ..printed] fuel

theorem collectKeeps ∀ (step: Nat → Step) (printed: List Nat) (fuel: Nat):
    List.length printed ≤ List.length (collect step printed fuel) :=
  collect.induct step
    (printed fuel result => List.length printed ≤ List.length result)
    (printed => arithmetic)
    (printed fuel halted => arithmetic)
    (printed fuel count none ih => ih)
    (printed fuel count value some ih => arithmetic)
    printed
    fuel

-- Twice the numbers that are 0 mod 3, plus the ones that are 1 mod 3.
def score: List Nat → Nat
  | [] => 0
  | [x, ..rest] =>
    match x % 3 with
      | 0 => 2 + score rest
      | 1 => 1 + score rest
      | _ => score rest

theorem scoreLe ∀ (xs: List Nat): score xs ≤ 2 * List.length xs :=
  score.induct
    (xs result => result ≤ 2 * List.length xs)
    arithmetic
    (x rest zero ih => arithmetic)
    (x rest one ih => arithmetic)
    (x rest notZero notOne ih => arithmetic)
    xs

-- Each element after the first, by its value, a zero counted as one.
def weigh: List Nat → Nat
  | [] => 0
  | [x, ..rest] =>
    match List.head rest with
      | None => 0
      | Some 0 => 1 + weigh rest
      | Some n => n + weigh rest

theorem weighCounts ∀ (xs: List Nat): List.length xs ≤ weigh xs + 1 :=
  weigh.induct
    (xs result => List.length xs ≤ result + 1)
    arithmetic
    (x rest none =>
      match rest with
        | [] => arithmetic
        | [y, ..ys] => (Option.someNotNone y none).impossible)
    (x rest zero ih => arithmetic)
    (x rest n some notZero ih => arithmetic)
    xs
