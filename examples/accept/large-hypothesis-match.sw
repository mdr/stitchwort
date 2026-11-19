-- A `match` on a call (`outer x k 12`) that a hypothesis mentions, where
-- that hypothesis is too large to compute in full (each round of `outer`
-- runs `inner`, which unfolds `settle … 40`): the hypothesis is read with
-- its calls as written, the call is found there, and the `match` refines
-- it (SW-4091). With the call in the goal instead, the goal itself is too
-- large and the `match` runs out:
-- examples/reject/as-written-unconfirmed-slow-check.sw.
import Std (Bool, Eq, List, Nat, Option, Void)

def step (n k: Nat): Nat := n * k + 1

def settle (x k: Nat): (rounds: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := step x k
    if next == x then Some x else settle next k more

def limit: Nat := 1000

def inner (x k: Nat): Nat := match settle x k 40 with
  | None => x
  | Some y => y

def outer (x k: Nat): (rounds: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := inner x k
    if next == x then Some x else outer next k more

theorem slowCheck ∀ (x k answer: Nat) (solved: outer x k 12 = Some answer): ∃ (y: Nat) => answer = y :=
  match found: outer x k 12 with
    | None => Void.impossible (Option.noneNotSome answer solved)
    | Some y => Witness y (Option.someInjective solved |> Eq.flipped)
