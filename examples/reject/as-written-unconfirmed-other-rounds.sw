-- expect-error: E-TYPE-MISMATCH
-- As as-written-unconfirmed-slow-check.sw, but the hypothesis is about 0
-- rounds while the `match` is on 12, so the generalised goal doesn't hold.
-- Checking it compares closures whose environments hold the same large
-- values, built separately but sharing their parts: the same-closure
-- shortcut compares each pair of shared parts once, so this fails at once
-- rather than after half a minute walking them as trees (SW-2730).
import Std (Bool, Eq, List, Nat, Option, Void)

def step (n: Nat) (k: Nat): Nat := n * k + 1

def settle (x: Nat) (k: Nat): (rounds: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := step x k
    if next == x then Some x else settle next k more

def limit: Nat := 1000

def inner (x: Nat) (k: Nat): Nat :=
  match settle x k 40 with
    | None => x
    | Some y => y

def outer (x: Nat) (k: Nat): (rounds: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := inner x k
    if next == x then Some x else outer next k more

theorem slowCheck (x: Nat) (k: Nat) (answer: Nat)
    (solved: outer x k 0 = Some answer): ∃ (y: Nat) => answer = y :=
  match found: outer x k 12 with
    | None => Void.exfalso (Option.noneNotSome answer solved)
    | Some y => Witness y (Option.someInjective [x := y] [y := answer] solved |> Eq.sym)
