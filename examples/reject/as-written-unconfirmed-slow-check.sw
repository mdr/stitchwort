-- expect-error: E-RESOURCE
-- A `match` whose hypothesis is too large to compute in full, where the
-- expression is found as written but checking the generalised goal would
-- compare the same huge values (each round of `outer` runs `inner`, which
-- unfolds `settle … 40`): the check has its own small budget, so the `match`
-- fails at once as it did before stage 4, rather than comparing for minutes.
-- (examples/accept/as-written-unconfirmed.sw; goal-as-written.md stage 4)
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
    (solved: outer x k 12 = Some answer): ∃ (y: Nat) => answer = y :=
  match found: outer x k 12 with
    | None => Void.exfalso (Option.noneNotSome answer solved)
    | Some y => Witness y (Option.someInjective solved |> Eq.sym)
