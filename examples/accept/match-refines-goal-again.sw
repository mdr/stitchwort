-- A `match` replaces its expression in the goal as it is when the `match`
-- is checked. `Witness (Cons k rest)` makes `run n (Cons k rest)` later, in
-- the arm, so its `step n` wasn't there to replace: one side computes to
-- `run m rest` and the other is stuck on `step n`. `byComputing` then
-- rewrites `step n` along the `match`'s equation and tries again
-- (match-refinement.md R3).

import Std (Eq, Exists, List, Nat, Option)

def step (n: Nat): Option Nat := match n with
  | Zero => None
  | Succ m => Some m

def run (n: Nat): List Nat → Option Nat
  | Nil => Some n
  | Cons k rest =>
    match step n with
      | Some m => run m rest
      | None => None

theorem sameRun ∀ (n k: Nat) (rest: List Nat): Exists (List Nat) (xs => run n xs = run n (Cons k rest)) :=
  match moved: step n with
    | Some m => Witness (Cons k rest) byComputing
    | None => Witness (Cons k rest) byComputing
