-- A term made inside a `match` arm, after the `match` replaced its
-- expression in the goal, still holds the expression: here `Witness (Cons
-- k rest)` makes `run n (Cons k rest)`, which computes to a `match` on
-- `step n`. Rewriting with the arm's equation, `moved`, replaces it there
-- too.

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

theorem sameRun (n: Nat) (k: Nat) (rest: List Nat): Exists (List Nat) (xs => run n xs = run n (Cons k rest)) :=
  match moved: step n with
    | Some m => Witness (Cons k rest) (rewrite moved in rfl)
    | None => Witness (Cons k rest) (rewrite moved in rfl)

-- The same when a `rewrite` in the arm makes the term.
theorem renamedRun (n: Nat) (other: Nat) (same: other = n) (k: Nat) (rest: List Nat): run other (Cons k rest) = run n (Cons k rest) :=
  match moved: step n with
    | Some m => rewrite same, moved in rfl
    | None => rewrite same, moved in rfl
