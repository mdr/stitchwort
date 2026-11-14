-- SW-1434: a proof follows `if a && b` with one `match e:` on the whole
-- `Bool`, as it follows any other `if`. The `if`s here are in a function
-- with a `decreasing` measure and in helpers lifted from a lambda, a
-- `match` arm and a local `def`; the example checks that a `match` on the
-- condition's `Bool` refines each of them.
import Std (Nat, Bool, Void, List, Option)

def run (target: Nat) (front: List Nat) (count sum: Nat) (rest: List Nat): Option (List Nat)
    decreasing front.length + rest.length
:=
  if sum == target && 2 <= count then Some (front.take count)
  else
    match rest with
      | [] => None
      | [next, ..more] => run target front (count + 1) (sum + next) more

theorem runFoundLong ∀ (target: Nat) (front: List Nat) (count sum: Nat) (rest found: List Nat)
    (r: run target front count sum rest = Some found):
    2 ≤ count ∨ 0 < rest.length :=
  rewrite run.unfold target front count sum rest at r in
    match e: sum == target && 2 <= count with
      | True => Inl (omega)
      | False =>
        match rest with
          | [] => Void.exfalso (Option.noneNotSome found r)
          | [next, ..more] => Inr (omega)

-- The same `if` inside a function inside a `match` arm that isn't the last
-- thing in the definition, and inside a local `def`: each is in a helper
-- lifted out of the definition, as is the inner `match`.
def marks (target count: Nat) (ys: List Nat): Nat := match ys with
  | [] => 0
  | [y, ..more] =>
    (z =>
          if z == target && 2 <= count then 1
          else
            match z with
              | Zero => 0
              | Succ k => 0) y
      + marks target count more

theorem marksLong ∀ (target count y: Nat) (same: y = target) (long: 2 ≤ count): marks target count [y] = 1 :=
  match e: y == target && 2 <= count with
    | True => omega
    | False => Void.exfalso (omega)

-- A local `def` with a recursive call, and a lambda in a `match` arm that
-- is not the last thing in the definition.
def outer (target: Nat) (xs: List Nat): Nat :=
  def go (sum: Nat) (rest: List Nat): Nat
      decreasing rest.length
  :=
    if sum == target && 2 <= xs.length then 1
    else
      match rest with
        | [] => 0
        | [r, ..more] => go (sum + r) more
  go 0 xs

theorem outerLong ∀ (target: Nat) (xs: List Nat) (same: target = 0) (long: 2 ≤ xs.length): outer target xs = 1 :=
  match e: 0 == target && 2 <= xs.length with
    | True => omega
    | False => Void.exfalso (omega)

def viaLambda (target count: Nat) (ys: List Nat): Nat := match ys with
  | [] => 0
  | [y, ..more] =>
    (z =>
          if z == target && 2 <= count then 1
          else
            (match more with
              | [] => 0
              | [m, ..rest] => viaLambda target count rest)) y
      + viaLambda target count more

theorem viaLambdaLong ∀ (target count y: Nat) (same: y = target) (long: 2 ≤ count): viaLambda target count [y] = 1 :=
  match e: y == target && 2 <= count with
    | True => omega
    | False => Void.exfalso (omega)
