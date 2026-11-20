-- `rewrite repeatedly [g]` takes a guarded arm's step: `g`'s call is stuck on
-- the guard even though its patterns are constructors, so the arm is a rule,
-- and its guard, `isZero x = True`, is a premise found in the context.
import Std (Bool, Eq, List, Nat)

def isZero (n: Nat): Bool := match n with
  | 0 => True
  | _ => False

def skipZeros (xs: List Nat): List Nat := match xs with
  | [] => []
  | [x, ..rest] if isZero x => skipZeros rest
  | [x, ..rest] => [x, ..skipZeros rest]

theorem zeroSkipped ∀ (x: Nat) (rest: List Nat): isZero x = True → skipZeros [x, ..rest] = skipZeros rest := h =>
  rewrite repeatedly [skipZeros]
