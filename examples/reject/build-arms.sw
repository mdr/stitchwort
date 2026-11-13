-- expect-error: E-TYPE-MISMATCH
-- Three arms give a proof of `x ∈ xs` where `xs.contains x` is expected and
-- are built, all in one retry; the fourth gives a number and is the only
-- error reported.
import Std (Bool, List, Nat)

theorem arms ∀ (k: Nat) (x: Nat) (xs: List Nat) (m: x ∈ xs): xs.contains x := match k with
  | 0 => m
  | 1 => m
  | 2 => m
  | _ => k
