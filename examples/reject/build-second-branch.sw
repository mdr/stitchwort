-- expect-error: E-TYPE-MISMATCH
-- The first branch of an `if` sets its type: here `x ∈ xs`, so the second,
-- a test fact, needs `.read`. Facts are built, never read, implicitly.
import Std (Bool, List, Nat)

theorem either ∀ (c: Bool) (x: Nat) (xs: List Nat) (m: x ∈ xs) (found: xs.contains x): True :=
  let w := if c then m else found
  rfl
