-- expect-error: E-TYPE-MISMATCH
-- A written `.read` is never built back into a test fact: read and then
-- built would turn `has xs x` into `xs.contains x`, two tests with the same
-- reading, silently.
import Std (Bool, List, Nat)

opaque def has (xs: List Nat) (x: Nat): Bool := xs.contains x

@[reading]
theorem hasReads (xs: List Nat) (x: Nat): has xs x ↔ x ∈ xs
    unfolding has
:= List.memContains xs x

theorem convert (xs: List Nat) (x: Nat) (h: has xs x): xs.contains x := h.read
