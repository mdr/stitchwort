-- expect-error: E-TYPE-MISMATCH
-- A test fact isn't its reading: `found` is `xs.contains x = True`, and the
-- note says it reads as `x ∈ xs` and that `.read` gives that
-- (docs/proposals/bool-as-proposition.md §6.7).
import Std (Bool, List)

theorem member (x: Nat) (xs: List Nat) (found: xs.contains x): x ∈ xs := found
