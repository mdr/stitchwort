-- Goals show the logic operators in their Unicode spellings (D1204, D1211),
-- whichever spelling the source used: `x ∈ xs`, `x ∉ xs`, `a ≠ b`, `¬p`,
-- `p ↔ q`, `∃ (x: T) => P`, `∧`, `∨` and `≤`.
import Std (Exists, Iff)

theorem shown (x: Nat) (y: Nat) (xs: List Nat) (p: Prop) (ne: x != y) (out: y !in xs) (np: !p):
    (x in xs <-> p) && (exists (n: Nat) => n <= x || n = y) := ?
