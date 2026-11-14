-- expect-error: E-READING-PLACE
-- A reading is declared with its test's function: `Nat.leq` is the
-- library's, so a program can't give it one.
import Std (Bool, Nat, Iff)

@[reading]
theorem leqReads (m n: Nat): Nat.leq m n ↔ m ≤ n := { forward = h => h, backward = h => h }
