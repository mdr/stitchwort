-- expect-error: E-MATCH-SIZE
-- The kernel matches a `Fin` one `FSucc` at a time, each case refining the
-- context, so a number pattern on one is limited to 64; a larger number is
-- compared in a condition (SW-2467).
import Std (Fin)

def name: (n: Nat) → Fin (Succ (Succ n)) → Text
  | _, 0 => "zero"
  | _, 1000000 => "a million"
  | _, _ => "other"
