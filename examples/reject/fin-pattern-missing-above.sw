-- expect-error: E-NONEXHAUSTIVE
-- The bound of this `Fin` isn't a number, so after 0 and 1 every larger
-- number is left: the missing case is reported as those numbers, as for a
-- `Nat`, not as the `FSucc _` two levels down (D1079).
import Std (Fin)

def name: (n: Nat) → Fin (Succ (Succ n)) → Text
  | _, 0 => "zero"
  | _, 1 => "one"
