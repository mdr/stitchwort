-- expect-error: E-NONEXHAUSTIVE
-- Number patterns on a `Fin` are compiled as numbers, so one far above the
-- others costs no more than a small one: the missing case, 1, is found
-- without matching down to 2^128 (SW-2467).
import Std (Fin)

def name: (n: Nat) → Fin (Succ (Succ n)) → Text
  | _, 0 => "zero"
  | _, 340282366920938463463374607431768211456 => "one"
