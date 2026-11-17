-- expect-error: E-NO-READING
-- A pattern that doesn't fit a test fact's reading: `small n` reads as
-- `n ≤ 9`, a reading that isn't an `Or`; for a test with no reading at all,
-- see `reading-pattern-opaque.sw` (docs/proposals/bool-as-proposition.md §6.7).
import Std (Bool, Nat)

def small (n: Nat): Bool := n < 10

def t (n: Nat) (h: small n = True): Nat :=
  match h with
    | Inl x => 0
    | Inr y => 1
