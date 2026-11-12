-- expect-error: E-NO-READING
-- A test fact with no reading has no parts: the error points at the pattern
-- that takes it apart (docs/proposals/bool-as-proposition.md §6.7).
import Std (Bool, Nat)

def small (n: Nat): Bool := n < 10

def t (n: Nat) (h: small n = True): Nat :=
  match h with
    | Inl x => 0
    | Inr y => 1
