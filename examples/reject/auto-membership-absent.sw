-- expect-error: E-AUTO-FALSE
-- A value that isn't in a long literal list is false, not undecidable.
import Std (List)

def inList (n: Nat) [auto ok: n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]: Nat := n

def use: Nat := inList 13
