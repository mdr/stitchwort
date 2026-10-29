-- How evaluation-based checking (option (b) in decide.md) scales: one
-- `rfl` over every assignment of n `Bool`s, here a parity identity.
-- Measured with STITCHWORT_TIMINGS=decls (elaboration ms + kernel ms):
-- n = 10: 37 + 29; n = 14: 773 + 596; n = 16: 3485 + 2626 (left out of
-- this file, to keep it quick; add `theorem n16: allBools 16 holds = True := rfl`).
import Std (Bool, List)

def xor (a: Bool) (b: Bool): Bool := if a then not b else b

def xorAll: List Bool → Bool
  | Nil => False
  | Cons x rest => xor x (xorAll rest)

def allBools: (n: Nat) → (p: List Bool → Bool) → Bool
  | Zero, p => p []
  | Succ n, p => allBools n (xs => p (Cons False xs)) && allBools n (xs => p (Cons True xs))

def holds (xs: List Bool): Bool := xorAll xs == xorAll (List.reverse xs)

theorem n10: allBools 10 holds = True := rfl

theorem n14: allBools 14 holds = True := rfl
