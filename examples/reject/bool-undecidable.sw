-- expect-error: E-AUTO-NONE
-- A proposition is used where a `Bool` is expected only if something
-- decides it, and nothing decides equality of functions.
def sameAs (f: Nat -> Nat) (gs: List (Nat -> Nat)): List (Nat -> Nat) :=
  List.filter (g => g = f) gs
