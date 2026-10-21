-- expect-error: E-INSTANCE-NONE
-- A proposition is used where a `Bool` is expected only if something
-- decides it, and functions have no `DecEq` instance.
def sameAs (f: Nat -> Nat) (gs: List (Nat -> Nat)): List (Nat -> Nat) :=
  List.filter (g => g = f) gs
