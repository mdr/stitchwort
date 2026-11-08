-- expect-error: E-ABILITY
-- A condition after a pattern can't perform operations: the case tree has no
-- place to run them.

ability Ask where
  ask: () → {Ask} ask

def matchesAnswer (n: Nat): {Ask} Nat :=
  match n with
    | k if Nat() == k => k
    | _ => 0
