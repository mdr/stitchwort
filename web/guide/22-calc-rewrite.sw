import Std (List, Eq)

-- `calc` writes a proof as a chain of steps. Each line says how it relates
-- to the one before and gives a reason; a step that follows by computing
-- needs no reason.
theorem chain (a: Nat) (b: Nat) (h1: a = b) (h2: b <= 3): a < 5 :=
  calc a
    _ = b := h1
    _ <= 3 := h2
    _ < 5

-- `rewrite` replaces the left side of an equation by its right side in
-- what you are proving, so you don't spell out the expression around it.
def double (n: Nat): Nat := n * 2

theorem addZero (n: Nat): n + 0 = n := omega

theorem doubleAddZero (n: Nat): double (n + 0) = n + n :=
  rewrite addZero n in
    calc double n
      _ = n * 2
      _ = n + n := omega

-- Proving two maps equal: the library has `List.mapCong`, and `_` leaves
-- the two functions for the compiler to read off the goal.
theorem mapAddZero (xs: List Nat): xs.map (x => x + 0) = xs.map (x => x) :=
  List.mapCong _ _ xs (x => rewrite addZero x in rfl)
