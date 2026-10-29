-- Option (b) by hand: what a derived enumeration (SW-807) and `decide`
-- would generate. `Finite a` is a list of every value with a proof that
-- every value is on it; a statement over finite variables is checked by
-- one `rfl` on `List.all`, and one generic lemma turns that into the
-- statement for every value.
import Std (Bool, List, Void)

type Finite (a: Type) = {
  all: List a,
  complete: (x: a) → x ∈ all
}

-- `List.all` true of a list is true of each member (day 21's `allMember`).
theorem allMember (passes: a → Bool): (xs: List a) → List.all xs passes = True → (x: a) → x ∈ xs → passes x = True
  | Nil, all, x, member => Void.exfalso member
  | Cons first rest, all, x, Inl same => rewrite <- same in Bool.andLeft _ _ all
  | Cons first rest, all, x, Inr later => allMember passes rest (Bool.andRight _ _ all) x later

-- The generic soundness lemma `decide` would use: check every value, get
-- the statement.
theorem Finite.check (fin: Finite a) (passes: a → Bool) (checked: List.all fin.all passes = True) (x: a): passes x = True :=
  allMember passes fin.all checked x (fin.complete x)

-- What deriving would give for `Bool` (SW-807): the constructors in order,
-- and the completeness proof by cases, one arm per constructor.
def boolFinite: Finite Bool := {
  all = [False, True],
  complete = x => match x with
    | False => Inl rfl
    | True => Inr (Inl rfl)
}

-- Day 12's truth table, as `decide` would elaborate it: the statement as a
-- `Bool` function of the four variables, checked over 16 values by one
-- `rfl`, then `Finite.check` four times (once per variable, nested).
def convex (plot: Bool) (vertical: Bool) (horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal
def concave (plot: Bool) (vertical: Bool) (horizontal: Bool) (diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

def rowEndsHolds (plot: Bool) (out: Bool) (side: Bool) (sideOut: Bool): Bool :=
  Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) == Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out)

theorem rowEndsChecked:
    List.all boolFinite.all (plot =>
      List.all boolFinite.all (out =>
        List.all boolFinite.all (side =>
          List.all boolFinite.all (sideOut => rowEndsHolds plot out side sideOut)))) = True := rfl

theorem rowEndsHoldsAll (plot: Bool) (out: Bool) (side: Bool) (sideOut: Bool): rowEndsHolds plot out side sideOut = True :=
  let p1 := Finite.check boolFinite (plot =>
      List.all boolFinite.all (out =>
        List.all boolFinite.all (side =>
          List.all boolFinite.all (sideOut => rowEndsHolds plot out side sideOut)))) rowEndsChecked plot
  let p2 := Finite.check boolFinite (out =>
      List.all boolFinite.all (side =>
        List.all boolFinite.all (sideOut => rowEndsHolds plot out side sideOut))) p1 out
  let p3 := Finite.check boolFinite (side =>
      List.all boolFinite.all (sideOut => rowEndsHolds plot out side sideOut)) p2 side
  Finite.check boolFinite (sideOut => rowEndsHolds plot out side sideOut) p3 sideOut
