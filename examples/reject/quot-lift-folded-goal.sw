-- expect-error: E-REFL
-- A definition that lifts its argument stays folded on a variable, as one
-- stuck on a `match` does (docs/proposals/map-equality.md §7.2, test A8), so
-- the message shows `observe q`, not the lift it unfolds to. With
-- `Quot.mk True` for `q` it would compute (accept/quot-lift.sw).
def BoolEq (x: Bool) (y: Bool): Prop := x = y
def QE: Type := Quot Bool BoolEq

def toNat (b: Bool): Nat := if b then 1 else 0

def toNatRespects (x: Bool) (y: Bool) (same: BoolEq x y): toNat x = toNat y :=
  rewrite same in rfl

def observe (q: QE): Nat := Quot.lift toNat toNatRespects q

theorem alwaysOne (q: QE): observe q = 1 := rfl
