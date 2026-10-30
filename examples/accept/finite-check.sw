-- `Finite.check` (docs/proposals/decide.md §6.2): a `Bool` statement about
-- every value of a finite type, proved by computing it for each value on
-- `Finite.all` (`rfl`) and one lemma. It goes past `cases`' 64 cases: ten
-- `Bool`s are 1,024 cases, checked as one list.
import Std (Bool, Fin, Finite, List)

-- Parity doesn't depend on the order of the bits (decide/scale.sw's
-- statement).
def xorAll: List Bool → Bool
  | Nil => False
  | Cons x rest => Bool.xor x (xorAll rest)

def sameBothWays (bits: List Bool): Bool := xorAll bits == xorAll (List.reverse bits)

-- The ten variables, as one value: a record of `Bool`s, whose `Finite`
-- instance is derived.
type Ten = { b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, b9: Bool }

def Ten.bits (t: Ten): List Bool := [t.b0, t.b1, t.b2, t.b3, t.b4, t.b5, t.b6, t.b7, t.b8, t.b9]

theorem tenBothWays (t: Ten): sameBothWays t.bits = True := Finite.check (u => sameBothWays u.bits) rfl t

-- Two variables, as a pair: day 12's `rowEndsSplit`'s shape, over a pair of
-- pairs.
def rowEnds: ((Bool, Bool), (Bool, Bool)) → Bool
  | ((plot, out), (side, sideOut)) =>
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut))
      == Bool.toNat (plot ∧ ¬out ∧ ¬side) + Bool.toNat (side ∧ sideOut ∧ plot ∧ ¬out)

theorem rowEndsAll (plot: Bool) (out: Bool) (side: Bool) (sideOut: Bool): rowEnds ((plot, out), (side, sideOut)) = True :=
  Finite.check rowEnds rfl ((plot, out), (side, sideOut))

-- `Fin n` has an instance written by hand.
theorem squaresBelow (i: Fin 6): (Fin.toNat i * Fin.toNat i < 36) = True :=
  Finite.check (j => Fin.toNat j * Fin.toNat j < 36) rfl i
