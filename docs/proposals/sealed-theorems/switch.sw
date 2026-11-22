import Std (Eq, Nat)

-- The probe for `STITCHWORT_SEAL_THEOREMS=1` (crates/cli/tests/tools/seal_switch.rs):
-- checks as it stands; with the switch on, `castComputes` is E-REFL (program 2 of
-- docs/proposals/sealed-theorems.md, section 3.1) and `useTrans` still checks.
theorem flippedT ∀ [a: Type] [x y: a] (p: x = y): y = x := J (y' p' => y' = x) byComputing p
theorem addZeroT ∀ (n: Nat): n + 0 = n := match n with
  | Zero => byComputing
  | Succ m => Eq.cong Succ (addZeroT m)

theorem useTrans ∀ (n m: Nat) (h: n = m): n + 0 = m := Eq.trans (addZeroT n) h

def castNat (n x: Nat): Nat := J (y p => Nat) x (flippedT (addZeroT n))
theorem castComputes: castNat 3 5 = 5 := byComputing
