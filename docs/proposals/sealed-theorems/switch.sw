import Std (Eq, Nat)

-- The probe for sealed theorems (crates/cli/tests/tools/sealed_theorems.rs; it was the
-- probe for stage 0's switch, which is now the default): `castComputes` is E-REFL
-- (program 2 of docs/proposals/sealed-theorems.md, section 3.1) and `useTrans` checks.
theorem flippedT ∀ [a: Type] [x y: a] (p: x = y): y = x := J (y' p' => y' = x) byComputing p
theorem addZeroT ∀ (n: Nat): n + 0 = n := match n with
  | Zero => byComputing
  | Succ m => Eq.cong Succ (addZeroT m)

theorem useTrans ∀ (n m: Nat) (h: n = m): n + 0 = m := Eq.trans (addZeroT n) h

def castNat (n x: Nat): Nat := J (y p => Nat) x (flippedT (addZeroT n))
theorem castComputes: castNat 3 5 = 5 := byComputing
