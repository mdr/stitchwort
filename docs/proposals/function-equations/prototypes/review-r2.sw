-- Review R2: `if h: p` whose branch uses `h` (§3.5). std has several:
-- Char.fromNat, Fin.ofNatCheck, SafeNat/SafeInt, Mod. Is the `ifTrue`
-- equation provable when `p` is `i < n` (a `Bool` equation underneath)?
import Std (Nat, Void, Eq, Fin, Option, Decidable, Bool)

def check (n: Nat) (i: Nat): Option (Fin n) := if h: i < n then Some (Fin.ofNatLt n i h) else None

theorem lessIsBool ∀ (i: Nat) (n: Nat) (h: i < n): Nat.leq (Succ i) n = True := h

theorem checkIfTrue ∀ (n: Nat) (i: Nat) (h: i < n): check n i = Some (Fin.ofNatLt n i h) :=
  Decidable.elimEq (Nat.decLessThan i n) (h2 => Some (Fin.ofNatLt n i h2)) (no => None) (Some (Fin.ofNatLt n i h))
    (h2 => J (r e => Some (Fin.ofNatLt n i h2) = Some (Fin.ofNatLt n i r)) rfl (Bool.uniqueEq (Nat.leq (Succ i) n) True h2 h))
    (no => Void.exfalso (no h))
