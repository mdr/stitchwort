-- Probe for docs/proposals/bool-and-prop.md §5 (option 1): `≤` as an
-- inductive relation. Checks.
import Std (Bool, Nat, Void)

type Le: Nat → Nat → Prop = | LeZero: Le 0 n | LeSucc (h: Le m n): Le (Succ m) (Succ n)

-- Induction on the proof: two arms, where `Nat.leTrans` has four.
theorem Le.trans: Le a b → Le b c → Le a c
  | LeZero, _ => LeZero
  | LeSucc h1, LeSucc h2 => LeSucc (Le.trans h1 h2)

-- The bridge from the test, by recursion on the numbers.
theorem Le.ofLeq: ∀ (m n: Nat) => Nat.leq m n = True → Le m n
  | Zero, n, h => LeZero
  | Succ m, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Succ n, h => LeSucc (Le.ofLeq m n h)

-- Big numbers still check quickly: the proof is the bridge applied to `rfl`,
-- and nothing builds the 30-digit chain of `LeSucc`.
theorem big: Le 123456789012345678901234567890 123456789012345678901234567891 :=
  Le.ofLeq 123456789012345678901234567890 123456789012345678901234567891 rfl
