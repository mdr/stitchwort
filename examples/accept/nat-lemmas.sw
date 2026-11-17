-- Arithmetic lemmas from the prelude, used in small proofs.
import Std (Eq, Nat)

theorem addSwap ∀ (a b c: Nat): a + (b + c) = b + (a + c) := calc a + (b + c)
  _ = a + b + c := (Nat.addAssoc a b c).flipped
  _ = b + a + c := Eq.cong (t => t + c) (Nat.addComm a b)
  _ = b + (a + c) := Nat.addAssoc b a c

theorem squareOfSum ∀ (a b: Nat): (a + b) * (a + b) = a * (a + b) + b * (a + b) := Nat.mulDistribRight a b (a + b)

theorem timesTwo ∀ (n: Nat): n * 2 = n + n := Eq.trans (Nat.mulSucc n 1) (Eq.cong (t => n + t) (Nat.mulOne n))

theorem leftSmaller ∀ (a b c: Nat) (h: a ≤ b): a ≤ b + c := Nat.leTrans a b (b + c) h (Nat.leAddRight b c)

theorem pred ∀ (n: Nat): (n + 5) - 5 = n := Nat.addSub n 5

theorem remainderSmall ∀ (n: Nat): n % 7 < 7 := Nat.modLess n 7 (Nat.succNotZero 6)

-- `arithmetic` knows division by a number; by a variable, the std facts about it
-- go in as hints.
theorem halfLe ∀ (n: Nat): n / 2 ≤ n := arithmetic

theorem halfLt ∀ (n: Nat) (h: 0 < n): n / 2 < n := Nat.divLt n 2 h arithmetic

theorem halfAndBack ∀ (n: Nat) (h: 0 < n): n / 2 + 1 ≤ n := arithmetic

theorem divLeSelf ∀ (n k: Nat) (h: k ≠ 0): n / k ≤ n := arithmetic [Nat.divLe n k]
