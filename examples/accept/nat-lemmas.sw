-- Arithmetic lemmas from the prelude, used in small proofs.
import Std (Eq, Nat)

theorem addSwap (a: Nat) (b: Nat) (c: Nat): a + (b + c) = b + (a + c) :=
  Eq.trans (Eq.sym (Nat.addAssoc a b c))
    (Eq.trans (Eq.cong (t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c))

theorem squareOfSum (a: Nat) (b: Nat): (a + b) * (a + b) = a * (a + b) + b * (a + b) := Nat.mulDistribRight a b (a + b)

theorem timesTwo (n: Nat): n * 2 = n + n := Eq.trans (Nat.mulSucc n 1) (Eq.cong (t => n + t) (Nat.mulOne n))

theorem leftSmaller (a: Nat) (b: Nat) (c: Nat) (h: a ≤ b): a ≤ b + c := Nat.leTrans a b (b + c) h (Nat.leAddRight b c)

theorem pred (n: Nat): (n + 5) - 5 = n := Nat.addSub n 5

theorem remainderSmall (n: Nat): n % 7 < 7 := Nat.modLess n 7 (Nat.succNotZero 6)

-- `omega` doesn't know division; the std facts about it go in as hints.
theorem halfLe (n: Nat): n / 2 ≤ n := omega [Nat.divLe n 2]

theorem halfLt (n: Nat) (h: 0 < n): n / 2 < n := Nat.divLt n 2 h omega

theorem halfAndBack (n: Nat) (h: 0 < n): n / 2 + 1 ≤ n := omega [Nat.divLt n 2 h omega]
