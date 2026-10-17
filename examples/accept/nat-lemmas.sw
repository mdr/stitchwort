-- Arithmetic lemmas from the prelude, used in small proofs.

theorem addSwap : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + (b + c) = b + (a + c)
addSwap a b c =
  Eq.trans (Eq.sym (Nat.addAssoc a b c))
    (Eq.trans (Eq.cong (\t -> t + c) (Nat.addComm a b)) (Nat.addAssoc b a c))

theorem squareOfSum : (a : Nat) -> (b : Nat) -> (a + b) * (a + b) = a * (a + b) + b * (a + b)
squareOfSum a b = Nat.mulDistribRight a b (a + b)

theorem timesTwo : (n : Nat) -> n * 2 = n + n
timesTwo n = Eq.trans (Nat.mulSucc n 1) (Eq.cong (\t -> n + t) (Nat.mulOne n))

theorem leftSmaller : (a : Nat) -> (b : Nat) -> (c : Nat) -> a <= b -> a <= b + c
leftSmaller a b c h = Nat.leTrans a b (b + c) h (Nat.leAddRight b c)

theorem pred : (n : Nat) -> (n + 5) - 5 = n
pred n = Nat.addSub n 5

theorem remainderSmall : (n : Nat) -> n % 7 < 7
remainderSmall n = Nat.modLess n 7 (Nat.succNotZero 6)
