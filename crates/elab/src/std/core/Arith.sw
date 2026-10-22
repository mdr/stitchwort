-- core/Arith.sw. Arithmetic laws for `Nat` and `Int` (associativity,
-- commutativity, distributivity), with `Bool.xor` and the sign lemmas
-- `Int.mulAssoc` uses. Loaded with the core: `Nat.instAdd`, `Nat.instMul`,
-- `Int.instAdd` and `Int.instMul` need their laws, and `+` and `*` go through
-- those instances (docs/proposals/prelude-slim.md §2.1).

-- Arithmetic laws (docs/proposals/interfaces.md §5.13, D187): what the
-- `Add` and `Mul` instances for `Nat` and `Int` need. They come before the
-- instances, and their `+` and `*` are the primitive operations.

theorem Nat.addZero: (n: Nat) -> n + 0 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.addZero n)

theorem Nat.addSucc: (n: Nat) -> (m: Nat) -> n + Succ m = Succ (n + m)
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Nat.addSucc n m)

theorem Nat.addComm: (m: Nat) -> (n: Nat) -> m + n = n + m
  | Zero, n => Eq.sym (Nat.addZero n)
  | Succ m, n => Eq.trans (Eq.cong Succ (Nat.addComm m n)) (Eq.sym (Nat.addSucc n m))

theorem Nat.addAssoc: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a + b) + c = a + (b + c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.cong Succ (Nat.addAssoc a b c)

theorem Nat.mulZero: (n: Nat) -> n * 0 = 0
  | Zero => rfl
  | Succ n => Nat.mulZero n

theorem Nat.mulOne: (n: Nat) -> n * 1 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.mulOne n)

theorem Nat.mulSucc: (n: Nat) -> (m: Nat) -> n * Succ m = n + n * m
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Eq.trans (Eq.cong (t => m + t) (Nat.mulSucc n m)) (Eq.trans (Eq.sym (Nat.addAssoc m n (n * m))) (Eq.trans (Eq.cong (t => t + n * m) (Nat.addComm m n)) (Nat.addAssoc n m (n * m)))))

theorem Nat.mulComm: (n: Nat) -> (m: Nat) -> n * m = m * n
  | Zero, m => Eq.sym (Nat.mulZero m)
  | Succ n, m => Eq.trans (Eq.cong (t => m + t) (Nat.mulComm n m)) (Eq.sym (Nat.mulSucc m n))

theorem Nat.mulDistribRight: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a + b) * c = a * c + b * c
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Eq.cong (t => c + t) (Nat.mulDistribRight a b c)) (Eq.sym (Nat.addAssoc c (a * c) (b * c)))

theorem Nat.mulAssoc: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a * b) * c = a * (b * c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Nat.mulDistribRight b (a * b) c) (Eq.cong (t => b * c + t) (Nat.mulAssoc a b c))

-- Addition laws, after Lean's core: case analysis on the constructors plus
-- lemmas about `Int.subNatNat`.
theorem Int.subNatNatZeroRight: (m: Nat) -> Int.subNatNat m 0 = OfNat m
  | Zero   => rfl
  | Succ m => rfl

theorem Int.subNatNatFromSucc (m: Nat) (n: Nat): (t: Nat) ->
    Int.subNatNatFrom (Succ m) (Succ n) t = Int.subNatNatFrom m n t
  | Zero   => rfl
  | Succ t => rfl

theorem Int.subNatNatSucc (m: Nat) (n: Nat): Int.subNatNat (Succ m) (Succ n) = Int.subNatNat m n := Int.subNatNatFromSucc m n (n - m)

theorem Int.addZero: (a: Int) -> Int.add a (OfNat 0) = a
  | OfNat m   => Eq.cong OfNat (Nat.addZero m)
  | NegSucc m => rfl

theorem Int.zeroAdd: (a: Int) -> Int.add (OfNat 0) a = a
  | OfNat m   => rfl
  | NegSucc m => rfl

theorem Int.addComm: (a: Int) -> (b: Int) -> Int.add a b = Int.add b a
  | OfNat m,   OfNat n   => Eq.cong OfNat (Nat.addComm m n)
  | OfNat m,   NegSucc n => rfl
  | NegSucc m, OfNat n   => rfl
  | NegSucc m, NegSucc n => Eq.cong (t => NegSucc (Succ t)) (Nat.addComm m n)

-- Adding a natural number to a difference.
theorem Int.ofNatAddSubNatNat (k: Nat): (m: Nat) -> (n: Nat) ->
    Int.add (OfNat k) (Int.subNatNat m n) = Int.subNatNat (m + k) n
  | Zero,   Zero   =>
    Eq.trans (Eq.cong OfNat (Nat.addZero k)) (Eq.sym (Int.subNatNatZeroRight k))
  | Zero,   Succ n => rfl
  | Succ m, Zero   =>
    Eq.trans (Eq.cong OfNat (Eq.trans (Nat.addSucc k m) (Eq.cong Succ (Nat.addComm k m))))
             (Eq.sym (Int.subNatNatZeroRight (Succ (m + k))))
  | Succ m, Succ n =>
    Eq.trans (Eq.cong (Int.add (OfNat k)) (Int.subNatNatSucc m n))
      (Eq.trans (Int.ofNatAddSubNatNat k m n) (Eq.sym (Int.subNatNatSucc (m + k) n)))

theorem Int.subNatNatAddOfNat (k: Nat) (m: Nat) (n: Nat):
    Int.add (Int.subNatNat m n) (OfNat k) = Int.subNatNat (m + k) n :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (OfNat k)) (Int.ofNatAddSubNatNat k m n)

-- Adding a negative number to a difference.
theorem Int.negSuccAddSubNatNat (k: Nat): (m: Nat) -> (n: Nat) ->
    Int.add (NegSucc k) (Int.subNatNat m n) = Int.subNatNat m (Succ (n + k))
  | Zero,   Zero   => rfl
  | Zero,   Succ n => Eq.cong (t => NegSucc (Succ t)) (Nat.addComm k n)
  | Succ m, Zero   => rfl
  | Succ m, Succ n =>
    Eq.trans (Eq.cong (Int.add (NegSucc k)) (Int.subNatNatSucc m n))
      (Eq.trans (Int.negSuccAddSubNatNat k m n) (Eq.sym (Int.subNatNatSucc m (Succ (n + k)))))

theorem Int.subNatNatAddNegSucc (k: Nat) (m: Nat) (n: Nat):
    Int.add (Int.subNatNat m n) (NegSucc k) = Int.subNatNat m (Succ (n + k)) :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (NegSucc k)) (Int.negSuccAddSubNatNat k m n)

theorem Int.addAssoc: (a: Int) -> (b: Int) -> (c: Int) ->
    Int.add (Int.add a b) c = Int.add a (Int.add b c)
  | OfNat a,   OfNat b,   OfNat c   => Eq.cong OfNat (Nat.addAssoc a b c)
  | OfNat a,   OfNat b,   NegSucc c =>
    Eq.trans (Eq.cong (t => Int.subNatNat t (Succ c)) (Nat.addComm a b))
             (Eq.sym (Int.ofNatAddSubNatNat a b (Succ c)))
  | OfNat a,   NegSucc b, OfNat c   =>
    Eq.trans (Int.subNatNatAddOfNat c a (Succ b))
      (Eq.trans (Eq.cong (t => Int.subNatNat t (Succ b)) (Nat.addComm a c))
                (Eq.sym (Int.ofNatAddSubNatNat a c (Succ b))))
  | NegSucc a, OfNat b,   OfNat c   => Int.subNatNatAddOfNat c b (Succ a)
  | OfNat a,   NegSucc b, NegSucc c => Int.subNatNatAddNegSucc c a (Succ b)
  | NegSucc a, OfNat b,   NegSucc c =>
    Eq.trans (Int.subNatNatAddNegSucc c b (Succ a))
      (Eq.trans (Eq.cong (t => Int.subNatNat b (Succ (Succ t))) (Nat.addComm a c))
                (Eq.sym (Int.negSuccAddSubNatNat a b (Succ c))))
  | NegSucc a, NegSucc b, OfNat c   =>
    Eq.trans (Eq.cong (t => Int.subNatNat c (Succ (Succ t))) (Nat.addComm a b))
             (Eq.sym (Int.negSuccAddSubNatNat a c (Succ b)))
  | NegSucc a, NegSucc b, NegSucc c =>
    Eq.trans (Eq.cong (t => NegSucc (Succ (Succ t))) (Nat.addAssoc a b c))
             (Eq.cong (t => NegSucc (Succ t)) (Eq.sym (Nat.addSucc a (b + c))))

theorem Nat.oneMul (n: Nat): 1 * n = n := Nat.addZero n

-- `Int` multiplication by signs and sizes: `a * b` has `a`'s size times
-- `b`'s, negated when exactly one of them is negative.
def Bool.xor: Bool -> Bool -> Bool
  | False, b => b
  | True,  b => !b

theorem Bool.xorAssoc: (a: Bool) -> (b: Bool) -> (c: Bool) -> Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c)
  | False, b,     c     => rfl
  | True,  False, c     => rfl
  | True,  True,  False => rfl
  | True,  True,  True  => rfl

def Int.isNeg: Int -> Bool
  | OfNat n   => False
  | NegSucc n => True

-- `k`, negated if `neg`.
def Int.signed: Bool -> Nat -> Int
  | False, k => OfNat k
  | True,  k => Int.neg (OfNat k)

theorem Int.mulSigned: (a: Int) -> (b: Int) ->
    Int.mul a b = Int.signed (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.natAbs a * Int.natAbs b)
  | OfNat m,   OfNat n   => rfl
  | OfNat m,   NegSucc n => rfl
  | NegSucc m, OfNat n   => rfl
  | NegSucc m, NegSucc n => rfl

theorem Int.signedMulLeft: (s: Bool) -> (k: Nat) -> (c: Int) ->
    Int.mul (Int.signed s k) c = Int.signed (Bool.xor s (Int.isNeg c)) (k * Int.natAbs c)
  | False, k,      c         => Int.mulSigned (OfNat k) c
  | True,  Zero,   OfNat n   => rfl
  | True,  Zero,   NegSucc n => rfl
  | True,  Succ j, c         => Int.mulSigned (NegSucc j) c

theorem Int.signedMulRight: (a: Int) -> (s: Bool) -> (k: Nat) ->
    Int.mul a (Int.signed s k) = Int.signed (Bool.xor (Int.isNeg a) s) (Int.natAbs a * k)
  | a,         False, k      => Int.mulSigned a (OfNat k)
  | a,         True,  Succ j => Int.mulSigned a (NegSucc j)
  | OfNat n,   True,  Zero   => rewrite Nat.mulZero n in rfl
  | NegSucc n, True,  Zero   => rewrite Nat.mulZero (Succ n) in rfl

theorem Int.mulAssoc (a: Int) (b: Int) (c: Int): Int.mul (Int.mul a b) c = Int.mul a (Int.mul b c) :=
  Eq.trans (Eq.cong (t => Int.mul t c) (Int.mulSigned a b))
    (Eq.trans (Int.signedMulLeft (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.natAbs a * Int.natAbs b) c)
      (Eq.trans
        (Eq.trans (Eq.cong (s => Int.signed s ((Int.natAbs a * Int.natAbs b) * Int.natAbs c)) (Bool.xorAssoc (Int.isNeg a) (Int.isNeg b) (Int.isNeg c)))
          (Eq.cong (Int.signed (Bool.xor (Int.isNeg a) (Bool.xor (Int.isNeg b) (Int.isNeg c)))) (Nat.mulAssoc (Int.natAbs a) (Int.natAbs b) (Int.natAbs c))))
        (Eq.sym (Eq.trans (Eq.cong (Int.mul a) (Int.mulSigned b c))
          (Int.signedMulRight a (Bool.xor (Int.isNeg b) (Int.isNeg c)) (Int.natAbs b * Int.natAbs c))))))

theorem Int.oneMul: (a: Int) -> Int.mul (OfNat 1) a = a
  | OfNat n   => Eq.cong OfNat (Nat.addZero n)
  | NegSucc n => Eq.cong NegSucc (Nat.addZero n)

theorem Int.mulOne: (a: Int) -> Int.mul a (OfNat 1) = a
  | OfNat n   => Eq.cong OfNat (Nat.mulOne n)
  | NegSucc n => Eq.cong NegSucc (Nat.mulOne n)

