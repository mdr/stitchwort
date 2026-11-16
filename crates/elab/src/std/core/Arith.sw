--| Arithmetic laws for `Nat` and `Int` (associativity,
--| commutativity, distributivity), with [`Bool.xor`] and the sign lemmas
--| [`Int.mulAssoc`] uses.
-- Loaded with the core: `Nat.instAdd`, `Nat.instMul`, `Int.instAdd` and
-- `Int.instMul` need their laws, and `+` and `*` go through those instances
-- (docs/proposals/prelude-slim.md §2.1).

-- Arithmetic laws (docs/proposals/interfaces.md §5.13, D187): what the
-- `Add` and `Mul` instances for `Nat` and `Int` need. They come before the
-- instances, and their `+` and `*` are the primitive operations.

theorem Nat.addZero ∀ (n: Nat): n + 0 = n := match n with
  | Zero => byComputing
  | Succ n => Eq.cong Succ (Nat.addZero n)

theorem Nat.addSucc ∀ (n m: Nat): n + Succ m = Succ (n + m) := match n with
  | Zero => byComputing
  | Succ n => Eq.cong Succ (Nat.addSucc n m)

theorem Nat.addComm ∀ (m n: Nat): m + n = n + m := match m with
  | Zero => (Nat.addZero n).flipped
  | Succ m => Eq.trans (Eq.cong Succ (Nat.addComm m n)) (Nat.addSucc n m).flipped

theorem Nat.addAssoc ∀ (a b c: Nat): (a + b) + c = a + (b + c) := match a with
  | Zero => byComputing
  | Succ a => Eq.cong Succ (Nat.addAssoc a b c)

theorem Nat.mulZero ∀ (n: Nat): n * 0 = 0 := match n with
  | Zero => byComputing
  | Succ n => Nat.mulZero n

theorem Nat.mulOne ∀ (n: Nat): n * 1 = n := match n with
  | Zero => byComputing
  | Succ n => Eq.cong Succ (Nat.mulOne n)

theorem Nat.mulSucc ∀ (n m: Nat): n * Succ m = n + n * m := match n with
  | Zero => byComputing
  | Succ n =>
    Eq.cong Succ
      (calc m + n * Succ m
        _ = m + (n + n * m) := Eq.cong (t => m + t) (Nat.mulSucc n m)
        _ = (m + n) + n * m := Eq.flipped (Nat.addAssoc m n (n * m))
        _ = (n + m) + n * m := Eq.cong (t => t + n * m) (Nat.addComm m n)
        _ = n + (m + n * m) := Nat.addAssoc n m (n * m))

theorem Nat.mulComm ∀ (n m: Nat): n * m = m * n := match n with
  | Zero => (Nat.mulZero m).flipped
  | Succ n => Eq.trans (Eq.cong (t => m + t) (Nat.mulComm n m)) (Nat.mulSucc m n).flipped

theorem Nat.mulDistribRight ∀ (a b c: Nat): (a + b) * c = a * c + b * c := match a with
  | Zero => byComputing
  | Succ a => Eq.trans (Eq.cong (t => c + t) (Nat.mulDistribRight a b c)) (Eq.flipped (Nat.addAssoc c (a * c) (b * c)))

theorem Nat.mulAssoc ∀ (a b c: Nat): (a * b) * c = a * (b * c) := match a with
  | Zero => byComputing
  | Succ a => Eq.trans (Nat.mulDistribRight b (a * b) c) (Eq.cong (t => b * c + t) (Nat.mulAssoc a b c))

-- Addition laws, after Lean's core: case analysis on the constructors plus
-- lemmas about `Int.subNatNat`.
theorem Int.subNatNatZeroRight ∀ (m: Nat): Int.subNatNat m 0 = OfNat m := match m with
  | Zero => byComputing
  | Succ m => byComputing

theorem Int.subNatNatFromSucc ∀ (m n t: Nat): Int.subNatNatFrom (Succ m) (Succ n) t = Int.subNatNatFrom m n t :=
  match t with
    | Zero => byComputing
    | Succ t => byComputing

theorem Int.subNatNatSucc ∀ (m n: Nat): Int.subNatNat (Succ m) (Succ n) = Int.subNatNat m n :=
  Int.subNatNatFromSucc m n (n - m)

theorem Int.addZero ∀ (a: Int): Int.add a (OfNat 0) = a := match a with
  | OfNat m => Eq.cong OfNat (Nat.addZero m)
  | NegSucc m => byComputing

theorem Int.zeroAdd ∀ (a: Int): Int.add (OfNat 0) a = a := match a with
  | OfNat m => byComputing
  | NegSucc m => byComputing

theorem Int.addComm ∀ (a b: Int): Int.add a b = Int.add b a := match a, b with
  | OfNat m, OfNat n => Eq.cong OfNat (Nat.addComm m n)
  | OfNat m, NegSucc n => byComputing
  | NegSucc m, OfNat n => byComputing
  | NegSucc m, NegSucc n => Eq.cong (t => NegSucc (Succ t)) (Nat.addComm m n)

--| Adding a natural number to a difference.
theorem Int.ofNatAddSubNatNat ∀ (k m n: Nat): Int.add (OfNat k) (Int.subNatNat m n) = Int.subNatNat (m + k) n :=
  match m, n with
    | Zero, Zero => Eq.trans (Eq.cong OfNat (Nat.addZero k)) (Int.subNatNatZeroRight k).flipped
    | Zero, Succ n => byComputing
    | Succ m, Zero =>
      calc Int.add (OfNat k) (Int.subNatNat (Succ m) 0)
        _ = OfNat (Succ (k + m)) := Eq.cong OfNat (Nat.addSucc k m)
        _ = OfNat (Succ (m + k)) := Eq.cong OfNat (Eq.cong Succ (Nat.addComm k m))
        _ = Int.subNatNat (Succ (m + k)) 0 := Eq.flipped (Int.subNatNatZeroRight (Succ (m + k)))
    | Succ m, Succ n =>
      calc Int.add (OfNat k) (Int.subNatNat (Succ m) (Succ n))
        _ = Int.add (OfNat k) (Int.subNatNat m n) := Eq.cong (Int.add (OfNat k)) (Int.subNatNatSucc m n)
        _ = Int.subNatNat (m + k) n := Int.ofNatAddSubNatNat k m n
        _ = Int.subNatNat (Succ (m + k)) (Succ n) := Eq.flipped (Int.subNatNatSucc (m + k) n)

theorem Int.subNatNatAddOfNat ∀ (k m n: Nat): Int.add (Int.subNatNat m n) (OfNat k) = Int.subNatNat (m + k) n :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (OfNat k)) (Int.ofNatAddSubNatNat k m n)

--| Adding a negative number to a difference.
theorem Int.negSuccAddSubNatNat ∀ (k m n: Nat):
    Int.add (NegSucc k) (Int.subNatNat m n) = Int.subNatNat m (Succ (n + k)) :=
  match m, n with
    | Zero, Zero => byComputing
    | Zero, Succ n => Eq.cong (t => NegSucc (Succ t)) (Nat.addComm k n)
    | Succ m, Zero => byComputing
    | Succ m, Succ n =>
      calc Int.add (NegSucc k) (Int.subNatNat (Succ m) (Succ n))
        _ = Int.add (NegSucc k) (Int.subNatNat m n) := Eq.cong (Int.add (NegSucc k)) (Int.subNatNatSucc m n)
        _ = Int.subNatNat m (Succ (n + k)) := Int.negSuccAddSubNatNat k m n
        _ = Int.subNatNat (Succ m) (Succ (Succ (n + k))) := Eq.flipped (Int.subNatNatSucc m (Succ (n + k)))

theorem Int.subNatNatAddNegSucc ∀ (k m n: Nat):
    Int.add (Int.subNatNat m n) (NegSucc k) = Int.subNatNat m (Succ (n + k)) :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (NegSucc k)) (Int.negSuccAddSubNatNat k m n)

theorem Int.addAssoc ∀ (a b c: Int): Int.add (Int.add a b) c = Int.add a (Int.add b c) := match a, b, c with
  | OfNat a, OfNat b, OfNat c => Eq.cong OfNat (Nat.addAssoc a b c)
  | OfNat a, OfNat b, NegSucc c =>
    Eq.trans
      (Eq.cong (t => Int.subNatNat t (Succ c)) (Nat.addComm a b))
      (Eq.flipped (Int.ofNatAddSubNatNat a b (Succ c)))
  | OfNat a, NegSucc b, OfNat c =>
    calc Int.add (Int.subNatNat a (Succ b)) (OfNat c)
      _ = Int.subNatNat (a + c) (Succ b) := Int.subNatNatAddOfNat c a (Succ b)
      _ = Int.subNatNat (c + a) (Succ b) := Eq.cong (t => Int.subNatNat t (Succ b)) (Nat.addComm a c)
      _ = Int.add (OfNat a) (Int.subNatNat c (Succ b)) := Eq.flipped (Int.ofNatAddSubNatNat a c (Succ b))
  | NegSucc a, OfNat b, OfNat c => Int.subNatNatAddOfNat c b (Succ a)
  | OfNat a, NegSucc b, NegSucc c => Int.subNatNatAddNegSucc c a (Succ b)
  | NegSucc a, OfNat b, NegSucc c =>
    calc Int.add (Int.subNatNat b (Succ a)) (NegSucc c)
      _ = Int.subNatNat b (Succ (Succ (a + c))) := Int.subNatNatAddNegSucc c b (Succ a)
      _ = Int.subNatNat b (Succ (Succ (c + a))) :=
        Eq.cong (t => Int.subNatNat b (Succ (Succ t))) (Nat.addComm a c)
      _ = Int.add (NegSucc a) (Int.subNatNat b (Succ c)) := Eq.flipped (Int.negSuccAddSubNatNat a b (Succ c))
  | NegSucc a, NegSucc b, OfNat c =>
    Eq.trans
      (Eq.cong (t => Int.subNatNat c (Succ (Succ t))) (Nat.addComm a b))
      (Eq.flipped (Int.negSuccAddSubNatNat a c (Succ b)))
  | NegSucc a, NegSucc b, NegSucc c =>
    Eq.trans
      (Eq.cong (t => NegSucc (Succ (Succ t))) (Nat.addAssoc a b c))
      (Eq.cong (t => NegSucc (Succ t)) (Eq.flipped (Nat.addSucc a (b + c))))

theorem Nat.oneMul ∀ (n: Nat): 1 * n = n := Nat.addZero n

--| Exclusive or: `True` when exactly one of `x` and `y` is.
def Bool.xor: (x: Bool) → (y: Bool) → Bool
  | False, b => b
  | True, b => ¬b

theorem Bool.xorAssoc ∀ (a b c: Bool): Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := match a, b, c with
  | False, b, c => byComputing
  | True, False, c => byComputing
  | True, True, False => byComputing
  | True, True, True => byComputing

--| Whether the integer is below zero.
def Int.isNeg: (x: Int) → Bool
  | OfNat n => False
  | NegSucc n => True

--| `n`, negated if `negative`.
def Int.signed: (negative: Bool) → (n: Nat) → Int
  | False, k => OfNat k
  | True, k => Int.neg (OfNat k)

--| `Int` multiplication by signs and sizes: `a * b` has `a`'s size times
--| `b`'s, negated when exactly one of them is negative.
theorem Int.mulSigned ∀ (a b: Int):
    Int.mul a b = Int.signed (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.natAbs a * Int.natAbs b) :=
  match a, b with
    | OfNat m, OfNat n => byComputing
    | OfNat m, NegSucc n => byComputing
    | NegSucc m, OfNat n => byComputing
    | NegSucc m, NegSucc n => byComputing

theorem Int.signedMulLeft ∀ (s: Bool) (k: Nat) (c: Int):
    Int.mul (Int.signed s k) c = Int.signed (Bool.xor s (Int.isNeg c)) (k * Int.natAbs c) :=
  match s, k, c with
    | False, k, c => Int.mulSigned (OfNat k) c
    | True, Zero, OfNat n => byComputing
    | True, Zero, NegSucc n => byComputing
    | True, Succ j, c => Int.mulSigned (NegSucc j) c

theorem Int.signedMulRight ∀ (a: Int) (s: Bool) (k: Nat):
    Int.mul a (Int.signed s k) = Int.signed (Bool.xor (Int.isNeg a) s) (Int.natAbs a * k) :=
  match a, s, k with
    | a, False, k => Int.mulSigned a (OfNat k)
    | a, True, Succ j => Int.mulSigned a (NegSucc j)
    | OfNat n, True, Zero => rewrite Nat.mulZero n then byComputing
    | NegSucc n, True, Zero => rewrite Nat.mulZero (Succ n) then byComputing

theorem Int.mulAssoc ∀ (a b c: Int): Int.mul (Int.mul a b) c = Int.mul a (Int.mul b c) :=
  calc Int.mul (Int.mul a b) c
    _ = Int.mul (Int.signed (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.natAbs a * Int.natAbs b)) c :=
      Eq.cong (t => Int.mul t c) (Int.mulSigned a b)
    _ = Int.signed (Bool.xor (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.isNeg c))
        ((Int.natAbs a * Int.natAbs b) * Int.natAbs c) :=
      Int.signedMulLeft (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.natAbs a * Int.natAbs b) c
    _ = Int.signed (Bool.xor (Int.isNeg a) (Bool.xor (Int.isNeg b) (Int.isNeg c)))
        ((Int.natAbs a * Int.natAbs b) * Int.natAbs c) :=
      Eq.cong
        (s => Int.signed s ((Int.natAbs a * Int.natAbs b) * Int.natAbs c))
        (Bool.xorAssoc (Int.isNeg a) (Int.isNeg b) (Int.isNeg c))
    _ = Int.signed (Bool.xor (Int.isNeg a) (Bool.xor (Int.isNeg b) (Int.isNeg c)))
        (Int.natAbs a * (Int.natAbs b * Int.natAbs c)) :=
      Eq.cong
        (Int.signed (Bool.xor (Int.isNeg a) (Bool.xor (Int.isNeg b) (Int.isNeg c))))
        (Nat.mulAssoc (Int.natAbs a) (Int.natAbs b) (Int.natAbs c))
    _ = Int.mul a (Int.signed (Bool.xor (Int.isNeg b) (Int.isNeg c)) (Int.natAbs b * Int.natAbs c)) :=
      Eq.flipped
        (Int.signedMulRight a (Bool.xor (Int.isNeg b) (Int.isNeg c)) (Int.natAbs b * Int.natAbs c))
    _ = Int.mul a (Int.mul b c) := Eq.flipped (Eq.cong (Int.mul a) (Int.mulSigned b c))

theorem Int.oneMul ∀ (a: Int): Int.mul (OfNat 1) a = a := match a with
  | OfNat n => Eq.cong OfNat (Nat.addZero n)
  | NegSucc n => Eq.cong NegSucc (Nat.addZero n)

theorem Int.mulOne ∀ (a: Int): Int.mul a (OfNat 1) = a := match a with
  | OfNat n => Eq.cong OfNat (Nat.mulOne n)
  | NegSucc n => Eq.cong NegSucc (Nat.mulOne n)
