-- Bitwise operations on `Nat`: shifting right and left, testing a bit, and
-- XOR, AND and OR, with the lemmas that relate them to division by powers
-- of 2 and to each bit.

-- Regrouping `(q * d + s) * 2 + t`, for dividing by 2 and then by `d`.
theorem Nat.regroupHalf (q: Nat) (d: Nat) (s: Nat) (t: Nat): (q * d + s) * 2 + t = q * (d * 2) + (s * 2 + t) := ring

-- Halving and then dividing by `2 ^ k` is dividing by `2 ^ (k + 1)`.
theorem Nat.halfDivPow (n: Nat) (k: Nat): n / 2 / Nat.pow 2 k = n / Nat.pow 2 (Succ k) :=
  let power := Nat.pow 2 k
  let positive := Nat.nonzeroOfPos power (Nat.powSuccPos 1 k)
  Eq.sym
    (Nat.divUnique n (Nat.pow 2 (Succ k)) (n / 2 / power) (n / 2 % power * 2 + n % 2)
      (omega [Nat.modLess (n / 2) power positive, Nat.modLess n 2 (Nat.succNotZero 1)])
      (Eq.trans (Nat.divModEq n 2 (Nat.succNotZero 1))
        (Eq.trans (Eq.cong (half => half * 2 + n % 2) (Nat.divModEq (n / 2) power positive))
          (Nat.regroupHalf (n / 2 / power) power (n / 2 % power) (n % 2)))))

-- `n` shifted right by `count` bits: `n / 2 ^ count` (`Nat.shiftRightDiv`),
-- in at most one step per bit of `n`.
def Nat.shiftRight: (n: Nat) → (count: Nat) → Nat
  | Zero, count => 0
  | Succ n, Zero => Succ n
  | Succ n, Succ count => Nat.shiftRight (Succ n / 2) count

theorem Nat.shiftRightNone: (n: Nat) → Nat.shiftRight n 0 = n
  | Zero => rfl
  | Succ n => rfl

theorem Nat.shiftRightSucc: (n: Nat) → (count: Nat) → Nat.shiftRight n (Succ count) = Nat.shiftRight (n / 2) count
  | Zero, count => rfl
  | Succ n, count => rfl

theorem Nat.shiftRightDiv: (n: Nat) → (count: Nat) → Nat.shiftRight n count = n / Nat.pow 2 count
  | n, Zero => rewrite Nat.shiftRightNone n in Eq.sym (Nat.divOne n)
  | n, Succ count =>
    rewrite Nat.shiftRightSucc n count, Nat.shiftRightDiv (n / 2) count in
      Nat.halfDivPow n count

-- Bit `i` of `n`, counting from 0 for the lowest: whether `n / 2 ^ i` is odd.
def Nat.testBit (n: Nat) (i: Nat): Bool := Nat.shiftRight n i % 2 == 1

theorem Nat.testBitDiv (n: Nat) (i: Nat): Nat.testBit n i = (n / Nat.pow 2 i % 2 == 1) :=
  Eq.cong (shifted => shifted % 2 == 1) (Nat.shiftRightDiv n i)

theorem Nat.testBitSucc (n: Nat) (i: Nat): Nat.testBit n (Succ i) = Nat.testBit (n / 2) i :=
  Eq.cong (shifted => shifted % 2 == 1) (Nat.shiftRightSucc n i)

-- Halving both numbers makes their sum smaller, unless both are 0.
theorem Nat.halvesLess (m: Nat) (n: Nat) (some: Nat.leq (m + n) 0 = False): m / 2 + n / 2 < m + n :=
  omega [Nat.divMulLe m 2 (Nat.succNotZero 1), Nat.divMulLe n 2 (Nat.succNotZero 1), Nat.leqFalse (m + n) 0 some]

-- The bitwise exclusive or: each bit of `Nat.xor m n` is set when exactly
-- one of `m` and `n` has it set (`Nat.testBitXor`).
def Nat.xor (m: Nat) (n: Nat): Nat
    decreasing m + n
:=
  if some: Nat.leq (m + n) 0 = False
  then (m + n) % 2 + Nat.xor (m / 2) (n / 2) [decreasing := Nat.halvesLess m n some] * 2
  else 0

theorem Nat.xorZero (m: Nat) (n: Nat) (none: Nat.leq (m + n) 0 = True): Nat.xor m n = 0 :=
  rewrite Nat.xor.unfold m n in
  rewrite none in
  rfl

theorem Nat.xorSome (m: Nat) (n: Nat) (some: Nat.leq (m + n) 0 = False): Nat.xor m n = (m + n) % 2 + Nat.xor (m / 2) (n / 2) * 2 :=
  rewrite Nat.xor.unfold m n in
  rewrite some in
  rfl

-- The lowest bit, and the rest.
theorem Nat.xorMod (m: Nat) (n: Nat): Nat.xor m n % 2 = (m + n) % 2 :=
  match some: Nat.leq (m + n) 0 with
    | False =>
      rewrite Nat.xorSome m n some, Nat.modAddMul ((m + n) % 2) (Nat.xor (m / 2) (n / 2)) 2 in
        Nat.modMod (m + n) 2
    | True => rewrite Nat.xorZero m n some, (omega: m + n = 0) in rfl

theorem Nat.xorDiv (m: Nat) (n: Nat): Nat.xor m n / 2 = Nat.xor (m / 2) (n / 2) :=
  match some: Nat.leq (m + n) 0 with
    | False =>
      rewrite Nat.xorSome m n some, Nat.divAddMul ((m + n) % 2) (Nat.xor (m / 2) (n / 2)) 2,
        Nat.divSmall ((m + n) % 2) 2 (Nat.modLess (m + n) 2 (Nat.succNotZero 1)) in rfl
    | True => rewrite Nat.xorZero m n some, (omega: m = 0), (omega: n = 0) in rfl

-- Whether the sum of two bits is odd is their exclusive or.
theorem Nat.oddSumBits: (m: Nat) → (n: Nat) → m < 2 → n < 2 → ((m + n) % 2 == 1) = Bool.xor (m == 1) (n == 1)
  | Zero, Zero, small, alsoSmall => rfl
  | Zero, Succ Zero, small, alsoSmall => rfl
  | Succ Zero, Zero, small, alsoSmall => rfl
  | Succ Zero, Succ Zero, small, alsoSmall => rfl
  | Succ (Succ m), n, small, alsoSmall => Void.exfalso (omega)
  | m, Succ (Succ n), small, alsoSmall => Void.exfalso (omega)

theorem Nat.oddSum (m: Nat) (n: Nat): ((m + n) % 2 == 1) = Bool.xor (m % 2 == 1) (n % 2 == 1) :=
  rewrite Eq.sym (Nat.addModMod m n 2), Eq.sym (Nat.modAddMod m (n % 2) 2) in
    Nat.oddSumBits (m % 2) (n % 2) (Nat.modLess m 2 (Nat.succNotZero 1)) (Nat.modLess n 2 (Nat.succNotZero 1))

-- Each bit of `Nat.xor m n` is the exclusive or of the bits of `m` and `n`.
theorem Nat.testBitXor: (i: Nat) → (m: Nat) → (n: Nat) → Nat.testBit (Nat.xor m n) i = Bool.xor (Nat.testBit m i) (Nat.testBit n i)
  | Zero, m, n =>
    rewrite Nat.shiftRightNone (Nat.xor m n), Nat.shiftRightNone m, Nat.shiftRightNone n, Nat.xorMod m n in
      Nat.oddSum m n
  | Succ i, m, n =>
    rewrite Nat.testBitSucc (Nat.xor m n) i, Nat.xorDiv m n, Nat.testBitSucc m i, Nat.testBitSucc n i in
      Nat.testBitXor i (m / 2) (n / 2)

-- Two remainders by 2 that are odd together are equal.
theorem Nat.bitsEqual: (m: Nat) → (n: Nat) → m < 2 → n < 2 → (m == 1) = (n == 1) → m = n
  | Zero, Zero, small, alsoSmall, same => rfl
  | Succ Zero, Succ Zero, small, alsoSmall, same => rfl
  | Zero, Succ Zero, small, alsoSmall, same => Void.exfalso (Bool.falseNotTrue same)
  | Succ Zero, Zero, small, alsoSmall, same => Void.exfalso (Bool.trueNotFalse same)
  | Succ (Succ m), n, small, alsoSmall, same => Void.exfalso (omega)
  | m, Succ (Succ n), small, alsoSmall, same => Void.exfalso (omega)

-- Numbers with the same bits are equal.
theorem Nat.eqOfTestBit (m: Nat) (n: Nat) (same: (i: Nat) → Nat.testBit m i = Nat.testBit n i): m = n
    decreasing m + n
:=
  match some: Nat.leq (m + n) 0 with
    | True => omega
    | False =>
      let low := Nat.bitsEqual (m % 2) (n % 2) (Nat.modLess m 2 (Nat.succNotZero 1)) (Nat.modLess n 2 (Nat.succNotZero 1))
        (rewrite Nat.shiftRightNone m, Nat.shiftRightNone n at same 0)
      let high :=
        Nat.eqOfTestBit (m / 2) (n / 2)
          (i => Eq.trans (Eq.sym (Nat.testBitSucc m i)) (Eq.trans (same (Succ i)) (Nat.testBitSucc n i))) [decreasing := Nat.halvesLess m n some]
      omega [Nat.divModEq m 2 (Nat.succNotZero 1), Nat.divModEq n 2 (Nat.succNotZero 1), low, high]

theorem Nat.xorExample: Nat.xor 2024 43690 = 44354 := rfl

-- Whether the product, and the sum plus the product, of two bits is odd:
-- their `and` and their `or`.
theorem Nat.oddProductBits: (m: Nat) → (n: Nat) → m < 2 → n < 2 → (m * n % 2 == 1) = (m == 1 ∧ n == 1)
  | Zero, Zero, small, alsoSmall => rfl
  | Zero, Succ Zero, small, alsoSmall => rfl
  | Succ Zero, Zero, small, alsoSmall => rfl
  | Succ Zero, Succ Zero, small, alsoSmall => rfl
  | Succ (Succ m), n, small, alsoSmall => Void.exfalso (omega)
  | m, Succ (Succ n), small, alsoSmall => Void.exfalso (omega)

theorem Nat.oddEitherBits: (m: Nat) → (n: Nat) → m < 2 → n < 2 → ((m + n + m * n) % 2 == 1) = (m == 1 ∨ n == 1)
  | Zero, Zero, small, alsoSmall => rfl
  | Zero, Succ Zero, small, alsoSmall => rfl
  | Succ Zero, Zero, small, alsoSmall => rfl
  | Succ Zero, Succ Zero, small, alsoSmall => rfl
  | Succ (Succ m), n, small, alsoSmall => Void.exfalso (omega)
  | m, Succ (Succ n), small, alsoSmall => Void.exfalso (omega)

theorem Nat.oddProduct (m: Nat) (n: Nat): (m * n % 2 == 1) = (m % 2 == 1 ∧ n % 2 == 1) :=
  rewrite Eq.sym (Nat.mulModMod m n 2), Eq.sym (Nat.modMulMod m (n % 2) 2) in
    Nat.oddProductBits (m % 2) (n % 2) (Nat.modLess m 2 (Nat.succNotZero 1)) (Nat.modLess n 2 (Nat.succNotZero 1))

theorem Nat.oddEither (m: Nat) (n: Nat): ((m % 2 + n % 2 + m % 2 * (n % 2)) % 2 == 1) = (m % 2 == 1 ∨ n % 2 == 1) :=
  Nat.oddEitherBits (m % 2) (n % 2) (Nat.modLess m 2 (Nat.succNotZero 1)) (Nat.modLess n 2 (Nat.succNotZero 1))

-- The bitwise and: each bit of `Nat.and m n` is set when both `m` and `n`
-- have it set (`Nat.testBitAnd`).
def Nat.and (m: Nat) (n: Nat): Nat
    decreasing m + n
:=
  if some: Nat.leq (m + n) 0 = False
  then m * n % 2 + Nat.and (m / 2) (n / 2) [decreasing := Nat.halvesLess m n some] * 2
  else 0

theorem Nat.andZero (m: Nat) (n: Nat) (none: Nat.leq (m + n) 0 = True): Nat.and m n = 0 :=
  rewrite Nat.and.unfold m n in
  rewrite none in
  rfl

theorem Nat.andSome (m: Nat) (n: Nat) (some: Nat.leq (m + n) 0 = False): Nat.and m n = m * n % 2 + Nat.and (m / 2) (n / 2) * 2 :=
  rewrite Nat.and.unfold m n in
  rewrite some in
  rfl

theorem Nat.andMod (m: Nat) (n: Nat): Nat.and m n % 2 = m * n % 2 :=
  match some: Nat.leq (m + n) 0 with
    | False =>
      rewrite Nat.andSome m n some, Nat.modAddMul (m * n % 2) (Nat.and (m / 2) (n / 2)) 2 in
        Nat.modMod (m * n) 2
    | True => rewrite Nat.andZero m n some, (omega: m = 0) in rfl

theorem Nat.andDiv (m: Nat) (n: Nat): Nat.and m n / 2 = Nat.and (m / 2) (n / 2) :=
  match some: Nat.leq (m + n) 0 with
    | False =>
      rewrite Nat.andSome m n some, Nat.divAddMul (m * n % 2) (Nat.and (m / 2) (n / 2)) 2,
        Nat.divSmall (m * n % 2) 2 (Nat.modLess (m * n) 2 (Nat.succNotZero 1)) in rfl
    | True => rewrite Nat.andZero m n some, (omega: m = 0), (omega: n = 0) in rfl

theorem Nat.testBitAnd: (i: Nat) → (m: Nat) → (n: Nat) → Nat.testBit (Nat.and m n) i = (Nat.testBit m i ∧ Nat.testBit n i)
  | Zero, m, n =>
    rewrite Nat.shiftRightNone (Nat.and m n), Nat.shiftRightNone m, Nat.shiftRightNone n, Nat.andMod m n in
      Nat.oddProduct m n
  | Succ i, m, n =>
    rewrite Nat.testBitSucc (Nat.and m n) i, Nat.andDiv m n, Nat.testBitSucc m i, Nat.testBitSucc n i in
      Nat.testBitAnd i (m / 2) (n / 2)

-- The bitwise or: each bit of `Nat.or m n` is set when `m` or `n` has it
-- set (`Nat.testBitOr`).
def Nat.or (m: Nat) (n: Nat): Nat
    decreasing m + n
:=
  if some: Nat.leq (m + n) 0 = False
  then (m % 2 + n % 2 + m % 2 * (n % 2)) % 2 + Nat.or (m / 2) (n / 2) [decreasing := Nat.halvesLess m n some] * 2
  else 0

theorem Nat.orZero (m: Nat) (n: Nat) (none: Nat.leq (m + n) 0 = True): Nat.or m n = 0 :=
  rewrite Nat.or.unfold m n in
  rewrite none in
  rfl

theorem Nat.orSome (m: Nat) (n: Nat) (some: Nat.leq (m + n) 0 = False): Nat.or m n = (m % 2 + n % 2 + m % 2 * (n % 2)) % 2 + Nat.or (m / 2) (n / 2) * 2 :=
  rewrite Nat.or.unfold m n in
  rewrite some in
  rfl

theorem Nat.orMod (m: Nat) (n: Nat): Nat.or m n % 2 = (m % 2 + n % 2 + m % 2 * (n % 2)) % 2 :=
  match some: Nat.leq (m + n) 0 with
    | False =>
      rewrite Nat.orSome m n some, Nat.modAddMul ((m % 2 + n % 2 + m % 2 * (n % 2)) % 2) (Nat.or (m / 2) (n / 2)) 2 in
        Nat.modMod (m % 2 + n % 2 + m % 2 * (n % 2)) 2
    | True => rewrite Nat.orZero m n some, (omega: m = 0), (omega: n = 0) in rfl

theorem Nat.orDiv (m: Nat) (n: Nat): Nat.or m n / 2 = Nat.or (m / 2) (n / 2) :=
  match some: Nat.leq (m + n) 0 with
    | False =>
      rewrite Nat.orSome m n some, Nat.divAddMul ((m % 2 + n % 2 + m % 2 * (n % 2)) % 2) (Nat.or (m / 2) (n / 2)) 2,
        Nat.divSmall ((m % 2 + n % 2 + m % 2 * (n % 2)) % 2) 2 (Nat.modLess (m % 2 + n % 2 + m % 2 * (n % 2)) 2 (Nat.succNotZero 1)) in rfl
    | True => rewrite Nat.orZero m n some, (omega: m = 0), (omega: n = 0) in rfl

theorem Nat.testBitOr: (i: Nat) → (m: Nat) → (n: Nat) → Nat.testBit (Nat.or m n) i = (Nat.testBit m i ∨ Nat.testBit n i)
  | Zero, m, n =>
    rewrite Nat.shiftRightNone (Nat.or m n), Nat.shiftRightNone m, Nat.shiftRightNone n, Nat.orMod m n in
      Nat.oddEither m n
  | Succ i, m, n =>
    rewrite Nat.testBitSucc (Nat.or m n) i, Nat.orDiv m n, Nat.testBitSucc m i, Nat.testBitSucc n i in
      Nat.testBitOr i (m / 2) (n / 2)

-- Regrouping `n * 2 * p`, for shifting left one bit and then `count` more.
theorem Nat.regroupDouble (n: Nat) (p: Nat): n * 2 * p = n * (p * 2) := ring

-- `n` shifted left by `count` bits: `n * 2 ^ count` (`Nat.shiftLeftMul`).
def Nat.shiftLeft: (n: Nat) → (count: Nat) → Nat
  | n, Zero => n
  | n, Succ count => Nat.shiftLeft (n * 2) count

theorem Nat.shiftLeftMul: (n: Nat) → (count: Nat) → Nat.shiftLeft n count = n * Nat.pow 2 count
  | n, Zero => Eq.sym (Nat.mulOne n)
  | n, Succ count =>
    rewrite Nat.shiftLeftMul (n * 2) count in
      Nat.regroupDouble n (Nat.pow 2 count)

-- Shifting left and then right by as many bits gives the number back.
theorem Nat.shiftRightShiftLeft (n: Nat) (count: Nat): Nat.shiftRight (Nat.shiftLeft n count) count = n :=
  rewrite Nat.shiftRightDiv (Nat.shiftLeft n count) count, Nat.shiftLeftMul n count in
    Nat.divUnique (n * Nat.pow 2 count) (Nat.pow 2 count) n 0 (Nat.powSuccPos 1 count) (Eq.sym (Nat.addZero (n * Nat.pow 2 count)))

theorem Nat.andExample: Nat.and 12 10 = 8 := rfl

theorem Nat.orExample: Nat.or 12 10 = 14 := rfl

theorem Nat.shiftLeftExample: Nat.shiftLeft 3 4 = 48 := rfl

-- The remainder by `2 ^ (k + 1)`: the remainder of half by `2 ^ k`, doubled,
-- and the lowest bit.
theorem Nat.modPowSucc (n: Nat) (k: Nat): n % Nat.pow 2 (Succ k) = n / 2 % Nat.pow 2 k * 2 + n % 2 :=
  let power := Nat.pow 2 k
  let positive := Nat.nonzeroOfPos power (Nat.powSuccPos 1 k)
  Nat.modUnique n (Nat.pow 2 (Succ k)) (n / 2 / power) (n / 2 % power * 2 + n % 2)
    (omega [Nat.modLess (n / 2) power positive, Nat.modLess n 2 (Nat.succNotZero 1)])
    (Eq.trans (Nat.divModEq n 2 (Nat.succNotZero 1))
      (Eq.trans (Eq.cong (half => half * 2 + n % 2) (Nat.divModEq (n / 2) power positive))
        (Nat.regroupHalf (n / 2 / power) power (n / 2 % power) (n % 2))))

-- Two numbers with the same bits above the lowest, and the same lowest bit.
theorem Nat.xorSameHalves (whole: Nat) (other: Nat) (high: Nat) (wholeBit: Nat) (otherBit: Nat) (wholeSplit: whole = high * 2 + wholeBit)
    (otherSplit: other = high * 2 + otherBit) (same: wholeBit = otherBit): whole = other :=
  omega

-- Adding two numbers' low bits as a whole number keeps the parity of their
-- sum.
theorem Nat.xorSumParity (lowX: Nat) (lowY: Nat) (highX: Nat) (highY: Nat) (x: Nat) (y: Nat) (splitX: lowX = highX * 2 + x % 2)
    (splitY: lowY = highY * 2 + y % 2): (lowX + lowY) % 2 = (x + y) % 2 :=
  omega [
    Nat.divModEq x 2 (Nat.succNotZero 1),
    Nat.divModEq y 2 (Nat.succNotZero 1),
    Nat.divModEq (lowX + lowY) 2 (Nat.succNotZero 1),
    Nat.divModEq (x + y) 2 (Nat.succNotZero 1),
    Nat.modLess x 2 (Nat.succNotZero 1),
    Nat.modLess y 2 (Nat.succNotZero 1),
    Nat.modLess (lowX + lowY) 2 (Nat.succNotZero 1),
    Nat.modLess (x + y) 2 (Nat.succNotZero 1)
  ]

-- The low `k` bits of an XOR are the XOR of the low `k` bits.
theorem Nat.xorModPow: (k: Nat) → (x: Nat) → (y: Nat) → Nat.xor x y % Nat.pow 2 k = Nat.xor (x % Nat.pow 2 k) (y % Nat.pow 2 k)
  | Zero, x, y =>
    rewrite (omega: x % 1 = 0), (omega: y % 1 = 0), Nat.xorZero 0 0 rfl in
      (omega: Nat.xor x y % 1 = 0)
  | Succ k, x, y =>
    let lowX := x % Nat.pow 2 (Succ k)
    let lowY := y % Nat.pow 2 (Succ k)
    let splitX := Nat.modPowSucc x k
    let splitY := Nat.modPowSucc y k
    let halfX: lowX / 2 = x / 2 % Nat.pow 2 k := omega [splitX]
    let halfY: lowY / 2 = y / 2 % Nat.pow 2 k := omega [splitY]
    let highs: Nat.xor x y / 2 % Nat.pow 2 k = Nat.xor (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k) :=
      Eq.trans (Eq.cong (half => half % Nat.pow 2 k) (Nat.xorDiv x y)) (Nat.xorModPow k (x / 2) (y / 2))
    let lowHighs: Nat.xor lowX lowY / 2 = Nat.xor (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k) :=
      Eq.trans (Nat.xorDiv lowX lowY) (rewrite halfX, halfY in rfl)
    let whole := Eq.trans (Nat.modPowSucc (Nat.xor x y) k) (Eq.cong (high => high * 2 + Nat.xor x y % 2) highs)
    let low :=
      Eq.trans (Nat.divModEq (Nat.xor lowX lowY) 2 (Nat.succNotZero 1)) (Eq.cong (high => high * 2 + Nat.xor lowX lowY % 2) lowHighs)
    let parity :=
      Eq.trans (Nat.xorMod x y)
        (Eq.trans
          (Eq.sym (Nat.xorSumParity lowX lowY (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k) x y splitX splitY))
          (Eq.sym (Nat.xorMod lowX lowY)))
    Nat.xorSameHalves (Nat.xor x y % Nat.pow 2 (Succ k)) (Nat.xor lowX lowY) (Nat.xor (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k))
      (Nat.xor x y % 2) (Nat.xor lowX lowY % 2) whole low parity

-- The XOR of two numbers below `2 ^ k` is below it.
theorem Nat.xorBelow (k: Nat) (x: Nat) (y: Nat) (smallX: x < Nat.pow 2 k) (smallY: y < Nat.pow 2 k): Nat.xor x y < Nat.pow 2 k :=
  let positive := Nat.nonzeroOfPos (Nat.pow 2 k) (Nat.powSuccPos 1 k)
  let kept := Nat.xorModPow k x y
  rewrite Nat.modSmall x (Nat.pow 2 k) smallX, Nat.modSmall y (Nat.pow 2 k) smallY at kept in
    rewrite Eq.sym kept in Nat.modLess (Nat.xor x y) (Nat.pow 2 k) positive
