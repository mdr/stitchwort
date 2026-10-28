-- `Mod n`: the numbers 0 to n - 1, where adding and multiplying wrap around,
-- as on a clock (`+` and `*` through the `Add` and `Mul` instances below).
-- For positions in a `Vec`, use `Fin n`: it has no arithmetic, so `i + 1` at
-- the last position can't silently wrap. `Fin.toMod` and `Mod.toFin` convert.
--
-- `Mod 0` has one value, 0, so that every `Mod n` has a zero: the numbers are
-- those below `Mod.size n`, which is `n` except that `Mod.size 0` is 1.
--
-- The range proof is built by deciding the comparison, not by citing
-- `Nat.modLt`: for a closed number the decision is `rfl`, so checking an `rfl`
-- about a `Mod 1000000` doesn't unfold that lemma's induction.

type Mod (n: Nat) = { value: Nat, isLt: value < Mod.size n }

-- How many numbers a `Mod n` has.
def Mod.size (n: Nat): Nat := Succ (n - 1)

-- The same proof as `auto` finds for `Succ k != 0`, so that `x % Mod.size n`
-- here and an `x % Succ k` written elsewhere are the same term.
theorem Mod.sizeNeZero (n: Nat): Mod.size n ≠ 0 := Nat.equalFalse (Mod.size n) 0 rfl

-- Two numbers with the same value are equal: their proofs are too.
theorem Mod.mkExt (n: Nat) (a: Nat) (b: Nat) (p: a < Mod.size n) (e: a = b):
    (q: b < Mod.size n) → ({ value = a, isLt = p }: Mod n) = { value = b, isLt = q } :=
  J (b' e' => (q': b' < Mod.size n) → ({ value = a, isLt = p }: Mod n) = { value = b', isLt = q' })
    (q' => J (r e'' => ({ value = a, isLt = p }: Mod n) = { value = a, isLt = r }) rfl
      (Bool.uniqueEq (Nat.leq (Succ a) (Mod.size n)) True p q'))
    e

theorem Mod.ext (i: Mod n) (j: Mod n) (e: i.value = j.value): i = j :=
  match i, j with
    | { value = a, isLt = p }, { value = b, isLt = q } => Mod.mkExt n a b p e q

-- `x` wrapped into range: `(Mod.ofNat 150: Mod 100)` is 50.
def Mod.ofNat [n: Nat] (x: Nat): Mod n :=
  if h: Nat.leq (Succ (x % Mod.size n)) (Mod.size n) = True then { value = x % Mod.size n, isLt = h }
  else Void.absurd (h (Nat.modLt x (Mod.size n) [ok := Mod.sizeNeZero n]))

theorem Mod.valueOfNat [n: Nat] (x: Nat): (Mod.ofNat x: Mod n).value = x % Mod.size n :=
  match Bool.decEq (Nat.leq (Succ (x % Mod.size n)) (Mod.size n)) True with
    | Yes h => rfl
    | No h => Void.exfalso (h (Nat.modLt x (Mod.size n) [ok := Mod.sizeNeZero n]))

-- `x` wrapped into range, Euclidean: `(Mod.ofInt (-1): Mod 100)` is 99.
def Mod.ofInt [n: Nat] (x: Int): Mod n := Mod.ofNat (Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n])

theorem Mod.valueOfInt [n: Nat] (x: Int): (Mod.ofInt x: Mod n).value = Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n] :=
  Eq.trans (Mod.valueOfNat (Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n]))
    (Nat.modSmall (Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n]) (Mod.size n) [ok := Mod.sizeNeZero n]
      (Int.modNatLt x (Mod.size n) [ok := Mod.sizeNeZero n]))

-- The number as an `Int`.
def Mod.toInt (i: Mod n): Int := Nat.toInt i.value

-- Whether this is 0.
def Mod.isZero (i: Mod n): Bool := i.value == 0

-- Move up by k: `i + k`, wrapping around.
def Mod.addNat [n: Nat] (i: Mod n) (k: Nat): Mod n := Mod.ofInt (i.toInt + k.toInt)

-- Move down by k: `i - k`, wrapping around.
def Mod.subNat [n: Nat] (i: Mod n) (k: Nat): Mod n := Mod.ofInt (i.toInt - k.toInt)

theorem Mod.addNatOfInt [n: Nat] (i: Mod n) (k: Nat): Mod.addNat i k = Mod.ofInt (i.toInt + k.toInt) := rfl
theorem Mod.subNatOfInt [n: Nat] (i: Mod n) (k: Nat): Mod.subNat i k = Mod.ofInt (i.toInt - k.toInt) := rfl

-- The number is below the size, so wrapping it changes nothing.
theorem Mod.valueOfNatValue [n: Nat] (i: Mod n): (Mod.ofNat i.value: Mod n).value = i.value :=
  Eq.trans (Mod.valueOfNat i.value) (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt)

theorem Mod.ofNatValue [n: Nat] (i: Mod n): Mod.ofNat i.value = i := Mod.ext (Mod.ofNat i.value) i (Mod.valueOfNatValue i)

-- Addition, multiplication and negation, wrapping.
def Mod.add (i: Mod n) (j: Mod n): Mod n := Mod.ofNat (i.value + j.value)

def Mod.mul (i: Mod n) (j: Mod n): Mod n := Mod.ofNat (i.value * j.value)

def Mod.neg (i: Mod n): Mod n := Mod.ofNat (Mod.size n - i.value)

-- `i` minus `j`, wrapping: `Mod.sub 5 7` is 98 in `Mod 100`, where `Nat`'s `5 - 7` is 0.
-- Written `i.sub j`.
def Mod.sub (i: Mod n) (j: Mod n): Mod n := Mod.add i (Mod.neg j)

theorem Mod.valueAdd [n: Nat] (i: Mod n) (j: Mod n): (Mod.add i j).value = (i.value + j.value) % Mod.size n :=
  Mod.valueOfNat (i.value + j.value)

theorem Mod.valueMul [n: Nat] (i: Mod n) (j: Mod n): (Mod.mul i j).value = (i.value * j.value) % Mod.size n :=
  Mod.valueOfNat (i.value * j.value)

theorem Mod.valueNeg [n: Nat] (i: Mod n): (Mod.neg i).value = (Mod.size n - i.value) % Mod.size n :=
  Mod.valueOfNat (Mod.size n - i.value)

theorem Mod.valueSub [n: Nat] (i: Mod n) (j: Mod n): (Mod.sub i j).value = (i.value + (Mod.size n - j.value)) % Mod.size n :=
  Eq.trans (Mod.valueAdd i (Mod.neg j))
    (Eq.trans (Eq.cong (t => (i.value + t) % Mod.size n) (Mod.valueNeg j))
      (Nat.addModMod i.value (Mod.size n - j.value) (Mod.size n) [ok := Mod.sizeNeZero n]))

-- `i + neg i` is 0, and subtracting a number from itself too.
theorem Mod.addNeg [n: Nat] (i: Mod n): Mod.add i (Mod.neg i) = Mod.zero :=
  Mod.ext (Mod.add i (Mod.neg i)) Mod.zero
    (Eq.trans (Mod.valueSub i i)
      (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.addSubCancel i.value (Mod.size n) (Nat.lessLe i.value (Mod.size n) i.isLt)))
        (Nat.modSelf (Mod.size n) [ok := Mod.sizeNeZero n])))

theorem Mod.subSelf [n: Nat] (i: Mod n): Mod.sub i i = Mod.zero := Mod.addNeg i

-- 0.
def Mod.zero [n: Nat]: Mod n := { value = 0, isLt = rfl }

theorem Mod.zeroAdd [n: Nat] (i: Mod n): Mod.add Mod.zero i = i :=
  Mod.ext (Mod.add Mod.zero i) i
    (Eq.trans (Mod.valueAdd Mod.zero i)
      (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt))

theorem Mod.addComm [n: Nat] (i: Mod n) (j: Mod n): Mod.add i j = Mod.add j i :=
  Mod.ext (Mod.add i j) (Mod.add j i)
    (Eq.trans (Mod.valueAdd i j)
      (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.addComm i.value j.value)) (Eq.sym (Mod.valueAdd j i))))

theorem Mod.addAssoc [n: Nat] (i: Mod n) (j: Mod n) (k: Mod n): Mod.add (Mod.add i j) k = Mod.add i (Mod.add j k) :=
  Mod.ext (Mod.add (Mod.add i j) k) (Mod.add i (Mod.add j k))
    (Eq.trans (Mod.valueAdd (Mod.add i j) k)
      (Eq.trans (Eq.cong (t => (t + k.value) % Mod.size n) (Mod.valueAdd i j))
        (Eq.trans (Nat.modAddMod (i.value + j.value) k.value (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.addAssoc i.value j.value k.value))
            (Eq.trans (Eq.sym (Nat.addModMod i.value (j.value + k.value) (Mod.size n) [ok := Mod.sizeNeZero n]))
              (Eq.trans (Eq.cong (t => (i.value + t) % Mod.size n) (Eq.sym (Mod.valueAdd j k)))
                (Eq.sym (Mod.valueAdd i (Mod.add j k)))))))))

-- 1, which in `Mod 1` is 0.
def Mod.one [n: Nat]: Mod n := Mod.ofNat 1

theorem Mod.oneMul [n: Nat] (i: Mod n): Mod.mul Mod.one i = i :=
  Mod.ext (Mod.mul Mod.one i) i
    (Eq.trans (Mod.valueMul Mod.one i)
      (Eq.trans (Eq.cong (t => (t * i.value) % Mod.size n) (Mod.valueOfNat 1))
        (Eq.trans (Nat.modMulMod 1 i.value (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.oneMul i.value))
            (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt)))))

theorem Mod.mulOne [n: Nat] (i: Mod n): Mod.mul i Mod.one = i :=
  Mod.ext (Mod.mul i Mod.one) i
    (Eq.trans (Mod.valueMul i Mod.one)
      (Eq.trans (Eq.cong (t => (i.value * t) % Mod.size n) (Mod.valueOfNat 1))
        (Eq.trans (Nat.mulModMod i.value 1 (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.mulOne i.value))
            (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt)))))

theorem Mod.mulAssoc [n: Nat] (i: Mod n) (j: Mod n) (k: Mod n): Mod.mul (Mod.mul i j) k = Mod.mul i (Mod.mul j k) :=
  Mod.ext (Mod.mul (Mod.mul i j) k) (Mod.mul i (Mod.mul j k))
    (Eq.trans (Mod.valueMul (Mod.mul i j) k)
      (Eq.trans (Eq.cong (t => (t * k.value) % Mod.size n) (Mod.valueMul i j))
        (Eq.trans (Nat.modMulMod (i.value * j.value) k.value (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.mulAssoc i.value j.value k.value))
            (Eq.trans (Eq.sym (Nat.mulModMod i.value (j.value * k.value) (Mod.size n) [ok := Mod.sizeNeZero n]))
              (Eq.trans (Eq.cong (t => (i.value * t) % Mod.size n) (Eq.sym (Mod.valueMul j k)))
                (Eq.sym (Mod.valueMul i (Mod.mul j k)))))))))

-- `+` and `*`.
instance Mod.instAdd [n: Nat]: Add (Mod n) :=
  { zero = Mod.zero, add = Mod.add, zeroAdd = Mod.zeroAdd, assoc = Mod.addAssoc, comm = Mod.addComm }

instance Mod.instMul [n: Nat]: Mul (Mod n) :=
  { one = Mod.one, mul = Mod.mul, oneMul = Mod.oneMul, mulOne = Mod.mulOne, assoc = Mod.mulAssoc }

-- The number itself: `"${(Mod.ofNat 50: Mod 100)}"` is `50`.
instance Mod.instShow: Show (Mod n) := Show.fromText (i => Nat.toText i.value)

-- `==` on numbers: equal exactly when their values are. Written by hand: a
-- derived `DecEq` is only for proofs of `<=` (as in `Dial`), not `<`.
instance Mod.instDecEq [n: Nat]: DecEq (Mod n) :=
  { decide = i j =>
    if h: i.value = j.value then Yes (Mod.ext i j h)
    else No (e => h (Eq.cong (k => k.value) e)) }

-- Numbers in order of their values (not of their clock positions: 99 comes
-- after 0 even though `99 + 1` is 0).
instance Mod.instOrd [n: Nat]: Ord (Mod n) := Ord.byKey ((i: Mod n) => i.value) Mod.ext

-- Conversions with `Fin`, the type of positions in a `Vec`.
theorem Mod.ltSize: (n: Nat) → (x: Nat) → x < n → x < Mod.size n
  | Zero, x, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, x, h => h

-- A position as a number modulo n (the same number).
def Fin.toMod (i: Fin n): Mod n := { value = Fin.toNat i, isLt = Mod.ltSize n (Fin.toNat i) (Fin.toNatLt i) }

-- A number modulo n as a position, when there is one (`n` isn't 0).
def Mod.toFin [auto ok: n ≠ 0] (i: Mod n): Fin n :=
  Fin.ofNatLt n i.value (Mod.ltOfNeZero n i.value ok i.isLt)

theorem Mod.ltOfNeZero: (n: Nat) → (x: Nat) → n ≠ 0 → x < Mod.size n → x < n
  | Zero, x, ok, h => Void.exfalso (ok rfl)
  | Succ n, x, ok, h => h

theorem Mod.valueToMod (i: Fin n): (Fin.toMod i).value = Fin.toNat i := rfl

theorem Mod.toNatToFin [n: Nat] [auto ok: n ≠ 0] (i: Mod n): Fin.toNat (Mod.toFin i) = i.value :=
  Fin.toNatOfNatLt n i.value (Mod.ltOfNeZero n i.value ok i.isLt)

theorem Mod.toModToFin [n: Nat] [auto ok: n ≠ 0] (i: Mod n): Fin.toMod (Mod.toFin i) = i :=
  Mod.ext (Fin.toMod (Mod.toFin i)) i (Mod.toNatToFin i)

-- Laws for `addNat`, `subNat` and `neg`: moving by 0, moving twice, moving
-- there and back, and `neg` as a mirror (`neg (i.subNat k) = (neg i).addNat k`:
-- turning left from `i` is turning right from its mirror image, mirrored).
-- Each is proved through `Mod.ofInt`, by way of the `Int`: wrapping before
-- adding or negating changes nothing, because adding a multiple of the size,
-- positive or negative, keeps the remainder.

-- `Mod.ofInt` after `Mod.toInt` changes nothing; wrapping before adding or
-- negating changes nothing either.
theorem Mod.ofIntToInt [n: Nat] (i: Mod n): Mod.ofInt i.toInt = i :=
  Mod.ext (Mod.ofInt i.toInt) i
    (Eq.trans (Mod.valueOfInt i.toInt) (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt))

theorem Mod.toIntOfInt [n: Nat] (x: Int): (Mod.ofInt x: Mod n).toInt = Nat.toInt (Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n]) :=
  Eq.cong Nat.toInt (Mod.valueOfInt x)

theorem Mod.ofIntAdd [n: Nat] (x: Int) (y: Int): (Mod.ofInt (Int.add (Mod.ofInt x: Mod n).toInt y): Mod n) = Mod.ofInt (Int.add x y) :=
  Mod.ext (Mod.ofInt (Int.add (Mod.ofInt x: Mod n).toInt y)) (Mod.ofInt (Int.add x y))
    (Eq.trans (Mod.valueOfInt (Int.add (Mod.ofInt x: Mod n).toInt y))
      (Eq.trans (Eq.cong (t => Int.modNat (Int.add t y) (Mod.size n) [ok := Mod.sizeNeZero n]) (Mod.toIntOfInt x))
        (Eq.trans (Int.modNatModAdd x y (Mod.size n) [ok := Mod.sizeNeZero n]) (Eq.sym (Mod.valueOfInt (Int.add x y))))))

theorem Mod.ofIntNeg [n: Nat] (x: Int): (Mod.ofInt (Int.neg (Mod.ofInt x: Mod n).toInt): Mod n) = Mod.ofInt (Int.neg x) :=
  Mod.ext (Mod.ofInt (Int.neg (Mod.ofInt x: Mod n).toInt)) (Mod.ofInt (Int.neg x))
    (Eq.trans (Mod.valueOfInt (Int.neg (Mod.ofInt x: Mod n).toInt))
      (Eq.trans (Eq.cong (t => Int.modNat (Int.neg t) (Mod.size n) [ok := Mod.sizeNeZero n]) (Mod.toIntOfInt x))
        (Eq.trans (Int.modNatModNeg x (Mod.size n) [ok := Mod.sizeNeZero n]) (Eq.sym (Mod.valueOfInt (Int.neg x))))))

-- `Mod.neg` is `-` on the `Int`, wrapped.
theorem Mod.subModEq (m: Nat) (ok: Succ m ≠ 0): (v: Nat) → v < Succ m →
    (Succ m - v) % Succ m = Int.modNat (Int.neg (OfNat v)) (Succ m) [ok := ok]
  | Zero, h => Eq.trans (Nat.modSelf (Succ m)) (Eq.sym (Nat.modSmall 0 (Succ m) h))
  | Succ w, h =>
    Eq.trans (Nat.modSmall (m - w) (Succ m) (Nat.subLe m w))
      (Eq.cong (t => m - t) (Eq.sym (Nat.modSmall w (Succ m) omega)))

theorem Mod.negOfInt [n: Nat] (i: Mod n): Mod.neg i = Mod.ofInt (Int.neg i.toInt) :=
  Mod.ext (Mod.neg i) (Mod.ofInt (Int.neg i.toInt))
    (Eq.trans (Mod.valueNeg i)
      (Eq.trans (Mod.subModEq (n - 1) (Mod.sizeNeZero n) i.value i.isLt) (Eq.sym (Mod.valueOfInt (Int.neg i.toInt)))))

-- The laws.
theorem Mod.addNatZero [n: Nat] (i: Mod n): i.addNat 0 = i :=
  Eq.trans (Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.addZero i.toInt)) (Mod.ofIntToInt i)

theorem Mod.subNatZero [n: Nat] (i: Mod n): i.subNat 0 = i :=
  Eq.trans (Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.addZero i.toInt)) (Mod.ofIntToInt i)

theorem Mod.addNatAddNat [n: Nat] (i: Mod n) (j: Nat) (k: Nat): (i.addNat j).addNat k = i.addNat (j + k) :=
  Eq.trans (Mod.ofIntAdd (Int.add i.toInt j.toInt) k.toInt)
    (Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.addAssoc i.toInt j.toInt k.toInt))

theorem Mod.subNatSubNat [n: Nat] (i: Mod n) (j: Nat) (k: Nat): (i.subNat j).subNat k = i.subNat (j + k) :=
  Eq.trans (Mod.ofIntAdd (Int.sub i.toInt j.toInt) (Int.neg k.toInt))
    (Eq.cong (t => (Mod.ofInt t: Mod n))
      (Eq.trans (Int.addAssoc i.toInt (Int.neg j.toInt) (Int.neg k.toInt))
        (Eq.cong (Int.add i.toInt) (Eq.sym (Int.negAdd j.toInt k.toInt)))))

theorem Mod.addNatSubNat [n: Nat] (i: Mod n) (k: Nat): (i.addNat k).subNat k = i :=
  Eq.trans (Mod.ofIntAdd (Int.add i.toInt k.toInt) (Int.neg k.toInt))
    (Eq.trans (Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.addAddNeg i.toInt k.toInt)) (Mod.ofIntToInt i))

theorem Mod.subNatAddNat [n: Nat] (i: Mod n) (k: Nat): (i.subNat k).addNat k = i :=
  Eq.trans (Mod.ofIntAdd (Int.sub i.toInt k.toInt) k.toInt)
    (Eq.trans (Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.addNegAdd i.toInt k.toInt)) (Mod.ofIntToInt i))

theorem Mod.negZero [n: Nat]: Mod.neg (Mod.zero: Mod n) = Mod.zero :=
  Mod.ext (Mod.neg (Mod.zero: Mod n)) Mod.zero
    (Eq.trans (Mod.valueNeg (Mod.zero: Mod n)) (Nat.modSelf (Mod.size n) [ok := Mod.sizeNeZero n]))

theorem Mod.negNeg [n: Nat] (i: Mod n): Mod.neg (Mod.neg i) = i :=
  calc Mod.neg (Mod.neg i)
    _ = Mod.ofInt (Int.neg (Mod.neg i).toInt) := Mod.negOfInt (Mod.neg i)
    _ = Mod.ofInt (Int.neg (Mod.ofInt (Int.neg i.toInt): Mod n).toInt) := Eq.cong (j => (Mod.ofInt (Int.neg (Mod.toInt j)): Mod n)) (Mod.negOfInt i)
    _ = Mod.ofInt (Int.neg (Int.neg i.toInt)) := Mod.ofIntNeg (Int.neg i.toInt)
    _ = Mod.ofInt i.toInt := Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.negNeg i.toInt)
    _ = i := Mod.ofIntToInt i

-- Turning back is the mirror image of turning forward.
theorem Mod.negSubNat [n: Nat] (i: Mod n) (k: Nat): Mod.neg (i.subNat k) = (Mod.neg i).addNat k :=
  calc Mod.neg (i.subNat k)
    _ = Mod.ofInt (Int.neg (i.subNat k).toInt) := Mod.negOfInt (i.subNat k)
    _ = Mod.ofInt (Int.neg (Int.sub i.toInt k.toInt)) := Mod.ofIntNeg (Int.sub i.toInt k.toInt)
    _ = Mod.ofInt (Int.add (Int.neg i.toInt) (Int.neg (Int.neg k.toInt))) := Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.negAdd i.toInt (Int.neg k.toInt))
    _ = Mod.ofInt (Int.add (Int.neg i.toInt) k.toInt) := Eq.cong (t => (Mod.ofInt (Int.add (Int.neg i.toInt) t): Mod n)) (Int.negNeg k.toInt)
    _ = Mod.ofInt (Int.add (Mod.ofInt (Int.neg i.toInt): Mod n).toInt k.toInt) := Eq.sym (Mod.ofIntAdd (Int.neg i.toInt) k.toInt)
    _ = (Mod.neg i).addNat k := Eq.cong (j => Mod.addNat j k) (Eq.sym (Mod.negOfInt i))

theorem Mod.negAddNat [n: Nat] (i: Mod n) (k: Nat): Mod.neg (i.addNat k) = (Mod.neg i).subNat k :=
  calc Mod.neg (i.addNat k)
    _ = Mod.ofInt (Int.neg (i.addNat k).toInt) := Mod.negOfInt (i.addNat k)
    _ = Mod.ofInt (Int.neg (Int.add i.toInt k.toInt)) := Mod.ofIntNeg (Int.add i.toInt k.toInt)
    _ = Mod.ofInt (Int.add (Int.neg i.toInt) (Int.neg k.toInt)) := Eq.cong (t => (Mod.ofInt t: Mod n)) (Int.negAdd i.toInt k.toInt)
    _ = Mod.ofInt (Int.add (Mod.ofInt (Int.neg i.toInt): Mod n).toInt (Int.neg k.toInt)) := Eq.sym (Mod.ofIntAdd (Int.neg i.toInt) (Int.neg k.toInt))
    _ = (Mod.neg i).subNat k := Eq.cong (j => Mod.subNat j k) (Eq.sym (Mod.negOfInt i))

test "mod: ofNat wraps" := (Mod.ofNat 150: Mod 100).value == 50
test "mod: ofInt wraps below zero" := (Mod.ofInt (-1): Mod 100).value == 99
test "mod: ofInt wraps far below zero" := (Mod.ofInt (-205): Mod 100).value == 95
test "mod: + wraps" := ((Mod.ofNat 99: Mod 100) + Mod.ofNat 1).value == 0
test "mod: + is exact below the size" := ((Mod.ofNat 50: Mod 100) + Mod.ofNat 60).value == 10
test "mod: * wraps" := ((Mod.ofNat 30: Mod 100) * Mod.ofNat 7).value == 10
test "mod: sub wraps" := (Mod.sub (Mod.ofNat 5: Mod 100) (Mod.ofNat 7)).value == 98
test "mod: neg" := (Mod.neg (Mod.ofNat 30: Mod 100)).value == 70
test "mod: neg 0 is 0" := (Mod.neg (Mod.ofNat 0: Mod 100)).value == 0
test "mod: Mod 0 has only 0" := (Mod.ofNat 5: Mod 0).value == 0 ∧ ((Mod.ofNat 3: Mod 0) + Mod.ofNat 4).value == 0
test "mod: Mod 1 has only 0" := ((Mod.ofNat 1: Mod 1) * Mod.ofNat 1).value == 0
test "mod: == by value" := (Mod.ofNat 150: Mod 100) == Mod.ofNat 50
test "mod: != different" := (Mod.ofNat 50: Mod 100) ≠ Mod.ofNat 51
test "mod: < by value" := (Mod.ofNat 3: Mod 100) < Mod.ofNat 4 ∧ (Mod.ofNat 4: Mod 100) ≤ Mod.ofNat 4
test "mod: show" := "${(Mod.ofNat 150: Mod 100)}" == "50"
test "mod: toInt" := Mod.toInt (Mod.ofNat 150: Mod 100) == 50
test "mod: Fin.toMod" := (Fin.toMod (Fin.ofNat 4: Fin 5)).value == 4
test "mod: Mod.toFin" := Fin.toNat (Mod.toFin (Mod.ofNat 4: Mod 5)) == 4
test "mod: subNat wraps" := ((Mod.ofNat 50: Mod 100).subNat 68).value == 82
test "mod: addNat wraps" := ((Mod.ofNat 99: Mod 100).addNat 1).value == 0 ∧ ((Mod.ofNat 99: Mod 100).addNat 1).isZero
test "mod: isZero" := (Mod.ofNat 5: Mod 100).isZero == False
test "mod: addNat twice" := ((Mod.ofNat 90: Mod 100).addNat 7).addNat 8 == (Mod.ofNat 90: Mod 100).addNat 15
test "mod: subNat then addNat" := (((Mod.ofNat 3: Mod 100).subNat 250).addNat 250).value == 3
test "mod: neg is a mirror" := Mod.neg ((Mod.ofNat 10: Mod 100).subNat 30) == (Mod.neg (Mod.ofNat 10: Mod 100)).addNat 30
test "mod: neg (neg i)" := Mod.neg (Mod.neg (Mod.ofNat 30: Mod 100)) == Mod.ofNat 30
