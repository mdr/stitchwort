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

-- The functions behind the instances are named `addMod`, `mulMod`, `zeroMod`,
-- `oneMod`, `zeroAddMod`, ...: the loader loads every library file with a
-- function whose last name is the field of a dictionary used as `add.zeroAdd`
-- or `Add.add`, so a `Mod.add` would make every `List` program load this file.

type Mod (n: Nat) = { value: Nat, isLt: value < Mod.size n }

-- How many numbers a `Mod n` has.
def Mod.size (n: Nat): Nat := Succ (n - 1)

theorem Mod.sizeNeZero (n: Nat): Mod.size n != 0 := Nat.succNotZero (n - 1)

-- Two numbers with the same value are equal: their proofs are too.
theorem Mod.mkExt (n: Nat) (a: Nat) (b: Nat) (p: a < Mod.size n) (e: a = b):
    (q: b < Mod.size n) -> ({ value = a, isLt = p }: Mod n) = { value = b, isLt = q } :=
  J (b' e' => (q': b' < Mod.size n) -> ({ value = a, isLt = p }: Mod n) = { value = b', isLt = q' })
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
    | No h  => Void.exfalso (h (Nat.modLt x (Mod.size n) [ok := Mod.sizeNeZero n]))

-- `x` wrapped into range, Euclidean: `(Mod.ofInt (-1): Mod 100)` is 99.
def Mod.ofInt [n: Nat] (x: Int): Mod n := Mod.ofNat (Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n])

theorem Mod.valueOfInt [n: Nat] (x: Int): (Mod.ofInt x: Mod n).value = Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n] :=
  Eq.trans (Mod.valueOfNat (Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n]))
    (Nat.modSmall (Int.modNat x (Mod.size n) [ok := Mod.sizeNeZero n]) (Mod.size n) [ok := Mod.sizeNeZero n]
      (Int.modNatLt x (Mod.size n) [ok := Mod.sizeNeZero n]))

-- The number as an `Int`.
def Mod.toInt (i: Mod n): Int := Nat.toInt i.value

-- The number is below the size, so wrapping it changes nothing.
theorem Mod.valueOfNatValue [n: Nat] (i: Mod n): (Mod.ofNat i.value: Mod n).value = i.value :=
  Eq.trans (Mod.valueOfNat i.value) (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt)

theorem Mod.ofNatValue [n: Nat] (i: Mod n): Mod.ofNat i.value = i := Mod.ext (Mod.ofNat i.value) i (Mod.valueOfNatValue i)

-- Addition, multiplication and negation, wrapping.
def Mod.addMod (i: Mod n) (j: Mod n): Mod n := Mod.ofNat (i.value + j.value)

def Mod.mulMod (i: Mod n) (j: Mod n): Mod n := Mod.ofNat (i.value * j.value)

def Mod.neg (i: Mod n): Mod n := Mod.ofNat (Mod.size n - i.value)

-- `i` minus `j`, wrapping: `Mod.sub 5 7` is 98 in `Mod 100`, where `Nat`'s `5 - 7` is 0.
-- Written `i.sub j`.
def Mod.sub (i: Mod n) (j: Mod n): Mod n := Mod.addMod i (Mod.neg j)

theorem Mod.valueAdd [n: Nat] (i: Mod n) (j: Mod n): (Mod.addMod i j).value = (i.value + j.value) % Mod.size n :=
  Mod.valueOfNat (i.value + j.value)

theorem Mod.valueMul [n: Nat] (i: Mod n) (j: Mod n): (Mod.mulMod i j).value = (i.value * j.value) % Mod.size n :=
  Mod.valueOfNat (i.value * j.value)

theorem Mod.valueNeg [n: Nat] (i: Mod n): (Mod.neg i).value = (Mod.size n - i.value) % Mod.size n :=
  Mod.valueOfNat (Mod.size n - i.value)

theorem Mod.valueSub [n: Nat] (i: Mod n) (j: Mod n): (Mod.sub i j).value = (i.value + (Mod.size n - j.value)) % Mod.size n :=
  Eq.trans (Mod.valueAdd i (Mod.neg j))
    (Eq.trans (Eq.cong (t => (i.value + t) % Mod.size n) (Mod.valueNeg j))
      (Nat.addModMod i.value (Mod.size n - j.value) (Mod.size n) [ok := Mod.sizeNeZero n]))

-- `i + neg i` is 0, and subtracting a number from itself too.
theorem Mod.addNeg [n: Nat] (i: Mod n): Mod.addMod i (Mod.neg i) = Mod.zeroMod :=
  Mod.ext (Mod.addMod i (Mod.neg i)) Mod.zeroMod
    (Eq.trans (Mod.valueSub i i)
      (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.addSubCancel i.value (Mod.size n) (Nat.lessLe i.value (Mod.size n) i.isLt)))
        (Nat.modSelf (Mod.size n) [ok := Mod.sizeNeZero n])))

theorem Mod.subSelf [n: Nat] (i: Mod n): Mod.sub i i = Mod.zeroMod := Mod.addNeg i

-- 0.
def Mod.zeroMod [n: Nat]: Mod n := { value = 0, isLt = rfl }

theorem Mod.zeroAddMod [n: Nat] (i: Mod n): Mod.addMod Mod.zeroMod i = i :=
  Mod.ext (Mod.addMod Mod.zeroMod i) i
    (Eq.trans (Mod.valueAdd Mod.zeroMod i)
      (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt))

theorem Mod.addComm [n: Nat] (i: Mod n) (j: Mod n): Mod.addMod i j = Mod.addMod j i :=
  Mod.ext (Mod.addMod i j) (Mod.addMod j i)
    (Eq.trans (Mod.valueAdd i j)
      (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.addComm i.value j.value)) (Eq.sym (Mod.valueAdd j i))))

theorem Mod.addAssoc [n: Nat] (i: Mod n) (j: Mod n) (k: Mod n): Mod.addMod (Mod.addMod i j) k = Mod.addMod i (Mod.addMod j k) :=
  Mod.ext (Mod.addMod (Mod.addMod i j) k) (Mod.addMod i (Mod.addMod j k))
    (Eq.trans (Mod.valueAdd (Mod.addMod i j) k)
      (Eq.trans (Eq.cong (t => (t + k.value) % Mod.size n) (Mod.valueAdd i j))
        (Eq.trans (Nat.modAddMod (i.value + j.value) k.value (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.addAssoc i.value j.value k.value))
            (Eq.trans (Eq.sym (Nat.addModMod i.value (j.value + k.value) (Mod.size n) [ok := Mod.sizeNeZero n]))
              (Eq.trans (Eq.cong (t => (i.value + t) % Mod.size n) (Eq.sym (Mod.valueAdd j k)))
                (Eq.sym (Mod.valueAdd i (Mod.addMod j k)))))))))

-- 1, which in `Mod 1` is 0.
def Mod.oneMod [n: Nat]: Mod n := Mod.ofNat 1

theorem Mod.oneMulMod [n: Nat] (i: Mod n): Mod.mulMod Mod.oneMod i = i :=
  Mod.ext (Mod.mulMod Mod.oneMod i) i
    (Eq.trans (Mod.valueMul Mod.oneMod i)
      (Eq.trans (Eq.cong (t => (t * i.value) % Mod.size n) (Mod.valueOfNat 1))
        (Eq.trans (Nat.modMulMod 1 i.value (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.oneMul i.value))
            (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt)))))

theorem Mod.mulOneMod [n: Nat] (i: Mod n): Mod.mulMod i Mod.oneMod = i :=
  Mod.ext (Mod.mulMod i Mod.oneMod) i
    (Eq.trans (Mod.valueMul i Mod.oneMod)
      (Eq.trans (Eq.cong (t => (i.value * t) % Mod.size n) (Mod.valueOfNat 1))
        (Eq.trans (Nat.mulModMod i.value 1 (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.mulOne i.value))
            (Nat.modSmall i.value (Mod.size n) [ok := Mod.sizeNeZero n] i.isLt)))))

theorem Mod.mulAssoc [n: Nat] (i: Mod n) (j: Mod n) (k: Mod n): Mod.mulMod (Mod.mulMod i j) k = Mod.mulMod i (Mod.mulMod j k) :=
  Mod.ext (Mod.mulMod (Mod.mulMod i j) k) (Mod.mulMod i (Mod.mulMod j k))
    (Eq.trans (Mod.valueMul (Mod.mulMod i j) k)
      (Eq.trans (Eq.cong (t => (t * k.value) % Mod.size n) (Mod.valueMul i j))
        (Eq.trans (Nat.modMulMod (i.value * j.value) k.value (Mod.size n) [ok := Mod.sizeNeZero n])
          (Eq.trans (Eq.cong (t => t % Mod.size n) (Nat.mulAssoc i.value j.value k.value))
            (Eq.trans (Eq.sym (Nat.mulModMod i.value (j.value * k.value) (Mod.size n) [ok := Mod.sizeNeZero n]))
              (Eq.trans (Eq.cong (t => (i.value * t) % Mod.size n) (Eq.sym (Mod.valueMul j k)))
                (Eq.sym (Mod.valueMul i (Mod.mulMod j k)))))))))

-- `+` and `*`.
instance Mod.instAdd [n: Nat]: Add (Mod n) :=
  { zero = Mod.zeroMod, add = Mod.addMod, zeroAdd = Mod.zeroAddMod, assoc = Mod.addAssoc, comm = Mod.addComm }

instance Mod.instMul [n: Nat]: Mul (Mod n) :=
  { one = Mod.oneMod, mul = Mod.mulMod, oneMul = Mod.oneMulMod, mulOne = Mod.mulOneMod, assoc = Mod.mulAssoc }

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
theorem Mod.ltSize: (n: Nat) -> (x: Nat) -> x < n -> x < Mod.size n
  | Zero,   x, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, x, h => h

-- A position as a number modulo n (the same number).
def Fin.toMod (i: Fin n): Mod n := { value = Fin.toNat i, isLt = Mod.ltSize n (Fin.toNat i) (Fin.toNatLt i) }

-- A number modulo n as a position, when there is one (`n` isn't 0).
def Mod.toFin [auto ok: n != 0] (i: Mod n): Fin n :=
  Fin.ofNatLt n i.value (Mod.ltOfNeZero n i.value ok i.isLt)

theorem Mod.ltOfNeZero: (n: Nat) -> (x: Nat) -> n != 0 -> x < Mod.size n -> x < n
  | Zero,   x, ok, h => Void.exfalso (ok rfl)
  | Succ n, x, ok, h => h

theorem Mod.valueToMod (i: Fin n): (Fin.toMod i).value = Fin.toNat i := rfl

theorem Mod.toNatToFin [n: Nat] [auto ok: n != 0] (i: Mod n): Fin.toNat (Mod.toFin i) = i.value :=
  Fin.toNatOfNatLt n i.value (Mod.ltOfNeZero n i.value ok i.isLt)

theorem Mod.toModToFin [n: Nat] [auto ok: n != 0] (i: Mod n): Fin.toMod (Mod.toFin i) = i :=
  Mod.ext (Fin.toMod (Mod.toFin i)) i (Mod.toNatToFin i)

test "mod: ofNat wraps" := (Mod.ofNat 150: Mod 100).value == 50
test "mod: ofInt wraps below zero" := (Mod.ofInt (-1): Mod 100).value == 99
test "mod: ofInt wraps far below zero" := (Mod.ofInt (-205): Mod 100).value == 95
test "mod: + wraps" := ((Mod.ofNat 99: Mod 100) + Mod.ofNat 1).value == 0
test "mod: + is exact below the size" := ((Mod.ofNat 50: Mod 100) + Mod.ofNat 60).value == 10
test "mod: * wraps" := ((Mod.ofNat 30: Mod 100) * Mod.ofNat 7).value == 10
test "mod: sub wraps" := (Mod.sub (Mod.ofNat 5: Mod 100) (Mod.ofNat 7)).value == 98
test "mod: neg" := (Mod.neg (Mod.ofNat 30: Mod 100)).value == 70
test "mod: neg 0 is 0" := (Mod.neg (Mod.ofNat 0: Mod 100)).value == 0
test "mod: Mod 0 has only 0" := (Mod.ofNat 5: Mod 0).value == 0 && ((Mod.ofNat 3: Mod 0) + Mod.ofNat 4).value == 0
test "mod: Mod 1 has only 0" := ((Mod.ofNat 1: Mod 1) * Mod.ofNat 1).value == 0
test "mod: == by value" := (Mod.ofNat 150: Mod 100) == Mod.ofNat 50
test "mod: != different" := (Mod.ofNat 50: Mod 100) != Mod.ofNat 51
test "mod: < by value" := (Mod.ofNat 3: Mod 100) < Mod.ofNat 4 && (Mod.ofNat 4: Mod 100) <= Mod.ofNat 4
test "mod: show" := "${(Mod.ofNat 150: Mod 100)}" == "50"
test "mod: toInt" := Mod.toInt (Mod.ofNat 150: Mod 100) == 50
test "mod: Fin.toMod" := (Fin.toMod (Fin.ofNat 4: Fin 5)).value == 4
test "mod: Mod.toFin" := Fin.toNat (Mod.toFin (Mod.ofNat 4: Mod 5)) == 4
