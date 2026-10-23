-- `Fin n`: the numbers below n, as an indexed data type (Agda's and Idris's
-- `Fin`). A value of `Fin n` is a position in a `Vec a n`, so `Vec.get` needs
-- no bound proof: the type of the index is the proof. `Fin.ofNatLt` and
-- `Fin.toNat` convert to and from a `Nat` with its bound.

type Fin: Nat -> Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

-- The number itself: `FSucc FZero` is 1.
def Fin.toNat: Fin n -> Nat
  | FZero => 0
  | FSucc i => Succ (Fin.toNat i)

theorem Fin.toNatLt: (i: Fin n) -> Fin.toNat i < n
  | FZero => rfl
  | FSucc i => Fin.toNatLt i

-- `i` as a position below n, from a proof that it is one.
def Fin.ofNatLt: (n: Nat) -> (i: Nat) -> i < n -> Fin n
  | Zero, i, h => Void.absurd (Bool.falseNotTrue h)
  | Succ n, Zero, h => FZero
  | Succ n, Succ i, h => FSucc (Fin.ofNatLt n i h)

-- `Fin.ofNat i` when `i < n` is decided for closed numbers: `(Fin.ofNat 2: Fin 5)`.
def Fin.ofNat (i: Nat) [auto ok: i < n]: Fin n := Fin.ofNatLt n i ok

theorem Fin.toNatOfNatLt: (n: Nat) -> (i: Nat) -> (h: i < n) -> Fin.toNat (Fin.ofNatLt n i h) = i
  | Zero, i, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, Zero, h => rfl
  | Succ n, Succ i, h => Eq.cong Succ (Fin.toNatOfNatLt n i h)

theorem Fin.ofNatExample: Fin.toNat (Fin.ofNat 3: Fin 5) = 3 := rfl

test "toNat" := Fin.toNat (FSucc (FSucc FZero): Fin 4) == 2
test "ofNat" := Fin.toNat (Fin.ofNat 4: Fin 5) == 4

-- The number itself: `"${(Fin.ofNat 2: Fin 5)}"` is `2`.
instance Fin.instShow: Show (Fin n) := Show.fromText (i => Nat.toText (Fin.toNat i))

-- Positions with the same number are equal (so `Fin.toNat i == Fin.toNat j`
-- decides `i = j`).
theorem Fin.toNatInjective: (i: Fin n) -> (j: Fin n) -> Fin.toNat i = Fin.toNat j -> i = j
  | FZero, FZero, h => rfl
  | FSucc i, FSucc j, h => Eq.cong FSucc (Fin.toNatInjective i j (Nat.succInjective (Fin.toNat i) (Fin.toNat j) h))
  | FZero, FSucc j, h => Void.exfalso (Nat.zeroNotSucc (Fin.toNat j) h)
  | FSucc i, FZero, h => Void.exfalso (Nat.succNotZero (Fin.toNat i) h)

-- `==` on positions: they're equal exactly when their numbers are. Written
-- by hand: deriving `==` for an indexed family is not supported yet.
instance Fin.instDecEq: DecEq (Fin n) :=
  { decide = i j =>
    if h: Fin.toNat i = Fin.toNat j then Yes (Fin.toNatInjective i j h)
    else No (e => h (Eq.cong Fin.toNat e)) }

-- Positions in order of their numbers.
instance Fin.instOrd: Ord (Fin n) := Ord.byKey Fin.toNat Fin.toNatInjective

test "fin: == equal" := (FSucc FZero: Fin 3) == FSucc FZero
test "fin: == different" := (FSucc FZero: Fin 3) != FZero
test "fin: == different depth" := (FSucc (FSucc FZero): Fin 3) != FSucc FZero
test "fin: < by number" := (FZero: Fin 3) < FSucc FZero && FSucc FZero <= (FSucc (FSucc FZero): Fin 3)
test "fin: show" := "${(Fin.ofNat 2: Fin 5)}" == "2"

-- `i` as a position below n, if it is one: `None` when `i >= n`.
def Fin.ofNatCheck (n: Nat) (i: Nat): Option (Fin n) := if h: i < n then Some (Fin.ofNatLt n i h) else None

theorem Fin.ofNatCheckDec (n: Nat) (i: Nat): (d: Decidable (i < n)) -> i < n ->
    Option.map Fin.toNat (Decidable.elim d (h => Some (Fin.ofNatLt n i h)) (h => None)) = Some i
  | Yes h, lt => Eq.cong Some (Fin.toNatOfNatLt n i h)
  | No r, lt => Void.exfalso (r lt)

theorem Fin.ofNatCheckLt (n: Nat) (i: Nat) (h: i < n): Option.map Fin.toNat (Fin.ofNatCheck n i) = Some i :=
  Fin.ofNatCheckDec n i (Bool.decTrue (Nat.leq (Succ i) n)) h

test "ofNatCheck" := (Option.map Fin.toNat (Fin.ofNatCheck 5 4), Option.map Fin.toNat (Fin.ofNatCheck 5 5)) == (Some 4, None)

-- The decimal digit a character shows: `Char.toDigit '7'` is 7, as a
-- `Fin 10`, and a character that isn't a digit gives `None`.
def Char.toDigit (char: Char): Option (Fin 10) := Option.flatMap (Fin.ofNatCheck 10) (Char.digitValue char)

theorem Char.toDigitOf: (m: Option Nat) -> Option.IsDigit m -> Option.map Fin.toNat (Option.flatMap (Fin.ofNatCheck 10) m) = m
  | None, h => rfl
  | Some d, h => Fin.ofNatCheckLt 10 d h

-- `Char.toDigit` is `Char.digitValue`, with the digit's bound in its type.
theorem Char.toDigitValue (c: Char): Option.map Fin.toNat (Char.toDigit c) = Char.digitValue c :=
  Char.toDigitOf (Char.digitValue c) (Char.digitValueDigit c)

test "char to digit" := List.map (c => Option.map Fin.toNat (Char.toDigit c)) (Text.toList "0a9") == [Some 0, None, Some 9]
