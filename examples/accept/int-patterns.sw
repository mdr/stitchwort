-- Number patterns on `Int` (docs/proposals/integers.md, "Number patterns on
-- `Int`"): a literal `k` is `OfNat k` and `-k` is `NegSucc (k - 1)` around a
-- number pattern on the `Nat` field, so a match on `Int` numbers is a `case`
-- on the sign with a number case in each branch.

def describe: Int → Text
  | 0 => "zero"
  | (-1) => "minus one"
  | 404 => "not found"
  | _ => "something else"

test "describe 0 == zero" := describe 0 == "zero"
test "describe (-1) == minus one" := describe (-1) == "minus one"
test "describe 404 == not found" := describe 404 == "not found"
test "describe (-404) == something else" := describe (-404) == "something else"
test "describe 1 == something else" := describe 1 == "something else"
test "describe (-2) == something else" := describe (-2) == "something else"

-- Row priority, and a variable is the integer, not the `Nat` field.
def pick: Int → Bool → Int
  | (-1), True => 7
  | z, False => z
  | _, _ => 9

theorem pick1: pick (-1) False = -1 := rfl

theorem pick2: pick (-2) False = -2 := rfl

theorem pick3: pick 3 False = 3 := rfl

theorem pick4: pick (-1) True = 7 := rfl

theorem pick5: pick 3 True = 9 := rfl

-- The sign split is real evidence: a whole branch with no numbers in it is
-- the catch-all, even for an unknown magnitude.
def zeroOrOther: Int → Bool
  | 0 => True
  | _ => False

theorem negativeIsOther (k: Nat): zeroOrOther (NegSucc k) = False := rfl

-- `0` and `-0` are one key; the first row with it wins, and the
-- second warns `W-REDUNDANT`.
def zeros: Int → Nat
  | 0 => 1
  | (-0) => 2
  | _ => 3

theorem zerosZero: zeros 0 = 1 := rfl

theorem zerosOne: zeros 1 = 3 := rfl

-- Repeated literals in different rows, with another column deciding.
def twice: Int → Bool → Nat
  | (-3), True => 1
  | 5, True => 2
  | (-3), _ => 3
  | _, _ => 4

theorem twice1: twice (-3) True = 1 := rfl

theorem twice2: twice (-3) False = 3 := rfl

theorem twice3: twice 5 False = 4 := rfl

theorem twice4: twice 5 True = 2 := rfl

-- Very large keys, either side of zero.
def big: Int → Nat
  | (-1000000000000000000000000000000) => 1
  | 1000000000000000000000000000000 => 2
  | _ => 3

theorem bigNeg: big (-1000000000000000000000000000000) = 1 := rfl

theorem bigPos: big 1000000000000000000000000000000 = 2 := rfl

theorem bigNear: big (-999999999999999999999999999999) = 3 := rfl

-- A column mixing literals, an explicit constructor and `_`.
def mixed: Int → Nat
  | 0 => 0
  | (-1) => 1
  | OfNat n => n + 10
  | _ => 99

theorem mixedZero: mixed 0 = 0 := rfl

theorem mixedNegOne: mixed (-1) = 1 := rfl

theorem mixedPos: mixed 4 = 14 := rfl

theorem mixedNeg: mixed (-7) = 99 := rfl

-- A catch-all before a literal makes the literal's row unreachable (`W-REDUNDANT`).
def shadowed: Int → Nat
  | _ => 1
  | 5 => 2

theorem shadowedFive: shadowed 5 = 1 := rfl

-- Two `Int` columns.
def quadrant: Int → Int → Text
  | 0, 0 => "origin"
  | 0, _ => "y axis"
  | _, 0 => "x axis"
  | (-1), (-1) => "diagonal"
  | _, _ => "elsewhere"

test "quadrant 0 0 == origin" := quadrant 0 0 == "origin"
test "quadrant 0 (-3) == y axis" := quadrant 0 (-3) == "y axis"
test "quadrant (-3) 0 == x axis" := quadrant (-3) 0 == "x axis"
test "quadrant (-1) (-1) == diagonal" := quadrant (-1) (-1) == "diagonal"
test "quadrant (-1) 1 == elsewhere" := quadrant (-1) 1 == "elsewhere"
test "quadrant 2 2 == elsewhere" := quadrant 2 2 == "elsewhere"

-- Inside other patterns, where the field's type is known to be `Int`.
def inSome: Option Int → Nat
  | Some (-1) => 1
  | Some 2 => 2
  | _ => 3

theorem inSome1: inSome (Some (-1)) = 1 := rfl

theorem inSome2: inSome (Some 2) = 2 := rfl

theorem inSome3: inSome (Some (-2)) = 3 := rfl

def inPair: (Int, Nat) → Nat
  | (-2, 0) => 1
  | (_, n) => n

theorem inPair1: inPair (-2, 0) = 1 := rfl

theorem inPair2: inPair (-2, 5) = 5 := rfl

-- A definition that unfolds to `Int` is matched the same way.
def Price: Type := Int

def priceLabel: Price → Text
  | 0 => "free"
  | (-1) => "refund"
  | _ => "paid"

test "priceLabel 0 == free" := priceLabel 0 == "free"
test "priceLabel (-1) == refund" := priceLabel (-1) == "refund"
test "priceLabel 3 == paid" := priceLabel 3 == "paid"

-- A literal, then constructors for the rest of each sign.
def sign: Int → Int
  | 0 => 0
  | OfNat _ => 1
  | NegSucc _ => -1

test "sign 0 == 0" := sign 0 == 0
test "sign 12 == 1" := sign 12 == 1
test "sign (-12) == -1" := sign (-12) == -1
