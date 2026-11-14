-- Chapter 2: values, definitions, blocks, text and numbers.
import Std (Float, Int, Nat, SafeNat, Text)

-- begin definitions
def answer: Nat := 42

def double (n: Nat): Nat := n + n

def greeting (name: Text): Text := "Hello, " ++ name ++ "!"

def area (width height: Nat): Nat := width * height
-- end definitions

-- begin docs
--| How many shelves `width` wide fit along a wall, rounded down. A width of 0
--| fits none. For the floor see [`area`].
def shelves (wall width: Nat): Nat := wall / width

test "shelves" := shelves 250 60 == 4 ∧ shelves 250 0 == 0
-- end docs

-- begin blocks
def describe (n: Nat): Text :=
  let half := n / 2
  let parity := if n % 2 == 0 then "even" else "odd"
  "${n} is ${parity}, and half of it is ${half}"
-- end blocks

-- begin if-chain
def grade (score: Nat): Text := if score ≥ 90 then "A" else if score ≥ 75 then "B" else if score ≥ 50 then "C" else "D"
-- end if-chain

-- begin leading-operator
def validScore (score: Nat): Bool := 0 <= score && score <= 100 && score != 13
-- end leading-operator

test "a line may start with an operator" := validScore 50 && !validScore 13

-- begin interpolation
def summary (name: Text) (items: List Nat): Text :=
  "${name} bought ${items.length} items: ${items}, costing ${items.sum}"

test "summary" := summary "Ada" [3, 4] == "Ada bought 2 items: [3, 4], costing 7"
-- end interpolation

-- begin text-block
def example: Text := """
  L68
  L30
    R48
  """

test "a text block" := example == "L68\nL30\n  R48\n"
test "its lines" := example.lines == ["L68", "L30", "  R48"]
-- end text-block

-- begin nat
test "no overflow" := 2 * 1000000000000 * 1000000000000 == 2000000000000000000000000
test "subtraction stops at zero" := 3 - 5 == 0
test "division rounds down" := 7 / 2 == 3 ∧ 7 % 2 == 1
-- end nat

-- begin int
def balance: Int := 3 - 5

test "Int subtraction" := balance == -2
test "a negative literal is an Int" := -5 + 2 == -3
test "converting" := balance.toNat == 0 ∧ (7: Nat).toInt == 7
test "absolute value" := Int.natAbs balance == 2
-- end int

-- begin division-by-zero
test "dividing by 0" := 7 / 0 == 0 ∧ 7 % 0 == 7

def averageOf (total count: Nat): Nat := total / count

test "the average of nothing" := averageOf 10 0 == 0
-- end division-by-zero

-- begin chars
def initial (name: Text): Char := match name.uncons with
  | Some (first, _) => first
  | None => '?'

test "initial" := initial "Ada" == 'A' ∧ initial "" == '?'

test "digit tests" := '7'.isAsciiDigit ∧ ¬'x'.isAsciiDigit ∧ 'x'.isAsciiLetter ∧ 'Q'.isAsciiUppercase
-- end chars

-- begin float
def celsius (fahrenheit: Float): Float := (fahrenheit - 32.0) * 5.0 / 9.0

test "boiling" := celsius 212.0 == 100.0
test "doubles round" := 0.1 + 0.2 == 0.30000000000000004
-- end float

-- begin safe
def small: Option SafeNat := SafeNat.ofNat 42

test "fits a JS number" := small.isSome
test "too big for a JS number" := (SafeNat.ofNat 9007199254740992).isNone
-- end safe
