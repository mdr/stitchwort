-- Checked `Fin` literals (D1073, docs/proposals/fin-literals.md): a numeral
-- is a `Fin n` where n is a known number above it. The bound is checked by
-- computing `k < n`, so no proof is written.

import Std (Fin, List)

-- A list of digits.
def digits: List (Fin 10) := [2, 7, 5, 7, 3]

-- The bound only has to compute to a number.
def Ten: Nat := 10

def nine: Fin Ten := 9

def zero: Fin (2 * 5) := 0

-- A function argument.
def toNat4 (x: Fin 4): Nat := x.toNat

-- A record field.
type Cell = { row: Fin 3, col: Fin 3 }

def corner: Cell := { row = 2, col = 0 }

-- The literal is the position itself.
theorem seven: Fin.toNat (7: Fin 10) = 7 := rfl

theorem two: (2: Fin 5) = FSucc (FSucc FZero) := rfl

theorem digitsNat: List.map Fin.toNat digits = [2, 7, 5, 7, 3] := rfl

-- Beside a `Fin` in a comparison, a numeral is one too.
theorem compared: (nine == 9 && zero < 3) = True := rfl

-- A pattern: a number pattern on a `Fin` is `FZero` or `FSucc`.
def name: Fin 3 -> Text
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"

theorem nameOne: name 1 = "one" := rfl

-- Where the bound isn't a number, a number pattern is still `FZero` or
-- `FSucc`, and mixes with them.
def isFirst: Fin (Succ n) -> Bool
  | 0 => True
  | FSucc _ => False

theorem firstOfThree: isFirst (0: Fin 3) = True := rfl

-- Numbers that aren't expected as a `Fin` are as before.
theorem stillNat: 2 + 3 = 5 := rfl

test "list" := digits.map Fin.toNat == [2, 7, 5, 7, 3]
test "argument" := toNat4 3 == 3
test "field" := corner.row.toNat == 2
test "pattern" := [name 0, name 1, name 2] == ["zero", "one", "two"]
