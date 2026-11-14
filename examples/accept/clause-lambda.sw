-- `match | …` is a lambda written as match arms: `x => match x with | …`.
-- With several patterns in an arm it takes several parameters. As a
-- definition's whole body it is the arms form, with the same equations.
import Std (List, Nat, Bool)

type Operator = | Add | Multiply

-- Whether `operator` can combine `a` and `b` into `target`.
def combines (target a b: Nat): Operator → Bool := match
  | Add => a + b == target
  | Multiply => a * b == target

def anyCombines (operators: List Operator) (target a b: Nat): Bool := operators.any (match
  | Add => a + b == target
  | Multiply => a * b == target)

-- Two parameters, written as a definition's arms are.
def sum: List Nat → Nat := xs =>
  xs.foldLeft 0 (match
    | total, 0 => total
    | total, n => total + n)

def Operator.symbol: Operator → Nat := match
  | Add => 43
  | Multiply => 42

theorem symbolOfAdd: Operator.symbol Add = 43 := Operator.symbol.eq1
theorem sumOfExample: sum [1, 0, 2] = 3 := rfl

test "a clause lambda is a lambda" := anyCombines [Add, Multiply] 6 2 3
test "the definition form" := combines 6 2 3 Multiply && !combines 6 2 3 Add
