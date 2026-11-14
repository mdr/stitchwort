-- `match some | …` keeps what matches: each arm's result is wrapped in
-- `Some`, and a value no arm matches gives `None`. It works wherever an
-- `a → Option b` does: `filterMap`, `findMap`, `Option.flatMap`, and as a
-- definition's whole body, which is the arms form with a last `_ => None`.
import Std (List, Nat, Option)

type Scan = | Corrupted (illegal: Nat) | Incomplete (missing: Nat) | Fine

def illegals (scans: List Scan): List Nat := scans.filterMap (match some | Corrupted illegal => illegal)

def firstMissing (scans: List Scan): Option Nat := scans.findMap (match some | Incomplete missing => missing)

-- A lookup table: the arms are the definition's, with `Some` added.
def operationOf: Nat → Option Scan := match some
  | 0 => Fine
  | 1 => Corrupted 1

-- Two patterns in an arm: a `Map.filterMap` function, say.
def both: Nat → Option Nat → Option Nat := match some | 0, Some n => n

-- The value matched can come from a pipeline.
def firstDigit (text: Nat): Option Nat :=
  text
    |> match some
      | 7 => 70
      | 8 => 80

-- `some` is a name anywhere but between `match` and `|`.
def some: Nat := 3
def pick: Nat → Nat := n =>
  match some with
    | 3 => n
    | _ => 0

theorem tableOfZero: operationOf 0 = Some Fine := operationOf.eq1
theorem tableOfFive: operationOf 5 = None := rfl

test "filterMap" := illegals [Corrupted 1, Fine, Corrupted 3, Incomplete 4] == [1, 3]
test "findMap" := firstMissing [Fine, Incomplete 4, Incomplete 5] == Some 4
test "table" := operationOf 0 == Some Fine && operationOf 5 == None
test "two patterns" := both 0 (Some 4) == Some 4 && both 0 None == None
test "pipeline" := firstDigit 8 == Some 80 && firstDigit 9 == None
test "some as a name" := pick 5 == 5
