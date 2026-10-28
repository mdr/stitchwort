-- An alias's functions are found by dot notation wherever the value's type
-- mentions the alias (docs/proposals/namespaces.md §4.8): a parameter, an
-- annotation, and a value whose type was inferred from one, such as an
-- element of a `List Code` or a value through a generic function. The
-- underlying type's functions are found too, after the alias's.

import Std (List)

type Code = List Nat

def Code.numericPart (code: Code): Nat := code.foldLeft 0 (number digit => 10 * number + digit)

def Code.scaled (code: Code) (factor: Nat): Nat := factor * code.numericPart

-- A lambda over the elements of a `List Code`.
def total (codes: List Code): Nat := codes.sumBy (code => code.numericPart)

-- An annotated lambda parameter.
def totalAnnotated (codes: List Code): Nat := codes.sumBy ((code: Code) => code.numericPart)

-- A section with an argument.
def totalScaled (codes: List Code): Nat := codes |> .sumBy (.scaled 2)

-- Through `List.map`.
def parts (codes: List Code): List Nat := codes.map (code => code.numericPart)

-- Through a generic function.
def same (value: a): a := value

def viaSame (code: Code): Nat := (same code).numericPart

-- The underlying type's functions, once `Code` has no `length`.
def digitCount (code: Code): Nat := code.length

-- A value of an alias of `Def … : Type` form, through `List.scanLeft`.
def FreeSpace: Type := List Nat

def FreeSpace.of (spans: List Nat): FreeSpace := spans

def FreeSpace.add (free: FreeSpace) (span: Nat): FreeSpace := Cons span free

def steps (spans: List Nat): List FreeSpace :=
  List.scanLeft spans (FreeSpace.of []) (free span => free.add span)

test "lambda" := total [[1, 2], [3]] == 15
test "annotated" := totalAnnotated [[1, 2], [3]] == 15
test "section" := totalScaled [[1, 2], [3]] == 30
test "map" := parts [[4, 2]] == [42]
test "generic" := viaSame [7] == 7
test "underlying" := digitCount [1, 2, 3] == 3
test "scan" := steps [1, 2] == [[], [1], [2, 1]]
