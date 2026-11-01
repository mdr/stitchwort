-- Which values does the alias's namespace reach?
type Code = List Nat

def Code.numericPart (code: Code): Nat := code.foldLeft 0 (number digit => 10 * number + digit)

-- A `List Nat` written by hand.
def handWritten (digits: List Nat): Nat := digits.numericPart

-- A literal.
def literal: Nat := [1, 2].numericPart

-- A literal checked against the alias.
def checkedLiteral: Nat := ([1, 2]: Code).numericPart

-- A `let` without an annotation, from a function returning the alias.
def first (codes: List Code): Code := codes.headOr []

def viaLet (codes: List Code): Nat :=
  let code := first codes
  code.numericPart

-- An element from a list operation (`List.map` on `List Code`).
def viaMap (codes: List Code): List Nat := codes.map (code => code.numericPart)

-- Through a generic function returning its argument's type.
def same (value: a): a := value

def viaSame (code: Code): Nat := (same code).numericPart
