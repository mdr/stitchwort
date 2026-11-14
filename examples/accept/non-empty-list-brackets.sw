import Std (NonEmptyList)

-- Where a `NonEmptyList` is expected, brackets build and match one: each pair
-- below, brackets and record, is the same term (the same hash).

def threeBrackets: NonEmptyList Nat := [1, 2, 3]
def threeRecord: NonEmptyList Nat := { head = 1, tail = [2, 3] }

def consBrackets (x: a) (xs: List a): NonEmptyList a := [x, ..xs]
def consRecord (x: a) (xs: List a): NonEmptyList a := { head = x, tail = xs }

-- A spread before the first item is put in front of it.
def aroundBrackets (xs: List a) (x: a): NonEmptyList a := [..xs, x]
def aroundRecord (xs: List a) (x: a): NonEmptyList a := NonEmptyList.prependList xs { head = x, tail = [] }

-- `[x, ..rest]` matches every `NonEmptyList`: no `[]` arm.
def firstBrackets: NonEmptyList a → a
  | [x, ..rest] => x

def firstRecord: NonEmptyList a → a
  | { head = x, tail = rest } => x

def sizeBrackets: NonEmptyList a → Text
  | [x] => "one"
  | [x, y] => "two"
  | [x, y, ..rest] => "many"

def sizeRecord: NonEmptyList a → Text
  | { head = x, tail = [] } => "one"
  | { head = x, tail = [y] } => "two"
  | { head = x, tail = [y, ..rest] } => "many"

-- Items that perform run in order, as in a `List` literal.
def mapBrackets (xs: NonEmptyList a) (f: a → {e} b): {e} NonEmptyList b := match xs with
  | [x, ..rest] => [f x, ..rest.map f]

def mapRecord (xs: NonEmptyList a) (f: a → {e} b): {e} NonEmptyList b := match xs with
  | { head = x, tail = rest } => { head = f x, tail = rest.map f }

-- A `Bool` item that performs is decided, as in a `List Bool`.
def orNone: Option Text → Text
  | None => "none"
  | Some t => t

def len(): {IO} Nat := (orNone IO.readLine()).length

def shortLines(): {IO} NonEmptyList Bool := [len() < 3, len() < 3]

-- Where the type isn't known, a literal is a `List`, as everywhere else.
def maxOfTwo (x y: Nat): Nat :=
  let both: NonEmptyList Nat := [x, y]
  both.maximum

test "brackets are records" := threeBrackets = threeRecord ∧ aroundBrackets [1, 2] 3 = { head = 1, tail = [2, 3] }
test "sizes" := sizeBrackets [1] == "one" && sizeBrackets [1, 2, 3] == "many"
test "a literal argument" := NonEmptyList.maximum [3, 1, 2] == 3 && maxOfTwo 4 9 == 9
