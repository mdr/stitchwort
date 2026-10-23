-- Named-field constructor patterns (docs/proposals/variant-fields.md §4):
-- `C { f = p, g, .. }` matches a `C`, naming its fields as a record pattern
-- names a record's. It means the positional pattern with `_` for the fields
-- left out, so coverage is the positional pattern's.

import Std (Eq, Int, List, Nat, Option)

type Point = { x: Int, y: Int }

type Shape =
  | Dot (ref: Nat) (id: Text) (start: Int)
  | Circle (ref: Nat) (id: Text) (start: Int) (text: Text)
  | Polygon (ref: Nat) (id: Text) (start: Int) (duration: Nat) (points: List Point)

-- A punned field binds a variable of its name; `..` ignores the rest.
-- Without `..`, every field is named. Each arm names `id`: no counting.
def idOf: Shape -> Text
  | Dot { ref, id, start } => id
  | Circle { id, .. } => id
  | Polygon { id, .. } => id

-- `f = p` matches field `f` with any pattern; fields in any order.
def label: Shape -> Text
  | Circle { text = t, start = 0, .. } => "at zero: " ++ t
  | Circle { start, text = t, .. } => t
  | Polygon { points = [], .. } => "empty"
  -- After `=`, a constructor takes its arguments without brackets.
  | Polygon { points = Cons p _, .. } => "from a point"
  | _ => "dot"

def textOf: Shape -> Option Text
  | Circle { text, .. } => Some text
  | _ => None

-- `C { .. }` matches any `C`.
def isPolygon: Shape -> Bool
  | Polygon { .. } => True
  | _ => False

-- Coverage is the positional pattern's: these three arms are exhaustive.
def duration: Shape -> Nat
  | Polygon { duration, .. } => duration
  | Circle { .. } => 1
  | Dot { .. } => 0

-- Named and positional patterns are the same pattern.
def startNamed: Shape -> Int
  | Dot { start, .. } => start
  | Circle { start, .. } => start
  | Polygon { start, .. } => start

def startPositional: Shape -> Int
  | Dot _ _ s => s
  | Circle _ _ s _ => s
  | Polygon _ _ s _ _ => s

theorem sameStart (a: Shape): startNamed a = startPositional a := match a with
  | Dot { .. } => rfl
  | Circle { .. } => rfl
  | Polygon { .. } => rfl

def circle: Shape := Circle 1 "c" 5 "hello"

test "named fields" := idOf circle == "c" && textOf circle == Some "hello"
test "by value" := label (Circle 2 "d" 0 "x") == "at zero: x"
test "nested" := label (Polygon 3 "p" 1 2 [{ x = 0, y = 0 }]) == "from a point"

-- Anywhere a pattern goes: in `match`, in tuples, lists and brackets, and
-- nested in each other.
def firstText (xs: List Shape): Option Text := match xs with
  | [Circle { text, .. }, ..rest] => Some text
  | _ => None

def bothCircles: (Shape, Shape) -> Bool
  | (Circle { .. }, Circle { .. }) => True
  | _ => False

def nestedOption: Option Shape -> Nat
  | Some (Polygon { points = [p], .. }) => 1
  | _ => 0

-- A one-constructor type, in `let` and in a lambda's bracketed parameter.
type Size = | MkSize (width: Nat) (height: Nat)

def area (s: Size): Nat :=
  let MkSize { width, height } := s
  width * height

def widths (xs: List Size): List Nat := xs.map ((MkSize { width, .. }) => width)

test "let and lambda" := area (MkSize 2 3) == 6 && widths [MkSize 4 1] == [4]

-- Parameters: the fields' types are the constructor's, instantiated.
type Box (a: Type) =
  | Empty
  | Full (content: a) (count: Nat)

def contentOr (d: a): Box a -> a
  | Full { content, .. } => content
  | Empty { } => d

test "parameters" := contentOr 0 (Full 7 2) == 7 && contentOr 0 Empty == 0

-- Implicit fields are skipped by braces, as by positional patterns.
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (head: a) (tail: Vec a n): Vec a (Succ n)

def headOf (xs: Vec a (Succ n)): a := match xs with
  | VCons { head, .. } => head

-- A field that is a record: a record pattern after `=`. A record pattern
-- as the constructor's positional argument is in brackets.
type Person = { name: Text, age: Nat }

type Wrap = | W (person: Person)

def nameByField: Wrap -> Text
  | W { person = { name, .. }, .. } => name

def nameByArgument: Wrap -> Text
  | W ({ name, .. }) => name

test "record fields" := nameByField (W { person = { name = "Ann", age = 3 } }) == "Ann"
  && nameByArgument (W ({ name = "Bo", age = 4 })) == "Bo"
