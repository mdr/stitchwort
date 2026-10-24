-- Chapter 3: variants, records and pattern matching.
import Std (List, Nat, Text)

-- begin variant
type Shape =
  | Circle (radius: Nat)
  | Rect (width: Nat) (height: Nat)
  | Dot

def Shape.area: Shape -> Nat
  | Circle radius => 3 * radius * radius
  | Rect width height => width * height
  | Dot => 0

test "area" := (Rect 3 4).area == 12
-- end variant

-- begin recursive
type Expr =
  | Num (value: Int)
  | Add (left: Expr) (right: Expr)
  | Mul (left: Expr) (right: Expr)
  | Neg (inner: Expr)

def Expr.value: Expr -> Int
  | Num n => n
  | Add a b => a.value + b.value
  | Mul a b => a.value * b.value
  | Neg e => -e.value

test "evaluate" := (Add (Num 2) (Mul (Num 3) (Neg (Num 4)))).value == -10
-- end recursive

-- begin record
type Person = {
  name: Text,
  age: Nat
}

def ada: Person := { name = "Ada", age = 36 }

def Person.birthday (person: Person): Person := { person | age = person.age + 1 }

def newborn (name: Text): Person := { name, age = 0 }

test "read a field" := ada.name == "Ada"
test "update" := ada.birthday.age == 37
test "the original is unchanged" := ada.age == 36
test "field punning" := (newborn "Grace").age == 0
-- end record

-- begin record-patterns
def Person.label: Person -> Text
  | { name, age } => "${name} (${age})"

def isAdult: Person -> Bool
  | { age, .. } => age >= 18

test "label" := ada.label == "Ada (36)"
-- end record-patterns

-- begin defaults
type Query = {
  text: Text,
  limit: Nat := 10,
  caseSensitive: Bool := False
}

def simple: Query := { text = "tea" }

test "defaults fill in" := simple.limit == 10 && !simple.caseSensitive
test "or are given" := ({ text = "tea", limit = 3 }: Query).limit == 3
-- end defaults

-- begin named-construction
type Event =
  | Meeting (title: Text) (minutes: Nat := 30) (room: Text)
  | Reminder (title: Text)

def standup: Event := Meeting { title = "Standup", room = "Blue" }
def review: Event := Meeting { title = "Review", minutes = 60, room = "Red" }

def Event.length: Event -> Nat
  | Meeting { minutes, .. } => minutes
  | Reminder _ => 0

test "default minutes" := standup.length == 30
-- end named-construction

-- begin shared-fields
test "every Event has a title" := review.title == "Review"

def retitled: Event := { standup | title = "Daily" }

test "shared-field update" := retitled.title == "Daily" && retitled.length == 30
-- end shared-fields

-- begin nested-patterns
def firstTwo: List Nat -> Text
  | [] => "nothing"
  | [x] => "just ${x}"
  | [x, y, ..rest] => "${x} and ${y}, then ${rest.length} more"

test "list patterns" := firstTwo [1, 2, 3, 4] == "1 and 2, then 2 more"

def simplify: Expr -> Expr
  | Add (Num 0) e => simplify e
  | Mul (Num 1) e => simplify e
  | Neg (Neg e) => simplify e
  | e => e

test "nested patterns" := simplify (Add (Num 0) (Neg (Neg (Num 5)))) == Num 5
-- end nested-patterns

-- begin match
def compareAges (a: Person) (b: Person): Text :=
  match Ord.compare a.age b.age with
    | Less => "${a.name} is younger"
    | Equal => "the same age"
    | Greater => "${a.name} is older"

def both (x: Option Nat) (y: Option Nat): Option Nat :=
  match x, y with
    | Some a, Some b => Some (a + b)
    | _, _ => None
-- end match

-- begin let-patterns
def divide (n: Nat): Text :=
  let (quotient, remainder) := (n / 7, n % 7)
  "${n} = 7 * ${quotient} + ${remainder}"

def total (pairs: List (Text, Nat)): Nat := pairs.foldLeft (sum (_, n) => sum + n) 0

test "let pattern" := divide 23 == "23 = 7 * 3 + 2"
test "lambda pattern" := total [("a", 1), ("b", 2)] == 3
-- end let-patterns

-- begin synonyms
type Grid = List (List Nat)

def Grid.width (grid: Grid): Nat := grid.map (.length) |> .maximum |> .getOrElse 0

test "a synonym is the type it names" := ([[1, 2, 3], [4]]: Grid).width == 3
-- end synonyms

-- begin option
def findAdult (people: List Person): Option Person := people.find isAdult

def adultName (people: List Person): Text :=
  match findAdult people with
    | Some person => person.name
    | None => "nobody"

test "found" := adultName [newborn "Bo", ada] == "Ada"
test "with helpers" := ((findAdult []).map (.name)).getOrElse "nobody" == "nobody"
-- end option
