-- House style for a bracket that spans lines: a comma at the end of each
-- line, no trailing comma after the last item, and the closer on its own
-- line in column 0.
--
-- A line starting with `,` or a closing bracket continues the bracket it's
-- in, however far left it starts. A trailing comma is also allowed in lists,
-- tuples and records, in expressions and patterns.
def example: List Text := [
  "a",
  "b",
  "c",
  "d",
  "e"
]

type Person = {
  name: Text,
  age: Nat
}

def ann: Person := {
  name = "Ann",
  age = 3
}

def grid: List (List Nat) := [
  [1, 2],
  [
    3,
    4
  ]
]

def pair: (Nat, Nat) := (
  1,
  2
)

-- Leading commas still work.
def leading: List Text := [
  "a",
  "b",
  "c",
  "d",
  "e"
]

def trailing: List Text := ["a", "b"]

def pairTrailing: (Nat, Nat) := (1, 2)

type Pet = { name: Text, age: Nat }

def bob: Pet := { name = "Bob", age = 3 }

def first: List Nat → Nat
  | [x, y] => x + y
  | _ => 0

def firstName: Pet → Text
  | { name, age } => name

def closer: List Nat := [
  1,
  2
]

test "layout" := example.length == 5
test "leading" := leading.length == 5
test "record" := ann.age == 3
test "grid" := grid.length == 2
test "pair" := pair == (1, 2)
test "trailing" := trailing.length == 2
test "pattern" := first [1, 2] == 3
