-- A line starting with `,` or a closing bracket continues the bracket it's
-- in, however far left it starts. A trailing comma is allowed in lists,
-- tuples and records, in expressions and patterns.
def example : List Text :=
  [ "a", "b"
  , "c", "d"
  , "e" ]

def trailing : List Text := ["a", "b",]

def pair : (Nat, Nat) := (1, 2,)

type Person = { name : Text, age : Nat, }

def ann : Person := { name = "Ann", age = 3, }

def first : List Nat -> Nat
  | [x, y,] => x + y
  | _ => 0

def firstName : Person -> Text
  | { name, age, } => name

def closer : List Nat :=
  [ 1
  , 2
  ]

test "layout" := example.length == 5
test "trailing" := trailing.length == 2
test "pattern" := first [1, 2] == 3
