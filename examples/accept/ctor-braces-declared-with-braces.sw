-- A constructor declared with its fields in braces is built and matched by
-- field name, and the declaration is what says so: `Circle` and `Square`
-- are the same shape of data, declared in the two styles
-- (docs/proposals/brace-syntax-review.md §5).

import Std (Eq, Nat, Option, Show)

type Shape = | Circle { id: Text, radius: Nat := 1 } | Square (id: Text) (side: Nat := 1)

def circle: Shape := Circle { id = "c" }

def sizeOf: Shape → Nat
  | Circle { radius, .. } => radius
  | Square _ side => side

test "named construction fills the default" := sizeOf circle == 1
test "positional application is the same value" := Circle "c" 1 == circle
test "named arguments fill defaults too" := sizeOf (Square (id := "s")) == 1

-- A braced constructor can still be given a record in brackets, and named by
-- `(f := e)`.
type Item = { name: Text, price: Nat }

type Purchase = | Order { item: Item, note: Text := "" }

def order: Purchase := Order { item = { name = "tea", price = 3 } }
def same: Purchase := Order (item := { name = "tea", price = 3 })
def bracketed: Purchase := Order ({ name = "tea", price = 3 }) "x"

test "the same order" := order == same ∧ bracketed == Order { item = { name = "tea", price = 3 }, note = "x" }

-- `show` prints a braced constructor by field name, and a record in a bracket
-- constructor without brackets, both as source.
test "show by name" := Show.toSource order == "Order { item = { name = \"tea\", price = 3 }, note = \"\" }"
test "show a record argument" :=
  Show.toSource (Some { name = "tea", price = 3 }) == "Some { name = \"tea\", price = 3 }"
