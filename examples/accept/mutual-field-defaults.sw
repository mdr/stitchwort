-- A field default of a record in a group is checked once the whole group is
-- admitted and derived, so it can compare or show values of a later type
-- and use that type's constructors.

import Std (List, Nat, Option, Text)

-- Uses `==` on a later type of the group (derived with the group).
type A = { kids: List B, empty: Bool := ([]: List B) == [] }

type B = { a: Option A }

-- Uses a later type's constructors and `${…}` on it.
type Item = {
  value: Ex,
  flag: Bool := Lit 1 == Lit 1,
  shown: Text := "${Lit 2}"
}

type Ex = | Lit (n: Nat) | Group (items: List Item)

test "default through a later type's ==" := ({ kids = [] }: A).empty
test "the group still compares" := ({ kids = [] }: A) == { kids = [], empty = True }
test "default with a later constructor" := ({ value = Lit 3 }: Item).flag
test "default shown" := ({ value = Lit 3 }: Item).shown == "Lit 2"
