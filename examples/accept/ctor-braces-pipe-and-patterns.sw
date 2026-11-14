-- Braces after a bracket-declared constructor are a record argument in a
-- pipe too, and in a pattern they are a record pattern on its argument even
-- when the record has a field of the constructor's own name.

import Std (Eq, Nat, Option)

type Item = { name: Text, price: Nat }
type Mode = | Filling | Draining

def put (n: Nat) (mode: Mode) (item: Item): Text := item.name
def pass (n: Nat) [a: Type] (x: a): a := x

def three: Nat := 3

test "the next argument in a pipe" := (three |> put Filling { name = "tea", price = 3 }) == "tea"

test "the same as unpiped, and bracketed" :=
  (pass three Some { name = "t", price = 1 }) == (three |> pass Some { name = "t", price = 1 })

-- `Some` is declared with brackets, so `{ value }` names the record's field
-- `value`, not `Some`'s own.
type Inner = { n: Nat }
type R = { value: Inner }
type Wrap = | MkWrap (value: R)

def Inner.size (i: Inner): Nat := i.n

def bracketed: Wrap → Nat
  | MkWrap { value } => value.size

def optional: Option R → Nat
  | Some { value } => value.size
  | None => 0

test "the record's field" := bracketed (MkWrap { value = { n = 7 } }) == 7 ∧ optional (Some { value = { n = 5 } }) == 5
