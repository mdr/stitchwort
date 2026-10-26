namespace Shop

-- The first line puts everything in this file under `Shop`. Names from
-- the library are imported by namespace.
import Std (Option)
import Text (split)

-- A type owns a namespace: its functions are `Item.cost` and so on.
type Item = { name: Text, cents: Nat }

def Item.cost (i: Item) (quantity: Nat): Nat := i.cents * quantity

def parse (line: Text): Option Item :=
  match split line ',' with
    | [name, cents] => cents.toNat |> .map (c => ({ name, cents = c }: Item))
    | _ => None

test "parse" := parse "tea,250" == Some ({ name = "tea", cents = 250 })
test "bad line" := parse "tea" == None
test "cost" := Item.cost { name = "tea", cents = 250 } 3 == 750
