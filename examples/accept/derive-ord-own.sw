-- A module's own `Ord` instance replaces the derived one
-- (docs/proposals/interfaces.md §5.11, §7.3): here items are ordered by
-- price, then by name, rather than by name first.

import Std (Eq)

type Item = { name: Text, price: Nat }

theorem Item.byPriceInjective: (x: Item) -> (y: Item) -> (x.price, x.name) = (y.price, y.name) -> x = y
  | { name = n1, price = p1 }, { name = n2, price = p2 }, h =>
    rewrite Eq.cong Pair.fst h, Eq.cong Pair.snd h in rfl

instance Item.instOrd: Ord Item := Ord.byKey ((i: Item) => (i.price, i.name)) Item.byPriceInjective

def tea: Item := { name = "tea", price = 3 }
def jam: Item := { name = "jam", price = 4 }

test "by price" := Ord.compare tea jam == Less
test "sort by price" := List.sort [jam, tea] == [tea, jam]
