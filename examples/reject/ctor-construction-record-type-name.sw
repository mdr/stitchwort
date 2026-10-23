-- expect-error: E-NOT-A-CONSTRUCTOR
-- A record type isn't a constructor: a record literal is written without its
-- name, `({ … }: Item)`.

type Item = { name: Text, price: Nat }

def tea: Item := Item { name = "tea", price = 3 }
