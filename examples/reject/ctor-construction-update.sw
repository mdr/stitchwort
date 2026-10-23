-- expect-error: E-PARSE
-- An update isn't a named construction.

type Item = { name: Text, price: Nat }

def bump (r: Item): Option Item := Some { r | price = 4 }
