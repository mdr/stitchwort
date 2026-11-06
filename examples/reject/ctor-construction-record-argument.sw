-- expect-error: E-UNKNOWN-FIELD
-- Braces right after a constructor declared with its fields in braces name
-- its fields, even when its one field holds a record: the record argument is
-- `Tea ({ … })`, or by field, `Tea { item = { … } }`.

type Item = { name: Text, price: Nat }

type Order = | Tea { item: Item }

def tea: Order := Tea { name = "tea", price = 3 }
