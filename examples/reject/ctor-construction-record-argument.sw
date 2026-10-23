-- expect-error: E-UNKNOWN-FIELD
-- Braces right after a constructor name its fields, even when its one field
-- holds a record: the record argument is `Some ({ … })`, or by field,
-- `Some { value = { … } }`.

type Item = { name: Text, price: Nat }

def tea: Option Item := Some { name = "tea", price = 3 }
