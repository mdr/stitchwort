-- expect-error: E-NOT-A-RECORD
-- `.field` needs a record; `Pair` is an ordinary data type.


first : Pair Nat Nat -> Nat
first p = p.fst
