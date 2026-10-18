-- `export` with arms, on its own line and on the signature's line; `[]`
-- patterns.

export
total : List Nat -> Nat
total Nil         = 0
total (Cons x xs) = x + total xs

export describe : List Nat -> Nat
describe []     = 0
describe [x]    = x
describe [x, y] = x + y
describe _      = 100
