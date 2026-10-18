-- `export` with arms, on its own line and on the signature's line; `[]`
-- patterns.

export def total : List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + total xs

export def describe : List Nat -> Nat
  | []     => 0
  | [x]    => x
  | [x, y] => x + y
  | _      => 100
