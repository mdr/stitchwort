-- expect-error: E-PARSE
-- The alternatives of a `match` that ends a `let` block must be indented
-- further than the block's column: at the column, each `|` starts a new
-- statement, and the message says to indent them.
def f (n: Nat): Nat :=
  let x := n + 1
  match x with
  | 0 => 1
  | k => k
