-- The alternatives of a `match` that ends a `let` block, indented further
-- than the block's column.
def f (n: Nat): Nat :=
  let x := n + 1
  match x with
    | 0 => 1
    | k => k

test "match arms indented in a let block" := f 0 == 1 ∧ f 4 == 5
