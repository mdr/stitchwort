-- D2086: does Lean print a numeral's pending type in an error message?

-- (1) A mismatch found while `3`'s type is pending.
example : Bool := some 3

-- (2) The same through a `let`.
example : Nat :=
  let x := some 3
  x

-- (3) An equation of numerals against something else.
example : Nat := (0 = 0)
