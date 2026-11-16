-- expect-error: E-PARSE
-- Lean's `record` (and `structure`) and OCaml's record declarations are
-- written as a `type` whose fields are in braces.
record Point where
  x: Nat
  y: Nat
