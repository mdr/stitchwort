-- expect-error: E-ATTRIBUTE
-- Which of the two would get the key? Write each field in its own brackets.
type Point =
  | MkPoint (@[js.name "x_pos"] x y: Nat)
