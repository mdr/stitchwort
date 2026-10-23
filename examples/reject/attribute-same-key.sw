-- expect-error: E-JS-NAME-CLASH
type Point =
  | MkPoint (@[js.name "y"] x: Nat) (y: Nat)
