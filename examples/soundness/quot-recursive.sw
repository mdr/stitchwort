-- expect-error: E-POSITIVITY
-- R10 (docs/proposals/map-equality.md §11.2): a data type can't be
-- recursive through a quotient yet; the message says what to write instead.
-- Pairs with accept/mutual-data.sw, a tree and a forest defined together.
type T =
  | Node (kids: Quot (List T) (xs ys => Unit))
