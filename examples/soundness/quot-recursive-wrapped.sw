-- expect-error: E-POSITIVITY
-- R10 (docs/proposals/map-equality.md §11.2): nor through a type built on a
-- quotient, here a record whose field is one (as `Map` will be). Pairs with
-- accept/mutual-data.sw.
type Bag (a: Type) = { items: Quot (List a) (xs ys => Unit) }

type Tree =
  | Node (label: Nat) (kids: Bag Tree)
