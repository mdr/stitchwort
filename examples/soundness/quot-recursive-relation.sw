-- expect-error: E-POSITIVITY
-- R13 (docs/proposals/map-equality.md §7.5, §7.6): strict positivity looks
-- at every argument of a quotient, its relation included, where `T` occurs
-- as a function's input. Pairs with `Node` in accept/quot-forms.sw.
type T: Type =
  | Node (kids: Quot Nat (x y => (t: T) -> Unit))
