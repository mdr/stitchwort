-- Pairs with soundness/index-proof-conflict.sw: with `P` a data type, its
-- constructors are told apart, so `SameP A B` is empty
-- (docs/proposals/indexed-families.md §6.3.2, test 22).
type P: Type =
  | A
  | B

type SameP (x: P): P -> Prop =
  | R: SameP x x

theorem noAB: SameP A B -> Void
  | ()
