-- expect-error: E-NOT-EMPTY
-- Matching never tells proofs apart (D137): `A` and `B` are proofs of the
-- same proposition, equal by rule I (docs/core.md, "Proof irrelevance"), so
-- the equation `B = A` is deleted, not a conflict, and `R` is a possible
-- case. Otherwise `noAB` would turn a provable `SameP A B` into `Void`.
-- Pairs with `noAB` in accept/index-proof-conflict-data.sw, where `P` is
-- data (docs/proposals/indexed-families.md §6.3.2, test 22).
type P: Prop = | A | B

type SameP (x: P): P → Prop = | R: SameP x x

theorem noAB: SameP A B → Void
  | ()
