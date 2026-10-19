-- expect-error: E-PROP-ELIM
-- Propositions defined together can't be matched on to produce data, even
-- one that would qualify on its own (one constructor, whose only field is a
-- proof): a deliberately conservative rule, as in Lean
-- (docs/proposals/mutual-recursion.md §7.3). Matching to produce another
-- proof is fine (accept/mutual-data.sw).
type EvenP: Prop =
  | EvenZero
  | EvenSucc (pred: OddP)

type OddP: Prop =
  | OddSucc (pred: EvenP)

def oddDepth: OddP -> Nat
  | OddSucc e => 1
