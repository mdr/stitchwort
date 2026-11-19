-- expect-error: E-NO-INDUCT
-- A recursive call inside a `match` that isn't in tail position gets its
-- induction hypothesis under the alternative, with the equation `e = C
-- fields` as a premise (function-induct-nontail-match.sw); a split of an
-- indexed family refines its indices too, which that equation doesn't
-- state, so `sumHeads` gets no `sumHeads.induct`, and the error says why.
import Std (List, Nat, Vec)

def sumHeads: List (Vec Nat 2) → Nat
  | [] => 0
  | [v, ..rest] =>
    Succ
      (match v with
        | VCons x _ => x + sumHeads rest)

theorem sumHeadsPositive ∀ (vs: List (Vec Nat 2)): sumHeads vs ≥ 0 := match induct (sumHeads vs) with
  | eq1 => arithmetic
  | eq2 v rest ih => arithmetic
