-- SW-847: a let-bound unannotated lambda over a pair can't use `.field`
-- on a component. The lambda is inferred where it is bound, so `item`'s
-- type is an unknown when `.value` is looked up; only the use below fixes
-- it (2024 day 3's Proofs.sw:64 annotates the pair pattern instead).
--
--   $ stitchwort check docs/proposals/postponement/sw847.sw
--
-- reports E-CANNOT-INFER at `item` in `total` (30 Oct 2026).

import Std (List, Nat)

type Item = { value: Nat }

def total (pairs: List (Nat, Item)): Nat :=
  let counted := ((index, item)) => if index < 3 then item.value else 0
  List.sumBy pairs counted

def annotated (pairs: List (Nat, Item)): Nat :=
  let counted := ((index, item): (Nat, Item)) => if index < 3 then item.value else 0
  List.sumBy pairs counted

-- An argument instead of a `let`: postponed today, accepted.
def inline (pairs: List (Nat, Item)): Nat :=
  List.sumBy pairs ((index, item) => if index < 3 then item.value else 0)
