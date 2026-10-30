-- A `.field` on a let-bound lambda's parameter whose type only the `let`'s
-- body fixes (SW-847, docs/proposals/postponement.md). The lambda is
-- inferred where it is bound, so `item`'s type is unknown when `.value` is
-- reached: the `.value` waits, and `List.sumBy pairs counted` says `item` is
-- an `Item`.

import Std (List, Nat)

type Item = { value: Nat }

def total (pairs: List (Nat, Item)): Nat :=
  let counted := ((index, item)) => if index < 3 then item.value else 0
  List.sumBy pairs counted

def annotated (pairs: List (Nat, Item)): Nat :=
  let counted := ((index, item): (Nat, Item)) => if index < 3 then item.value else 0
  List.sumBy pairs counted

-- An argument instead of a `let`: checked after `pairs`, which fixes it.
def inline (pairs: List (Nat, Item)): Nat :=
  List.sumBy pairs ((index, item) => if index < 3 then item.value else 0)

def pairs: List (Nat, Item) := [(0, { value = 5 }), (7, { value = 9 }), (2, { value = 4 })]

test "total" := total pairs == 9

test "as annotated" := total pairs == annotated pairs && total pairs == inline pairs

test "nothing counted" := total [(3, { value = 1 })] == 0
