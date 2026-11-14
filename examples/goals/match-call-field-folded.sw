-- After a `match` on the test inside a `decreasing` definition, each arm's
-- goal still shows the field of the call, `(pick n …).items`, not the
-- fuelled helper the call unfolds to (docs/proposals/match-call-field.md
-- §2.2).
import Std (Nat)

type Bag = { items: List Nat }

def empty: Bag := { items = [] }

def pick (n: Nat) (bag: Bag): Bag
    decreasing n
:=
  if n ≤ 1 then bag else pick (n / 2) { items = [n, ..bag.items] } [decreasing := omega]

theorem fits ∀ (n: Nat): (pick n empty).items.length ≤ 100 := match small: Nat.leq n 1 with
  | True => ?
  | False => ?
