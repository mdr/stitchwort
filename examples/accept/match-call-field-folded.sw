-- A field of a call of a `decreasing` definition stays a field of the call,
-- `(pick n empty).items`, rather than a field of what the call unfolds to
-- (docs/proposals/match-call-field.md §2.2; AoC 2024 day 23,
-- `largestFromAnswers`). So a `match` on the call finds it there (it
-- abstracts the call out of the goal, so `h` is then about `result`), and one
-- on the test inside `pick` leaves the call alone, as for `pick n empty`
-- standing alone: each arm's goal still holds the call, which
-- `pick.unfold` then rewrites.
import Std (Nat)

type Bag = { items: List Nat }

def empty: Bag := { items = [] }

def pick (n: Nat) (bag: Bag): Bag
    decreasing n
:=
  if n ≤ 1 then bag else pick (n / 2) { items = [n, ..bag.items] } [decreasing := omega]

theorem callFound ∀ (n: Nat) (h: pick n empty = empty): (pick n empty).items = [] := match same: pick n empty with
  | result => rewrite h in rfl

theorem armsKeepCall ∀ (n: Nat): (pick n empty).items.length = (pick n empty).items.length + 0 :=
  match small: Nat.leq n 1 with
    | True => rewrite pick.unfold n empty, small in rfl
    | False => rewrite pick.unfold n empty, small in rfl

-- The field still computes to the field of the unfolding.
theorem computes: (pick 6 empty).items = [3, 6] := rfl
