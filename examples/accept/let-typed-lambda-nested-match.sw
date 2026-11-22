-- A typed `let` lambda (`beyond`, as in `Float.Theory.roundsToInfinity`)
-- used by one arm directly and by another inside a nested `match` that
-- waits as a queued check (SW-4598).

import Std (Bool, Nat)

theorem lePick ∀ (p t: Nat) (low: p ≤ t) (pick: (p = 3) ∨ (p = 4)): 3 ≤ t :=
  let beyond: 3 ≤ p → 3 ≤ t := hp => Nat.leTrans 3 p t hp low
  let over: (e: 3 = 3) → 3 ≤ t := e =>
    (match pick with
      | Inl er => beyond (arithmetic [er])
      | Inr er =>
        match c: Nat.leq 3 p with
          | True => beyond (arithmetic [c])
          | False => beyond (arithmetic [er]))
  over byComputing
