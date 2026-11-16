-- expect-warning: W-REWRITE-REPEATEDLY-UNSTATED
-- What `rewrite repeatedly` leaves depends on its rules, so a proof after
-- `then` that relies on its exact form breaks far from the cause when a rule
-- changes. State what is left (`then (t: P)`, a typed `let`), or end with a
-- closer that doesn't depend on the form (`arithmetic`, `cases`).
import Std (List, Nat)

theorem unstated ∀ (xs ys: List Nat) (h: xs = ys): (xs ++ []) ++ [] = ys := rewrite repeatedly [List.appendNil] then h

theorem stated ∀ (xs ys: List Nat) (h: xs = ys): (xs ++ []) ++ [] = ys :=
  rewrite repeatedly [List.appendNil] then (h: xs = ys)
