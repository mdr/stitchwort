-- `omega` and `ring` that fail while their goal holds an unknown the
-- declaration will still settle wait for it, whole, and run again on the
-- goal now known, as `rewrite` and `cases` do (stage 7, rule 2, in
-- docs/proposals/postponement.md). Here the lambda comes before the list
-- that says what its parameter is, so `p.fst` waits, and with it the type
-- of the `<` and `*` in the goals.
import Std (Eq, List, Nat)

def mapFirst (f: a → Nat) (xs: List a): List Nat := List.map xs f

def firsts (xs: List (Nat, Nat)): List Nat :=
  mapFirst (p => (let below: p.fst < p.fst + 1 := omega; let twice: p.fst * 2 = p.fst + p.fst := ring; p.fst)) xs
