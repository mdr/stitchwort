-- `List.unfold`: build a list from a seed. A file of its own: the loop needs
-- a measure to end (`decreasing`, docs/proposals/well-founded-recursion.md),
-- so a program that doesn't unfold doesn't check it.

-- `List.unfold seed step measure shrinks` asks `step` about the seed: `None`
-- ends the list, and `Some (MkPair v next)` puts `v` first and goes on from
-- `next`. It ends because `measure` gets smaller at every `Some`, which
-- `shrinks` proves for every step `step` can take.
def List.unfold (seed: s) (step: s -> Option (Pair a s)) (measure: s -> Nat)
    (shrinks: (x: s) -> (y: s) -> (v: a) -> step x = Some (MkPair v y) -> measure y < measure x): List a
  decreasing measure seed
:=
  match e: step seed with
    | None => Nil
    | Some (MkPair v next) => Cons v (List.unfold next step measure shrinks [decreasing := shrinks seed next v e])
