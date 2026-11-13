-- `List.unfold.induct`: the library's `List.unfold` matches `step seed` with
-- a nested pattern, `Some (MkPair v next)`, so its case for that alternative
-- binds `v` and `next` and the equation `step seed = Some (MkPair v next)`.
import Std (Eq, List, Nat, Option, Pair)

-- The list is no longer than the measure of the seed: each `Some` step makes
-- the measure smaller (`shrinks`), by at least the one element it adds.
theorem unfoldLengthLe ∀ (seed: s) (step: s → Option (Pair a s)) (measure: s → Nat)
    (shrinks: ∀ (x y: s) (v: a) => step x = Some (MkPair v y) → measure y < measure x):
    List.length (List.unfold seed step measure shrinks) ≤ measure seed :=
  List.unfold.induct
    (seed step measure shrinks result => List.length result ≤ measure seed)
    (seed step measure shrinks found => omega)
    (seed step measure shrinks v next found ih =>
      let smaller := shrinks seed next v found
      omega)
    seed step measure shrinks
