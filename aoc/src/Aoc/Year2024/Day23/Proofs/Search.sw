-- The search's three steps, one per branch of `Links.largestFrom`.

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Std (Bool, Decidable, Eq, Nat, Option, Set, Void)

-- Too few candidates left to beat `best`.
theorem largestPruned (links: Links) (clique: Set Computer) (candidates: Set Computer) (best: Set Computer)
    (pruned: clique.size + candidates.size ≤ best.size): links.largestFrom clique candidates best = best :=
  rewrite Links.largestFrom.unfold links clique candidates best in
  match fits: Nat.leq (clique.size + candidates.size) best.size with
    | True => rfl
    | False => Void.exfalso (omega [pruned, fits])

-- No candidates left, and the clique beats `best`.
theorem largestDone (links: Links) (clique: Set Computer) (candidates: Set Computer) (best: Set Computer)
    (beats: best.size < clique.size + candidates.size) (found: candidates.popMin = None): links.largestFrom clique candidates best = clique :=
  rewrite Links.largestFrom.unfold links clique candidates best, found in
  match fits: Nat.leq (clique.size + candidates.size) best.size with
    | True => Void.exfalso (omega [beats, fits])
    | False => rfl

-- The smallest candidate is in the clique, then not.
theorem largestStep (links: Links) (clique: Set Computer) (candidates: Set Computer) (best: Set Computer)
    (beats: best.size < clique.size + candidates.size) (candidate: Computer) (others: Set Computer)
    (found: candidates.popMin = Some (candidate, others)):
    links.largestFrom clique candidates best
      = links.largestFrom clique others (links.largestFrom (clique.insert candidate) (links.neighbours candidate |> .intersect others) best) :=
  rewrite Links.largestFrom.unfold links clique candidates best, found in
  match fits: Nat.leq (clique.size + candidates.size) best.size with
    | True => Void.exfalso (omega [beats, fits])
    | False =>
      Decidable.elimEq _ _ _ _ (fewer => rfl) (notFewer => Void.exfalso (notFewer (Set.sizePopMin candidates candidate others found)))
