--| The search's three steps, one per branch of `Links.largestFrom`.

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Std (Bool, Eq, Nat, Option, Set, Void)

--| Too few candidates left to beat `best`.
theorem largestPruned ∀ (links: Links) (clique candidates best: Set Computer)
    (pruned: clique.size + candidates.size ≤ best.size):
    links.largestFrom clique candidates best = best :=
  rewrite Links.largestFrom.unfold links clique candidates best then
    match fits: Nat.leq (clique.size + candidates.size) best.size with | True => byComputing

--| No candidates left, and the clique beats `best`.
theorem largestDone ∀ (links: Links) (clique candidates best: Set Computer)
    (beats: best.size < clique.size + candidates.size)
    (found: candidates.popMin = None):
    links.largestFrom clique candidates best = clique :=
  rewrite Links.largestFrom.unfold links clique candidates best, found then
    match fits: Nat.leq (clique.size + candidates.size) best.size with
      | True => Void.impossible (arithmetic [beats, fits])
      | False => byComputing

--| The smallest candidate is in the clique, then not.
theorem largestStep ∀ (links: Links) (clique candidates best: Set Computer)
    (beats: best.size < clique.size + candidates.size)
    (candidate: Computer) (others: Set Computer)
    (found: candidates.popMin = Some (candidate, others)):
    links.largestFrom clique candidates best
      = links.largestFrom clique others
        (links.largestFrom (clique.insert candidate) (links.neighbours candidate |> .intersect others) best) :=
  rewrite Links.largestFrom.unfold links clique candidates best, found then
    match fits: Nat.leq (clique.size + candidates.size) best.size with
      | True => Void.impossible (arithmetic [beats, fits])
      | False => byComputing
