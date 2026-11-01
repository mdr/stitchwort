-- The pairs of the polymer after a step are the pairs before it, each
-- replaced by what its rule makes of it (`pairsStep`); a step keeps the
-- first element (`stepFirst`); and an element's count is whether the first
-- element is it plus how many pairs end with it (`countByPairs`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, List, Nat, Option)

-- What a pair becomes in a step, by the puzzle's rules: with a rule, the
-- pairs either side of the inserted element; without one, itself.
def expand (rules: List Rule) (pair: (Char, Char)): List (Char, Char) :=
  match insertionFor rules pair.fst pair.snd with
    | Some c => [(pair.fst, c), (c, pair.snd)]
    | None => [pair]

-- The first pairs of a step's result: those `a b` becomes, then the pairs
-- of the step from `b` on.
theorem pairsAcross (rules: List Rule) (a: Char) (b: Char) (tail: List Char):
    List.zipWithNext (Cons a (List.append (between rules a b) (Cons b tail))) = List.append (expand rules (a, b)) (List.zipWithNext (Cons b tail)) :=
  match e: insertionFor rules a b with
    | Some c => rfl
    | None => rfl

theorem pairsStepCons (rules: List Rule) (a: Char) (b: Char) (rest: List Char):
    List.zipWithNext (step rules (Cons a (Cons b rest))) = List.append (expand rules (a, b)) (List.zipWithNext (step rules (Cons b rest))) :=
  match rest with
    | Nil => pairsAcross rules a b Nil
    | Cons c more => pairsAcross rules a b (List.append (between rules b c) (step rules (Cons c more)))

theorem pairsStep (rules: List Rule): (polymer: List Char) → List.zipWithNext (step rules polymer) = List.flatMap (List.zipWithNext polymer) (expand rules)
  | Nil => rfl
  | Cons a Nil => rfl
  | Cons a (Cons b rest) => rewrite pairsStepCons rules a b rest, pairsStep rules (Cons b rest) in rfl
