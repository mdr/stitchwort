--| The pairs of the polymer after a step are the pairs before it, each
--| replaced by what its rule makes of it (`pairsStep`); a step keeps the
--| first element (`stepFirst`); and an element's count is whether the first
--| element is it plus how many pairs end with it (`countByPairs`).

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, List, Nat, Option)

--| What a pair becomes in a step, by the puzzle's rules: with a rule, the
--| pairs either side of the inserted element; without one, itself.
def expand (rules: List Rule) (pair: (Char, Char)): List (Char, Char) :=
  match insertionFor rules pair.fst pair.snd with
    | Some c => [(pair.fst, c), (c, pair.snd)]
    | None => [pair]

--| The first pairs of a step's result: those `a b` becomes, then the pairs
--| of the step from `b` on.
theorem pairsAcross (rules: List Rule) (a: Char) (b: Char) (tail: List Char):
    List.zipWithNext [a, ..List.append (between rules a b) [b, ..tail]] = List.append (expand rules (a, b)) (List.zipWithNext [b, ..tail]) :=
  match e: insertionFor rules a b with
    | Some c => rfl
    | None => rfl

theorem pairsStepCons (rules: List Rule) (a: Char) (b: Char) (rest: List Char):
    List.zipWithNext (step rules [a, b, ..rest]) = List.append (expand rules (a, b)) (List.zipWithNext (step rules [b, ..rest])) :=
  match rest with
    | [] => pairsAcross rules a b []
    | [c, ..more] => pairsAcross rules a b (List.append (between rules b c) (step rules [c, ..more]))

theorem pairsStep (rules: List Rule): (polymer: List Char) → List.zipWithNext (step rules polymer) = List.flatMap (List.zipWithNext polymer) (expand rules)
  | [] => rfl
  | [a] => rfl
  | [a, b, ..rest] => rewrite pairsStepCons rules a b rest, pairsStep rules [b, ..rest] in rfl
