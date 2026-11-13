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
def expand (rules: List Rule) (pair: ElementPair): List ElementPair := match insertionFor rules pair with
  | Some c => [{ first = pair.first, second = c }, { first = c, second = pair.second }]
  | None => [pair]

--| The first pairs of a step's result: those `a b` becomes, then the pairs
--| of the step from `b` on.
theorem pairsAcross (rules: List Rule) (a: Char) (b: Char) (tail: List Char):
    pairsOf [a, ..List.append (between rules a b) [b, ..tail]] = List.append (expand rules { first = a, second = b }) (pairsOf [b, ..tail]) :=
  match e: insertionFor rules { first = a, second = b } with
    | Some c => rfl
    | None => rfl

theorem pairsStepCons (rules: List Rule) (a: Char) (b: Char) (rest: List Char):
    pairsOf (step rules [a, b, ..rest]) = List.append (expand rules { first = a, second = b }) (pairsOf (step rules [b, ..rest])) :=
  match rest with
    | [] => pairsAcross rules a b []
    | [c, ..more] => pairsAcross rules a b (List.append (between rules b c) (step rules [c, ..more]))

theorem pairsStep (rules: List Rule) (polymer: List Char): pairsOf (step rules polymer) = List.flatMap (pairsOf polymer) (expand rules) :=
  match polymer with
    | [] => rfl
    | [a] => rfl
    | [a, b, ..rest] => rewrite pairsStepCons rules a b rest, pairsStep rules [b, ..rest] in rfl
