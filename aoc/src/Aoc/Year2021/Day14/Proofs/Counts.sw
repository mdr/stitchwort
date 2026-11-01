-- The program's pair counts stand for the polymer's pairs: every weighted
-- sum of the counts is the same sum over the polymer's pairs
-- (`Represents`). Counting the template's pairs starts it, and a step of
-- the counts keeps it with a step of the polymer (`stepRepresents`): the
-- pair-count abstraction commutes with a step.

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Eq, List, Map, Nat)

-- For every function `f` on pairs, the counts' sum of `f` is the sum of `f`
-- over the polymer's pairs of neighbours.
def Represents (counts: PairCounts) (polymer: List Char): Prop :=
  (f: (Char, Char) → Nat) → weight counts f = List.sumBy (List.zipWithNext polymer) f

-- Each pair with the same count `n`.
theorem entriesWeightAll (f: (Char, Char) → Nat) (n: Nat) (pairs: List (Char, Char)):
    entriesWeight (pairs.map (pair => (pair, n))) f = n * List.sumBy pairs f :=
  rewrite List.sumByMap pairs (entry => entry.snd * f entry.fst) (pair => (pair, n)) in List.sumByMulLeft pairs n f

theorem countPairsRepresents (polymer: List Char): Represents (countPairs polymer) polymer :=
  f =>
    omega [
      weightAddAll f Map.empty (List.map (List.zipWithNext polymer) (pair => (pair, 1))),
      entriesWeightAll f 1 (List.zipWithNext polymer)
    ]

-- Each count goes to the pairs its pair becomes.
theorem stepWeight (table: Map (Char, Char) Char) (counts: PairCounts) (f: (Char, Char) → Nat):
    weight (stepCounts table counts) f = weight counts (pair => List.sumBy (becomes table pair) f) :=
  let entries := (entry: ((Char, Char), Nat)) => becomes table entry.fst |> .map (next => (next, entry.snd))
  calc weight (stepCounts table counts) f
    _ = weight Map.empty f + entriesWeight (List.flatMap (Map.toList counts) entries) f := weightAddAll f Map.empty (List.flatMap (Map.toList counts) entries)
    _ = List.sumBy (Map.toList counts) (entry => entriesWeight (entries entry) f) := List.sumByFlatMap (Map.toList counts) (entry => entry.snd * f entry.fst) entries
    _ = weight counts (pair => List.sumBy (becomes table pair) f) :=
      List.sumByCong (Map.toList counts) (entry => entriesWeight (entries entry) f) (entry => entry.snd * List.sumBy (becomes table entry.fst) f)
        (entry => entriesWeightAll f entry.snd (becomes table entry.fst))

theorem stepRepresents (rules: List Rule) (one: OneRulePerPair rules) (counts: PairCounts) (polymer: List Char) (represents: Represents counts polymer):
    Represents (stepCounts (ruleTable rules) counts) (step rules polymer) :=
  f =>
    calc weight (stepCounts (ruleTable rules) counts) f
      _ = weight counts (pair => List.sumBy (becomes (ruleTable rules) pair) f) := stepWeight (ruleTable rules) counts f
      _ = List.sumBy (List.zipWithNext polymer) (pair => List.sumBy (becomes (ruleTable rules) pair) f) := represents _
      _ = List.sumBy (List.zipWithNext polymer) (pair => List.sumBy (expand rules pair) f) :=
        List.sumByCong (List.zipWithNext polymer) (pair => List.sumBy (becomes (ruleTable rules) pair) f) (pair => List.sumBy (expand rules pair) f)
          (pair => rewrite becomesExpand rules one pair in rfl)
      _ = List.sumBy (List.flatMap (List.zipWithNext polymer) (expand rules)) f := Eq.sym (List.sumByFlatMap (List.zipWithNext polymer) f (expand rules))
      _ = List.sumBy (List.zipWithNext (step rules polymer)) f := rewrite pairsStep rules polymer in rfl

-- After any number of steps, the program's counts stand for the polymer.
theorem iterateRepresents (manual: Manual) (one: OneRulePerPair manual.rules): (steps: Nat) → (counts: PairCounts) → (polymer: List Char) → Represents counts polymer →
    Represents (Nat.iterate steps (stepCounts (ruleTable manual.rules)) counts) (Nat.iterate steps (step manual.rules) polymer)
  | Zero, counts, polymer, represents, f => represents f
  | Succ steps, counts, polymer, represents, f =>
    iterateRepresents manual one steps (stepCounts (ruleTable manual.rules) counts) (step manual.rules polymer) (stepRepresents manual.rules one counts polymer represents) f
