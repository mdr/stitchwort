--| Day 14 as the puzzle states it, over the program's `Rule` and `Manual`:
--| a step builds the new polymer, element by element, and the answer is
--| read off the polymer's element counts. The proofs (Proofs/) show the
--| program's pair counts give the same answer, for any number of steps.

namespace Aoc.Year2021.Day14.Spec
import Aoc.Year2021.Day14 (ElementPair, Manual, Rule)
import Std (List, Nat, Option)

--| The element the rule for `pair` inserts, if a rule is for it.
def insertionFor (rules: List Rule) (pair: ElementPair): Option Char :=
  rules.find (rule => rule.pair == pair) |> .map (rule => rule.insert)

--| What goes between `a` and `b` in a step: the rule's element, or nothing.
def between (rules: List Rule) (a b: Char): List Char := match insertionFor rules { first = a, second = b } with
  | Some c => [c]
  | None => []

--| One step: between each element and the next, what that pair's rule
--| inserts. Every pair is looked at in the polymer before the step.
def step (rules: List Rule): List Char → List Char
  | [a, b, ..rest] => [a, ..between rules a b ++ step rules [b, ..rest]]
  | polymer => polymer

--| The polymer after `steps` steps.
def afterSteps (steps: Nat) (manual: Manual): List Char := Nat.iterate steps (step manual.rules) manual.template

--| How many times `element` occurs in `polymer`.
def quantity (polymer: List Char) (element: Char): Nat := polymer.count (== element)

--| The quantity of the most common element less that of the least common.
def spreadOf (polymer: List Char): Nat :=
  let quantities := polymer.unique.map (quantity polymer)
  quantities.maximum.getOrElse 0 - quantities.minimum.getOrElse 0

--| The answer after `steps` steps (10 for part 1, 40 for part 2).
def answer (steps: Nat) (manual: Manual): Nat := spreadOf (afterSteps steps manual)

--| No two rules are for the same pair, so "the rule for a pair" means one
--| thing. The puzzle's rules are like this; the parser checks it.
def OneRulePerPair (rules: List Rule): Prop := List.Distinct (rules.map (rule => rule.pair))
