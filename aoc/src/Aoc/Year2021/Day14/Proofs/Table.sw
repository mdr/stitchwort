--| The program's rule table is the puzzle's rules, when no two rules are
--| for the same pair: `Map.fromList` keeps the last rule for a pair, the
--| puzzle's `insertionFor` the first, and with one rule a pair they agree.

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, DecEq, Eq, List, Map, Option, Ord, Void)

--| No rule for `key` in `rules`, if `key` isn't one of their pairs.
theorem findAbsent (key: ElementPair) (rules: List Rule) (absent: key ∉ rules.map (rule => rule.pair)):
    rules.find (rule => rule.pair == key) = None :=
  match found: List.find rules (rule => rule.pair == key) with
    | None => rfl
    | Some rule =>
      let (Both passes member) := List.findSome rules (rule => rule.pair == key) rule found
      let same := passes.read
      Void.exfalso (absent (rewrite <- same in List.memMap rules rule member (rule => rule.pair)))

theorem lookupRules (key: ElementPair) (rules: List Rule) (h: OneRulePerPair rules):
    Map.lookupLast key (rules.map (rule => (rule.pair, rule.insert))) = Option.map (rules.find (rule => rule.pair == key)) (rule => rule.insert) :=
  match rules, h with
    | [], _ => rfl
    | [rule, ..rest], Both fresh distinct =>
      let earlier := lookupRules key rest distinct
      match t: rule.pair == key with
        | True =>
          let same := t.read
          let none := findAbsent key rest (rewrite <- same in fresh)
          let lookupNone: Map.lookupLast key (List.map rest (rule => (rule.pair, rule.insert))) = None := rewrite none at earlier in earlier
          rewrite lookupNone, <- same, Ord.compareSelf rule.pair in rfl
        | False =>
          rewrite <- earlier in
            match found: Map.lookupLast key (List.map rest (rule => (rule.pair, rule.insert))) with
              | Some c => rfl
              | None =>
                match c: Ord.compare key rule.pair with
                  | Equal => Void.exfalso (DecEq.soundFalse rule.pair key t (Eq.sym (Ord.equal key rule.pair c)))
                  | Less => rfl
                  | Greater => rfl

--| The program's table gives each pair the puzzle's insertion...
theorem tableInsertion (rules: List Rule) (one: OneRulePerPair rules) (pair: ElementPair): Map.get (ruleTable rules) pair = insertionFor rules pair :=
  rewrite Map.getFromList pair (rules.map (rule => (rule.pair, rule.insert))) in lookupRules pair rules one

--| ...so a pair becomes in the program what it becomes by the rules.
theorem becomesExpand (rules: List Rule) (one: OneRulePerPair rules) (pair: ElementPair): pair.becomes (ruleTable rules) = expand rules pair :=
  match pair with
    | { first = a, second = b } => rewrite tableInsertion rules one { first = a, second = b } in rfl
