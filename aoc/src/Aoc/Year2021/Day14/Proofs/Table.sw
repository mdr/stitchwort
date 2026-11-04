--| The program's rule table is the puzzle's rules, when no two rules are
--| for the same pair: `Map.fromList` keeps the last rule for a pair, the
--| puzzle's `insertionFor` the first, and with one rule a pair they agree.

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, DecEq, Eq, List, Map, Option, Ord, Void)

--| No rule for `key` in `rules`, if `key` isn't one of their pairs.
theorem findAbsent (key: (Char, Char)) (rules: List Rule) (absent: key ∉ rules.map (rule => (rule.left, rule.right))):
    List.find rules (rule => (rule.left, rule.right) == key) = None :=
  match found: List.find rules (rule => (rule.left, rule.right) == key) with
    | None => rfl
    | Some rule =>
      let (Both passes member) := List.findSome rules (rule => (rule.left, rule.right) == key) rule found
      let same := DecEq.sound (rule.left, rule.right) key passes
      Void.exfalso (absent (rewrite <- same in List.memMap rules rule member (rule => (rule.left, rule.right))))

theorem lookupRules (key: (Char, Char)): (rules: List Rule) → OneRulePerPair rules →
    Map.lookupLast key (rules.map (rule => (rule.pair, rule.insert))) = Option.map (rules.find (rule => (rule.left, rule.right) == key)) (rule => rule.insert)
  | [], _ => rfl
  | [rule, ..rest], Both fresh distinct =>
    let earlier := lookupRules key rest distinct
    match t: (rule.left, rule.right) == key with
      | True =>
        let same := DecEq.sound (rule.left, rule.right) key t
        let none := findAbsent key rest (rewrite <- same in fresh)
        let lookupNone: Map.lookupLast key (List.map rest (rule => (Rule.pair rule, rule.insert))) = None := rewrite none at earlier in earlier
        rewrite lookupNone, <- same, Ord.compareSelf (rule.left, rule.right) in rfl
      | False =>
        rewrite <- earlier in
          match found: Map.lookupLast key (List.map rest (rule => (Rule.pair rule, rule.insert))) with
            | Some c => rfl
            | None =>
              match c: Ord.compare key (rule.left, rule.right) with
                | Equal => Void.exfalso (DecEq.soundFalse (rule.left, rule.right) key t (Eq.sym (Ord.equal key (rule.left, rule.right) c)))
                | Less => rfl
                | Greater => rfl

--| The program's table gives each pair the puzzle's insertion...
theorem tableInsertion (rules: List Rule) (one: OneRulePerPair rules) (a: Char) (b: Char): Map.get (ruleTable rules) (a, b) = insertionFor rules a b :=
  rewrite Map.getFromList (a, b) (rules.map (rule => (rule.pair, rule.insert))) in lookupRules (a, b) rules one

--| ...so a pair becomes in the program what it becomes by the rules.
theorem becomesExpand (rules: List Rule) (one: OneRulePerPair rules) (pair: (Char, Char)): becomes (ruleTable rules) pair = expand rules pair :=
  match pair with
    | (a, b) => rewrite tableInsertion rules one a b in rfl
