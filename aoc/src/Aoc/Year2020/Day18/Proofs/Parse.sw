--| The parser reads the puzzle's format, under the part's rules: whatever
--| `precedence.expression` reads is an expression written out whose shape
--| follows the strengths, when each level of `precedence` holds the
--| operators of one strength, the loosest first.

namespace Aoc.Year2020.Day18.Proofs
import Aoc.Year2020.Day18 (..)
import Aoc.Year2020.Day18 (Spec)
import Std (Char, Eq, List, Nat, Parse)

--| Each level holds operators of one strength, from `strength` up by one
--| a level.
def Ranked (strengthOf: Operator → Nat): (strength: Nat) → (levels: List (List Operator)) → Prop
  | strength, [] => Unit
  | strength, [operators, ..tighter] => List.All (operator => strengthOf operator = strength) operators ∧ Ranked strengthOf (strength + 1) tighter

--| What a level of the parser reads: an expression written out, following
--| the strengths, binding at least `strength` strongly.
def Level (strengthOf: Operator → Nat) (strength: Nat) (read: List Char) (expression: Expression): Prop :=
  Spec.Written expression read ∧ Spec.Follows strengthOf expression ∧ Spec.BindsAtLeast strengthOf strength expression

theorem bindsWeaken (strengthOf: Operator → Nat) (strength: Nat): (expression: Expression) →
    Spec.BindsAtLeast strengthOf (strength + 1) expression → Spec.BindsAtLeast strengthOf strength expression
  | Number value, binds => Trivial
  | Operation operator left right, binds => omega
  | Parenthesised inner, binds => Trivial

theorem spacedWritten: (operator: Operator) → (operator.spaced).toList = [' ', Spec.symbol operator, ' ']
  | Plus => rfl
  | Times => rfl

theorem readsOperator (operators: List Operator):
    Parse.Reads (() => operator operators) (read found => found ∈ operators ∧ read = [' ', Spec.symbol found, ' ']) :=
  Parse.readsWeaken (Parse.readsPickBy operators Operator.spaced)
    (read found (Both member same) => Both member (rewrite same in spacedWritten found))

theorem readsOperand (strengthOf: Operator → Nat) (strength: Nat) (expression: () → {Parse} Expression)
    (readsExpression: Parse.Reads expression (Level strengthOf 0)): Parse.Reads (() => operand expression) (Level strengthOf strength) :=
  Parse.readsOneOf _ _
    (Both
      (Parse.readsThen Parse.readsNat (numberRead value number =>
        Parse.readsDone (Number value) _ (Both (rewrite List.appendNil numberRead in number) (Both Trivial Trivial))))
      (Both
        (Parse.readsThen (Parse.readsChar '(') (openRead u opened =>
          Parse.readsThen readsExpression (innerRead inner (Both written (Both follows binds)) =>
            Parse.readsThen (Parse.readsChar ')') (closeRead u2 closed =>
              Parse.readsDone (Parenthesised inner) _
                (Both (Witness innerRead (Both (rewrite opened, closed, List.appendNil [')'] in List.appendAssoc ['('] innerRead [')']) written))
                  (Both follows Trivial))))))
        Trivial))

--| What a step of a chain reads: an operator of the level, then the next
--| level's expression.
def StepRead (strengthOf: Operator → Nat) (strength: Nat) (operators: List Operator) (read: List Char) (found: (Operator, Expression)): Prop :=
  ∃ (rightRead: List Char) =>
    read = [' ', Spec.symbol found.fst, ' '] ++ rightRead ∧ found.fst ∈ operators ∧ Level strengthOf (strength + 1) rightRead found.snd

theorem readsStep (strengthOf: Operator → Nat) (strength: Nat) (operators: List Operator) (term: () → {Parse} Expression)
    (readsTerm: Parse.Reads term (Level strengthOf (strength + 1))): Parse.Reads (() => step operators term) (StepRead strengthOf strength operators) :=
  Parse.readsThen (readsOperator operators) (operatorRead found (Both member spaced) =>
    Parse.readsThen readsTerm (rightRead right level =>
      Parse.readsDone (found, right) _ (Witness rightRead (Both (rewrite spaced, List.appendNil rightRead in rfl) (Both member level)))))

--| Folding the steps from the left keeps what a level reads.
theorem foldSteps (strengthOf: Operator → Nat) (strength: Nat) (operators: List Operator)
    (ranked: List.All (operator => strengthOf operator = strength) operators):
    (steps: List (Operator, Expression)) → (left: Expression) → (leftRead: List Char) → (restRead: List Char) →
      Level strengthOf strength leftRead left → Parse.Each (StepRead strengthOf strength operators) restRead steps →
      Level strengthOf strength (leftRead ++ restRead) (groupLeft left steps)
  | [], left, leftRead, restRead, level, none => rewrite none, List.appendNil leftRead in level
  | [(found, right), ..later], left, leftRead, restRead, Both written (Both follows binds),
    Witness stepRead (Witness laterRead (Both split (Both (Witness rightRead (Both spaced (Both member (Both rightWritten (Both rightFollows rightBinds))))) each))) =>
    let same: strengthOf found = strength := List.allMem _ found operators ranked member
    let combined: Level strengthOf strength (leftRead ++ stepRead) (Operation found left right) :=
      Both (Witness leftRead (Witness rightRead (Both (rewrite spaced in rfl) (Both written rightWritten))))
        (Both (Both (rewrite same in binds) (Both (rewrite same in rightBinds) (Both follows rightFollows))) (omega [same]))
    rewrite split, Eq.sym (List.appendAssoc leftRead stepRead laterRead) in
      foldSteps strengthOf strength operators ranked later (Operation found left right) (leftRead ++ stepRead) laterRead combined each

theorem readsChain (strengthOf: Operator → Nat) (strength: Nat) (operators: List Operator) (term: () → {Parse} Expression)
    (ranked: List.All (operator => strengthOf operator = strength) operators)
    (readsTerm: Parse.Reads term (Level strengthOf (strength + 1))): Parse.Reads (() => chain operators term) (Level strengthOf strength) :=
  Parse.readsThen readsTerm (firstRead first (Both written (Both follows binds)) =>
    Parse.readsThen (Parse.readsMany (() => step operators term) _ (readsStep strengthOf strength operators term readsTerm)) (restRead steps each =>
      let folded := groupLeft first steps
      let level: Level strengthOf strength (firstRead ++ (restRead ++ [])) folded :=
        rewrite List.appendNil restRead in
          foldSteps strengthOf strength operators ranked steps first firstRead restRead
            (Both written (Both follows (bindsWeaken strengthOf strength first binds))) each
      Parse.readsDone folded (read value => Level strengthOf strength (firstRead ++ (restRead ++ read)) value) level))

theorem readsLevel (strengthOf: Operator → Nat) (expression: () → {Parse} Expression) (readsExpression: Parse.Reads expression (Level strengthOf 0)):
    (levels: List (List Operator)) → (strength: Nat) → Ranked strengthOf strength levels →
      Parse.Reads (() => level expression levels) (Level strengthOf strength)
    := levels strength ranked =>
  match levels with
    | [] => readsOperand strengthOf strength expression readsExpression
    | [operators, ..tighter] =>
      readsChain strengthOf strength operators (() => level expression tighter) (And.left ranked)
        (readsLevel strengthOf expression readsExpression tighter (strength + 1) (And.right ranked))

--| A whole expression, under ranked levels, is one written out that
--| follows the strengths.
theorem readsExpression (strengthOf: Operator → Nat) (precedence: Precedence) (ranked: Ranked strengthOf 0 precedence.levels):
    Parse.Reads (() => precedence.expression) (Spec.Means strengthOf) :=
  Parse.readsWeaken
    (Parse.readsRecursive (self => level self precedence.levels) (Level strengthOf 0)
      (self readsSelf => readsLevel strengthOf self readsSelf precedence.levels 0 ranked))
    (read expression (Both written (Both follows binds)) => Both written follows)
