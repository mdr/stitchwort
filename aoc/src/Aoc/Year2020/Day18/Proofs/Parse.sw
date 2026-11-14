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
  | strength, [operators, ..tighter] =>
    List.All (operator => strengthOf operator = strength) operators ∧ Ranked strengthOf (strength + 1) tighter

--| What a level of the parser reads: an expression written out, following
--| the strengths, binding at least `strength` strongly.
def Level (strengthOf: Operator → Nat) (strength: Nat) (read: List Char) (expression: Expression): Prop :=
  Spec.Written expression read ∧ Spec.Follows strengthOf expression ∧ Spec.BindsAtLeast strengthOf strength expression

theorem bindsWeaken ∀ (strengthOf: Operator → Nat) (strength: Nat) (expression: Expression)
    (binds: Spec.BindsAtLeast strengthOf (strength + 1) expression):
    Spec.BindsAtLeast strengthOf strength expression :=
  match expression with
    | Number value => Trivial
    | Operation operator left right => omega
    | Parenthesised inner => Trivial

theorem spacedWritten ∀ (operator: Operator): (operator.spaced).toList = [' ', Spec.symbol operator, ' '] :=
  match operator with
    | Plus => rfl
    | Times => rfl

theorem readsOperator ∀ (operators: List Operator):
    Parse.Reads (() => operator operators) (read found => found ∈ operators ∧ read = [' ', Spec.symbol found, ' ']) :=
  Parse.readsWeaken (Parse.readsPickBy operators Operator.spaced) (read found (Both member same) =>
    Both member (rewrite same in spacedWritten found))

theorem readsOperand ∀ (strengthOf: Operator → Nat) (strength: Nat) (expression: () → {Parse} Expression)
    (readsExpression: Parse.Reads expression (Level strengthOf 0)):
    Parse.Reads (() => operand expression) (Level strengthOf strength) :=
  Parse.readsOneOf _ _
    (Both
      (Parse.readsThen Parse.readsNat (numberRead value number =>
        Parse.readsDone (Number value) _ (Both (rewrite List.appendNil numberRead in number) (Both Trivial Trivial))))
      (Both
        (Parse.readsThen (Parse.readsChar '(') (openRead u opened =>
          Parse.readsThen readsExpression (innerRead inner (Both written (Both follows binds)) =>
            Parse.readsThen (Parse.readsChar ')') (closeRead u2 closed =>
              Parse.readsDone
                (Parenthesised inner) _
                (Both
                  (Witness innerRead
                    (Both
                      (rewrite opened, closed, List.appendNil [')'] in List.appendAssoc ['('] innerRead [')'])
                      written))
                  (Both follows Trivial))))))
        Trivial))

theorem readsChain ∀ (strengthOf: Operator → Nat) (strength: Nat)
    (operators: List Operator) (term: () → {Parse} Expression)
    (ranked: List.All (operator => strengthOf operator = strength) operators)
    (readsTerm: Parse.Reads term (Level strengthOf (strength + 1))):
    Parse.Reads (() => chain operators term) (Level strengthOf strength) :=
  Parse.readsChainLeft term
    (() => Operator.node (operator operators))
    (Level strengthOf (strength + 1))
    (read combine =>
      ∃ (found: Operator) => (found ∈ operators ∧ read = [' ', Spec.symbol found, ' ']) ∧ combine = Operator.node found)
    (Level strengthOf strength)
    readsTerm
    (Parse.readsMap (() => operator operators) Operator.node _ (readsOperator operators))
    (read first (Both written (Both follows binds)) =>
      Both written (Both follows (bindsWeaken strengthOf strength first binds)))
    (leftRead operatorRead rightRead left combine right (Both written (Both follows binds)) (Witness found
      (Both (Both member spaced) same)) (Both rightWritten (Both rightFollows rightBinds)) =>
      let sameStrength: strengthOf found = strength := List.allMem _ found operators ranked member
      rewrite same, spaced in
        Both
          (Witness leftRead (Witness rightRead (Both rfl (Both written rightWritten))))
          (Both
            (Both
              (rewrite sameStrength in binds)
              (Both (rewrite sameStrength in rightBinds) (Both follows rightFollows)))
            (omega [sameStrength])))

theorem readsLevel ∀ (strengthOf: Operator → Nat) (expression: () → {Parse} Expression)
    (readsExpression: Parse.Reads expression (Level strengthOf 0))
    (levels: List (List Operator)) (strength: Nat)
    (ranked: Ranked strengthOf strength levels):
    Parse.Reads (() => level expression levels) (Level strengthOf strength) :=
  match levels with
    | [] => readsOperand strengthOf strength expression readsExpression
    | [operators, ..tighter] =>
      readsChain strengthOf strength operators
        (() => level expression tighter)
        (And.left ranked)
        (readsLevel strengthOf expression readsExpression tighter (strength + 1) (And.right ranked))

--| A whole expression, under ranked levels, is one written out that
--| follows the strengths.
theorem readsExpression ∀ (strengthOf: Operator → Nat) (precedence: Precedence)
    (ranked: Ranked strengthOf 0 precedence.levels):
    Parse.Reads (() => precedence.expression) (Spec.Means strengthOf) :=
  Parse.readsWeaken
    (Parse.readsRecursive (self => level self precedence.levels) (Level strengthOf 0) (self readsSelf =>
      readsLevel strengthOf self readsSelf precedence.levels 0 ranked))
    (read expression (Both written (Both follows binds)) => Both written follows)
