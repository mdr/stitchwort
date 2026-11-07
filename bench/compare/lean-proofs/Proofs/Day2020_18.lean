import Lib

/-! 2020 day 18, ported from aoc/src/Aoc/Year2020/Day18 (program, Spec/, Proofs/).

Only the proofs that don't go through the parser library are ported (see
bench/compare/lean-proofs/README.md): Stitchwort's other 30 theorems are about
`Std.Parse`'s `Reads` and `Runs`, thousands of lines of library with no Lean
counterpart. What is here is the program's types, the spec, the grammar's own
combinatorics (`chainOf`, `Exact`, `Stop`) and the answer's arithmetic. -/

namespace Day2020_18

inductive Operator | plus | times
  deriving DecidableEq, BEq

def Operator.spaced : Operator → String
  | .plus => " + "
  | .times => " * "

def Operator.apply : Operator → Nat → Nat → Nat
  | .plus, left, right => left + right
  | .times, left, right => left * right

inductive Expression
  | number (value : Nat)
  | operation (operator : Operator) (left right : Expression)
  | parenthesised (inner : Expression)

def Expression.value : Expression → Nat
  | .number value => value
  | .operation operator left right => operator.apply left.value right.value
  | .parenthesised inner => inner.value

structure Precedence where
  levels : List (List Operator)

def samePrecedence : Precedence := ⟨[[.plus, .times]]⟩

def additionFirst : Precedence := ⟨[[.times], [.plus]]⟩

structure Homework where
  expressions : List Expression

def Homework.sum (homework : Homework) : Nat := (homework.expressions.map Expression.value).sum

def Operator.node (operator : Operator) : Expression → Expression → Expression :=
  fun left right => .operation operator left right

-- Spec

def isDigit (char : Char) : Bool := '0' ≤ char && char ≤ '9'

def digitsValue (digits : List Char) : Nat :=
  digits.foldl (fun value digit => value * 10 + (digit.toNat - 48)) 0

def NumberWritten (read : List Char) (number : Nat) : Prop :=
  read ≠ [] ∧ read.all isDigit = true ∧ number = digitsValue read

def symbol : Operator → Char
  | .plus => '+'
  | .times => '*'

def Written : Expression → List Char → Prop
  | .number value, read => NumberWritten read value
  | .operation operator left right, read =>
    ∃ leftRead rightRead,
      read = leftRead ++ [' ', symbol operator, ' '] ++ rightRead ∧ Written left leftRead ∧ Written right rightRead
  | .parenthesised inner, read => ∃ innerRead, read = ['('] ++ innerRead ++ [')'] ∧ Written inner innerRead

def part1Strength (_operator : Operator) : Nat := 0

def part2Strength : Operator → Nat
  | .plus => 1
  | .times => 0

def BindsAtLeast (strengthOf : Operator → Nat) (strength : Nat) : Expression → Prop
  | .number _ => True
  | .operation operator _ _ => strength ≤ strengthOf operator
  | .parenthesised _ => True

def Follows (strengthOf : Operator → Nat) : Expression → Prop
  | .number _ => True
  | .operation operator left right =>
    BindsAtLeast strengthOf (strengthOf operator) left
      ∧ BindsAtLeast strengthOf (strengthOf operator + 1) right
      ∧ Follows strengthOf left
      ∧ Follows strengthOf right
  | .parenthesised inner => Follows strengthOf inner

def value : Expression → Nat
  | .number value => value
  | .operation .plus left right => value left + value right
  | .operation .times left right => value left * value right
  | .parenthesised inner => value inner

-- The parts of Std.Parse the proofs below use

def chainFold (first : α) (steps : List ((α → α → α) × α)) : α :=
  steps.foldl (fun left step => step.1 left step.2) first

def joinReads : List (List Char × α) → List Char
  | [] => []
  | (read, _) :: steps => read ++ joinReads steps

def stepValues : List (List Char × α) → List α
  | [] => []
  | (_, v) :: steps => v :: stepValues steps

-- Proofs/Proofs.sw

theorem valueSpec : ∀ expression : Expression, expression.value = value expression
  | .number _ => rfl
  | .operation .plus left right => by simp only [Expression.value, Operator.apply, value, valueSpec left, valueSpec right]
  | .operation .times left right => by simp only [Expression.value, Operator.apply, value, valueSpec left, valueSpec right]
  | .parenthesised inner => valueSpec inner

theorem sumSpec (homework : Homework) : homework.sum = (homework.expressions.map value).sum := by
  have : homework.expressions.map Expression.value = homework.expressions.map value :=
    List.map_congr_left (fun e _ => valueSpec e)
  rw [Homework.sum, this]

-- Proofs/Parse.sw (the pure parts)

def Ranked (strengthOf : Operator → Nat) : Nat → List (List Operator) → Prop
  | _, [] => True
  | strength, operators :: tighter =>
    (∀ operator ∈ operators, strengthOf operator = strength) ∧ Ranked strengthOf (strength + 1) tighter

theorem samePrecedenceRanked : Ranked part1Strength 0 samePrecedence.levels :=
  ⟨by intro operator _; rfl, trivial⟩

theorem additionFirstRanked : Ranked part2Strength 0 additionFirst.levels := by
  refine ⟨?_, ?_, trivial⟩
  · intro operator member
    cases operator <;> simp_all [part2Strength]
  · intro operator member
    cases operator <;> simp_all [part2Strength]

theorem bindsWeaken (strengthOf : Operator → Nat) (strength : Nat) : ∀ expression : Expression,
    BindsAtLeast strengthOf (strength + 1) expression → BindsAtLeast strengthOf strength expression
  | .number _, _ => trivial
  | .operation operator left right, binds => by simp only [BindsAtLeast] at *; omega
  | .parenthesised _, _ => trivial

theorem spacedWritten : ∀ operator : Operator, operator.spaced.toList = [' ', symbol operator, ' ']
  | .plus => rfl
  | .times => rfl

-- Proofs/Complete.sw (the pure parts)

def size : Expression → Nat
  | .number _ => 1
  | .operation _ left right => 1 + size left + size right
  | .parenthesised inner => 1 + size inner

def Exact (strengthOf : Operator → Nat) : Nat → List (List Operator) → Prop
  | strength, [] => ∀ operator, strengthOf operator < strength
  | strength, operators :: tighter =>
    (∀ operator, operator ∈ operators ↔ strengthOf operator = strength) ∧ Exact strengthOf (strength + 1) tighter

def Stop (strengthOf : Operator → Nat) (strength : Nat) (rest : List Char) : Prop :=
  rest.takeWhile isDigit = []
    ∧ ∀ (operator : Operator) (more : List Char), rest = [' ', symbol operator, ' '] ++ more → strengthOf operator < strength

theorem symbolInjective : ∀ one other : Operator, (symbol one == symbol other) = true → one = other
  | .plus, .plus, _ => rfl
  | .plus, .times, same => by simp [symbol] at same
  | .times, .plus, same => by simp [symbol] at same
  | .times, .times, _ => rfl

def second : List Char → Char
  | _ :: char :: _ => char
  | _ => ' '

def first : List Char → Char
  | char :: _ => char
  | [] => ' '

theorem stopUp (strengthOf : Operator → Nat) (strength : Nat) (rest : List Char) (stop : Stop strengthOf strength rest) :
    Stop strengthOf (strength + 1) rest :=
  ⟨stop.1, fun other more same => by have := stop.2 other more same; omega⟩

theorem stopStep (strengthOf : Operator → Nat) (operator : Operator) (more : List Char) :
    Stop strengthOf (strengthOf operator + 1) ([' ', symbol operator, ' '] ++ more) := by
  refine ⟨rfl, fun other otherMore same => ?_⟩
  have symbols : symbol operator = symbol other := congrArg second same
  have equal := symbolInjective other operator (by rw [symbols]; simp)
  rw [equal]; omega

theorem stopClose (strengthOf : Operator → Nat) (rest : List Char) : Stop strengthOf 0 ([')'] ++ rest) :=
  ⟨rfl, fun other more same => absurd (congrArg (fun chars => first chars == ' ') same) (by simp [first])⟩

theorem stopNil (strengthOf : Operator → Nat) : Stop strengthOf 0 [] :=
  ⟨rfl, fun other more same => absurd same (by simp)⟩

theorem bindsZero (strengthOf : Operator → Nat) : ∀ expression : Expression, BindsAtLeast strengthOf 0 expression
  | .number _ => trivial
  | .operation operator _ _ => Nat.zero_le (strengthOf operator)
  | .parenthesised _ => trivial

theorem sizePositive : ∀ expression : Expression, size expression ≤ 0 → False
  | .number _, small => by simp [size] at small
  | .operation _ _ _, small => by simp only [size] at small; omega
  | .parenthesised _, small => by simp only [size] at small; omega

def NotOperator (operator : Operator) : List Operator → Prop
  | [] => True
  | other :: more => (other == operator) = false ∧ NotOperator operator more

theorem notOperatorSnoc (operator other : Operator) (different : (other == operator) = false) :
    ∀ before : List Operator, NotOperator operator before → NotOperator operator (before ++ [other])
  | [], _ => ⟨different, trivial⟩
  | _ :: more, ⟨here, later⟩ => ⟨here, notOperatorSnoc operator other different more later⟩

def GoodSteps (strengthOf : Operator → Nat) (strength bound : Nat) :
    List (List Char × ((Expression → Expression → Expression) × Expression)) → Prop
  | [] => True
  | (read, combine, right) :: steps =>
    (∃ (operator : Operator) (rightRead : List Char),
      read = [' ', symbol operator, ' '] ++ rightRead
        ∧ strengthOf operator = strength
        ∧ combine = Operator.node operator
        ∧ Written right rightRead
        ∧ Follows strengthOf right
        ∧ BindsAtLeast strengthOf (strength + 1) right
        ∧ size right < bound)
      ∧ GoodSteps strengthOf strength bound steps

theorem goodStepsWeaken (strengthOf : Operator → Nat) (strength bound larger : Nat) (le : bound ≤ larger) :
    ∀ steps : List (List Char × ((Expression → Expression → Expression) × Expression)),
      GoodSteps strengthOf strength bound steps → GoodSteps strengthOf strength larger steps
  | [], _ => trivial
  | (read, combine, right) :: steps, ⟨⟨operator, rightRead, split, same, made, written, follows, binds, small⟩, later⟩ =>
    ⟨⟨operator, rightRead, split, same, made, written, follows, binds, by omega⟩,
      goodStepsWeaken strengthOf strength bound larger le steps later⟩

theorem joinReadsSnoc (read : List Char) (value : α) : ∀ steps : List (List Char × α),
    joinReads (steps ++ [(read, value)]) = joinReads steps ++ read
  | [] => by simp [joinReads]
  | (first, v) :: steps => by
    simp only [List.cons_append, joinReads, joinReadsSnoc read value steps, List.append_assoc]

theorem stepValuesSnoc (read : List Char) (value : α) : ∀ steps : List (List Char × α),
    stepValues (steps ++ [(read, value)]) = stepValues steps ++ [value]
  | [] => rfl
  | (first, v) :: steps => by
    simp only [List.cons_append, stepValues, stepValuesSnoc read value steps]

theorem chainFoldSnoc (start : Expression) (read : List Char) (combine : Expression → Expression → Expression)
    (right : Expression) (steps : List (List Char × ((Expression → Expression → Expression) × Expression))) :
    chainFold start (stepValues (steps ++ [(read, (combine, right))])) =
      combine (chainFold start (stepValues steps)) right := by
  rw [stepValuesSnoc read (combine, right) steps, chainFold, chainFold, List.foldl_append]
  rfl

theorem goodStepsSnoc (strengthOf : Operator → Nat) (strength bound : Nat) (read : List Char)
    (combine : Expression → Expression → Expression) (right : Expression) :
    ∀ steps : List (List Char × ((Expression → Expression → Expression) × Expression)),
      GoodSteps strengthOf strength bound steps →
      (∃ (operator : Operator) (rightRead : List Char),
        read = [' ', symbol operator, ' '] ++ rightRead
          ∧ strengthOf operator = strength
          ∧ combine = Operator.node operator
          ∧ Written right rightRead
          ∧ Follows strengthOf right
          ∧ BindsAtLeast strengthOf (strength + 1) right
          ∧ size right < bound) →
      GoodSteps strengthOf strength bound (steps ++ [(read, (combine, right))])
  | [], _, new => ⟨new, trivial⟩
  | _ :: steps, ⟨here, later⟩, new =>
    ⟨here, goodStepsSnoc strengthOf strength bound read combine right steps later new⟩

theorem chainOf (strengthOf : Operator → Nat) (strength : Nat) :
    ∀ (expression : Expression) (read : List Char), Written expression read → Follows strengthOf expression →
      BindsAtLeast strengthOf strength expression →
      ∃ (start : Expression) (startRead : List Char)
        (steps : List (List Char × ((Expression → Expression → Expression) × Expression))),
        expression = chainFold start (stepValues steps) ∧ read = startRead ++ joinReads steps
          ∧ Written start startRead ∧ Follows strengthOf start ∧ BindsAtLeast strengthOf (strength + 1) start
          ∧ size start ≤ size expression ∧ GoodSteps strengthOf strength (size expression) steps
  | .number v, read, written, follows, _ =>
    ⟨.number v, read, [], rfl, by simp [joinReads], written, follows, trivial, by omega, trivial⟩
  | .parenthesised inner, read, written, follows, _ =>
    ⟨.parenthesised inner, read, [], rfl, by simp [joinReads], written, follows, trivial, by omega, trivial⟩
  | .operation operator left right, read, ⟨leftRead, rightRead, split, leftWritten, rightWritten⟩,
    ⟨leftBinds, rightBinds, leftFollows, rightFollows⟩, binds => by
    by_cases tighter : strength + 1 ≤ strengthOf operator
    · exact ⟨.operation operator left right, read, [], rfl, by simp [joinReads],
        ⟨leftRead, rightRead, split, leftWritten, rightWritten⟩,
        ⟨leftBinds, rightBinds, leftFollows, rightFollows⟩, tighter, by omega, trivial⟩
    · have same : strengthOf operator = strength := by simp only [BindsAtLeast] at binds; omega
      obtain ⟨start, startRead, steps, made, leftSplit, startWritten, startFollows, startBinds, smaller, good⟩ :=
        chainOf strengthOf strength left leftRead leftWritten leftFollows (same ▸ leftBinds)
      refine ⟨start, startRead, steps ++ [([' ', symbol operator, ' '] ++ rightRead, (Operator.node operator, right))],
        ?_, ?_, startWritten, startFollows, startBinds, ?_, ?_⟩
      · rw [chainFoldSnoc, ← made]; rfl
      · rw [joinReadsSnoc, split, leftSplit]; simp only [List.append_assoc]
      · simp only [size]; omega
      · exact goodStepsSnoc strengthOf strength (size (.operation operator left right))
          ([' ', symbol operator, ' '] ++ rightRead) (Operator.node operator) right steps
          (goodStepsWeaken strengthOf strength (size left) (size (.operation operator left right))
            (by simp only [size]; omega) steps good)
          ⟨operator, rightRead, rfl, same, rfl, rightWritten, rightFollows, same ▸ rightBinds, by simp only [size]; omega⟩

theorem afterSteps (strengthOf : Operator → Nat) (strength bound : Nat) (rest : List Char)
    (stop : Stop strengthOf strength rest) :
    ∀ steps : List (List Char × ((Expression → Expression → Expression) × Expression)),
      GoodSteps strengthOf strength bound steps → Stop strengthOf (strength + 1) (joinReads steps ++ rest)
  | [], _ => stopUp strengthOf strength rest stop
  | (read, combine, right) :: steps, ⟨⟨operator, rightRead, split, same, _⟩, later⟩ => by
    simp only [joinReads, split, List.append_assoc]
    rw [← same]
    exact stopStep strengthOf operator (rightRead ++ (joinReads steps ++ rest))

theorem samePrecedenceExact : Exact part1Strength 0 samePrecedence.levels := by
  refine ⟨fun operator => ?_, fun operator => ?_⟩
  · cases operator <;> simp [part1Strength]
  · simp [part1Strength]

theorem additionFirstExact : Exact part2Strength 0 additionFirst.levels := by
  refine ⟨fun operator => ?_, fun operator => ?_, fun operator => ?_⟩
  · cases operator <;> simp [part2Strength]
  · cases operator <;> simp [part2Strength]
  · cases operator <;> simp [part2Strength]

end Day2020_18
