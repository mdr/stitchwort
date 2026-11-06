--| A line means at most one expression under a part's rules: the grammar
--| is unambiguous. The proof reads the line back with `readLevel`, a pure
--| reader made for it (the program's parser isn't involved), and shows the
--| reader gives back every expression the line means, so two such
--| expressions are the reader's one answer.
--|
--| The reader takes the levels of operators as the program's parser does,
--| loosest first, and `Exact` says they are all the operators, a strength
--| a level. `fuel` bounds the nesting; each completeness lemma says how
--| much is enough.

namespace Aoc.Year2020.Day18.Proofs
import Aoc.Year2020.Day18 (..)
import Aoc.Year2020.Day18 (Spec)
import Std (Bool, Char, DecEq, Eq, Exists, List, Nat, Option, Parse, Void)

def size: Expression → Nat
  | Number value => 1
  | Operation operator left right => 1 + size left + size right
  | Parenthesised inner => 1 + size inner

-- The reader

--| One of `operators` with a space either side, and what follows it.
def stepOperator (operators: List Operator): List Char → Option (Operator, List Char)
  | [space, symbolChar, space2, ..after] =>
    if space == ' ' && space2 == ' ' then (operators.find (operator => Spec.symbol operator == symbolChar)).map (operator => (operator, after)) else None
  | _ => None

def readLevel (all: List (List Operator)) (fuel: Nat) (levels: List (List Operator)) (chars: List Char): Option (Expression, List Char) :=
  match fuel with
    | Zero => None
    | Succ more =>
      match levels with
        | [] => readOperand all more chars
        | [operators, ..tighter] =>
          match readLevel all more tighter chars with
            | Some (first, rest) => readSteps all more operators tighter first rest
            | None => None

def readOperand (all: List (List Operator)) (fuel: Nat) (chars: List Char): Option (Expression, List Char) :=
  match chars.takeWhile Parse.isDigit with
    | [] => readBracketed all fuel chars
    | [digit, ..digits] => Some (Number (Parse.digitsValue [digit, ..digits]), chars.dropWhile Parse.isDigit)

def readBracketed (all: List (List Operator)) (fuel: Nat): List Char → Option (Expression, List Char)
  | [open, ..inside] =>
    if open == '(' then
      match readLevel all fuel all inside with
        | Some (inner, [close, ..after]) => if close == ')' then Some (Parenthesised inner, after) else None
        | _ => None
    else None
  | [] => None

def readSteps (all: List (List Operator)) (fuel: Nat) (operators: List Operator) (tighter: List (List Operator)) (acc: Expression) (chars: List Char):
    Option (Expression, List Char) :=
  match fuel with
    | Zero => None
    | Succ more =>
      match stepOperator operators chars with
        | None => Some (acc, chars)
        | Some (found, after) =>
          match readLevel all more tighter after with
            | Some (right, rest) => readSteps all more operators tighter (Operation found acc right) rest
            | None => None

-- What the reader needs

--| The levels hold every operator, a strength a level, from `strength` up.
def Exact (strengthOf: Operator → Nat): (strength: Nat) → (levels: List (List Operator)) → Prop
  | strength, [] => (operator: Operator) → strengthOf operator < strength
  | strength, [operators, ..tighter] =>
    ((operator: Operator) → (operator ∈ operators ↔ strengthOf operator = strength)) ∧ Exact strengthOf (strength + 1) tighter

--| What comes after an expression at `strength` doesn't continue it: no
--| digit, and no operator binding at least as strongly.
def Stop (strengthOf: Operator → Nat) (strength: Nat) (rest: List Char): Prop :=
  rest.takeWhile Parse.isDigit = []
    ∧ ((operator: Operator) → (more: List Char) → rest = [' ', Spec.symbol operator, ' '] ++ more → strengthOf operator < strength)

--| The reader, given enough fuel, reads `expression` back from what it is
--| written as, up to `rest`.
def Complete (all: List (List Operator)) (strengthOf: Operator → Nat) (levels: List (List Operator)) (strength: Nat) (expression: Expression): Prop :=
  (read: List Char) → (rest: List Char) → Spec.Written expression read → Spec.Follows strengthOf expression
    → Spec.BindsAtLeast strengthOf strength expression → Exact strengthOf strength levels → Stop strengthOf strength rest
    → ∃ (least: Nat) => (fuel: Nat) → least ≤ fuel → readLevel all fuel levels (read ++ rest) = Some (expression, rest)

theorem symbolInjective: (one: Operator) → (other: Operator) → (Spec.symbol one == Spec.symbol other) = True → one = other
  | Plus, Plus, same => rfl
  | Plus, Times, same => Void.exfalso (Bool.falseNotTrue same)
  | Times, Plus, same => Void.exfalso (Bool.falseNotTrue same)
  | Times, Times, same => rfl

def second: List Char → Char
  | [first, char, ..rest] => char
  | _ => ' '

def first: List Char → Char
  | [char, ..rest] => char
  | [] => ' '

theorem stepFound (operators: List Operator) (operator: Operator) (member: operator ∈ operators) (after: List Char):
    stepOperator operators ([' ', Spec.symbol operator, ' '] ++ after) = Some (operator, after) :=
  match found: operators.find (other => Spec.symbol other == Spec.symbol operator) with
    | Some other =>
      let same := symbolInjective other operator (And.left (List.findSome operators _ other found))
      rewrite same in rfl
    | None => Void.exfalso (List.findNoneNotMem operators _ operator (DecEq.refl (Spec.symbol operator)) member found)

theorem stepSound (operators: List Operator) (operator: Operator) (after: List Char):
    (chars: List Char) → stepOperator operators chars = Some (operator, after) → operator ∈ operators ∧ chars = [' ', Spec.symbol operator, ' '] ++ after
  | [], stepped => Void.exfalso (Option.noneNotSome _ stepped)
  | [a], stepped => Void.exfalso (Option.noneNotSome _ stepped)
  | [a, c], stepped => Void.exfalso (Option.noneNotSome _ stepped)
  | [a, c, b, ..rest], stepped =>
    match spaces: a == ' ' && b == ' ' with
      | True =>
        match found: operators.find (other => Spec.symbol other == c) with
          | Some other =>
            let pair := Option.someInjective stepped
            let same: other = operator := Eq.cong (.fst) pair
            let tail: rest = after := Eq.cong (.snd) pair
            let facts := List.findSome operators _ other found
            rewrite <- same, <- tail, DecEq.sound (Bool.andLeft spaces), DecEq.sound (Bool.andRight spaces), DecEq.sound (And.left facts) in
              Both (And.right facts) rfl
          | None => Void.exfalso (Option.noneNotSome _ stepped)
      | False => Void.exfalso (Option.noneNotSome _ stepped)

theorem stepNone (strengthOf: Operator → Nat) (strength: Nat) (operators: List Operator)
    (exact: (operator: Operator) → (operator ∈ operators ↔ strengthOf operator = strength)) (rest: List Char) (stop: Stop strengthOf strength rest):
    stepOperator operators rest = None :=
  match stepped: stepOperator operators rest with
    | None => rfl
    | Some (operator, after) =>
      let facts := stepSound operators operator after rest stepped
      let same := (exact operator).forward (And.left facts)
      let below := And.right stop operator after (And.right facts)
      Void.exfalso (omega [same, below])

theorem stopUp (strengthOf: Operator → Nat) (strength: Nat) (rest: List Char) (stop: Stop strengthOf strength rest): Stop strengthOf (strength + 1) rest :=
  Both (And.left stop) (other more same => omega [And.right stop other more same])

theorem stopStep (strengthOf: Operator → Nat) (operator: Operator) (more: List Char):
    Stop strengthOf (strengthOf operator + 1) ([' ', Spec.symbol operator, ' '] ++ more) :=
  Both rfl (other otherMore same =>
    let symbols: Spec.symbol operator = Spec.symbol other := Eq.cong second same
    let equal := symbolInjective other operator (rewrite symbols in DecEq.refl (Spec.symbol other))
    rewrite equal in omega)

theorem stopClose (strengthOf: Operator → Nat) (rest: List Char): Stop strengthOf 0 ([')'] ++ rest) :=
  Both rfl (other more same => Void.exfalso (Bool.falseNotTrue (Eq.cong (chars => first chars == ' ') same)))

theorem stopNil (strengthOf: Operator → Nat): Stop strengthOf 0 [] :=
  Both rfl (other more same => Void.exfalso (List.nilNotCons _ _ same))

theorem readNumber (all: List (List Operator)) (fuel: Nat) (read: List Char) (value: Nat) (rest: List Char)
    (written: Spec.NumberWritten read value) (noDigit: rest.takeWhile Parse.isDigit = []):
    readOperand all fuel (read ++ rest) = Some (Number value, rest) :=
  match read with
    | [] => Void.exfalso (And.left written rfl)
    | [digit, ..digits] =>
      let digitsAll := And.left (And.right written)
      rewrite List.takeWhileAppend Parse.isDigit rest [digit, ..digits] digitsAll, noDigit, List.appendNil digits in
        rewrite List.dropWhileAppend Parse.isDigit rest [digit, ..digits] digitsAll, List.dropWhileStops Parse.isDigit rest noDigit, And.right (And.right written) in
          rfl

-- A level's chain

--| `expression` is `start` followed by `steps` steps of strength
--| `strength`, written as `read`: each an operator and a right side
--| binding more strongly, grouped from the left.
def Spine (strengthOf: Operator → Nat) (strength: Nat): (steps: Nat) → (expression: Expression) → (start: Expression) → (read: List Char) → Prop
  | Zero, expression, start, read => expression = start ∧ read = []
  | Succ steps, expression, start, read =>
    ∃ (operator: Operator) => ∃ (left: Expression) => ∃ (right: Expression) => ∃ (leftRead: List Char) => ∃ (rightRead: List Char) =>
      expression = Operation operator left right
        ∧ strengthOf operator = strength
        ∧ read = leftRead ++ [' ', Spec.symbol operator, ' '] ++ rightRead
        ∧ Spine strengthOf strength steps left start leftRead
        ∧ Spec.Written right rightRead
        ∧ Spec.Follows strengthOf right
        ∧ Spec.BindsAtLeast strengthOf (strength + 1) right

--| Every expression at a level is its first operand, binding more
--| strongly, followed by a chain of steps.
theorem spine (strengthOf: Operator → Nat) (strength: Nat):
    (expression: Expression) → (read: List Char) → Spec.Written expression read → Spec.Follows strengthOf expression
      → Spec.BindsAtLeast strengthOf strength expression
      → ∃ (start: Expression) => ∃ (startRead: List Char) => ∃ (stepsRead: List Char) => ∃ (steps: Nat) =>
        Spine strengthOf strength steps expression start stepsRead ∧ read = startRead ++ stepsRead ∧ Spec.Written start startRead
          ∧ Spec.Follows strengthOf start ∧ Spec.BindsAtLeast strengthOf (strength + 1) start ∧ size start ≤ size expression
  | Number value, read, written, follows, binds =>
    Witness (Number value) (Witness read (Witness [] (Witness 0 (Both (Both rfl rfl) (Both (Eq.sym (List.appendNil read)) (Both written (Both follows (Both Trivial omega))))))))
  | Parenthesised inner, read, written, follows, binds =>
    Witness (Parenthesised inner) (Witness read (Witness [] (Witness 0 (Both (Both rfl rfl) (Both (Eq.sym (List.appendNil read)) (Both written (Both follows (Both Trivial omega))))))))
  | Operation operator left right, read, Witness leftRead (Witness rightRead (Both split (Both leftWritten rightWritten))),
    Both leftBinds (Both rightBinds (Both leftFollows rightFollows)), binds =>
    if tighter: strength + 1 ≤ strengthOf operator then
      Witness (Operation operator left right) (Witness read (Witness [] (Witness 0 (Both (Both rfl rfl)
        (Both (Eq.sym (List.appendNil read))
          (Both (Witness leftRead (Witness rightRead (Both split (Both leftWritten rightWritten))))
            (Both (Both leftBinds (Both rightBinds (Both leftFollows rightFollows))) (Both tighter omega))))))))
    else
      let same: strengthOf operator = strength := omega [binds, tighter]
      match spine strengthOf strength left leftRead leftWritten leftFollows (rewrite <- same in leftBinds) with
        | Witness start (Witness startRead (Witness stepsRead (Witness steps (Both chain (Both leftSplit (Both startWritten (Both startFollows (Both startBinds smaller)))))))) =>
          let longer: Spine strengthOf strength (Succ steps) (Operation operator left right) start (stepsRead ++ [' ', Spec.symbol operator, ' '] ++ rightRead) :=
            Witness operator (Witness left (Witness right (Witness stepsRead (Witness rightRead
              (Both rfl (Both same (Both rfl (Both chain (Both rightWritten (Both rightFollows (rewrite <- same in rightBinds)))))))))))
          let whole: read = startRead ++ (stepsRead ++ [' ', Spec.symbol operator, ' '] ++ rightRead) :=
            rewrite split, leftSplit in List.appendAssoc startRead stepsRead _
          Witness start (Witness startRead (Witness _ (Witness (Succ steps) (Both longer (Both whole (Both startWritten (Both startFollows (Both startBinds omega))))))))

--| A chain of at least one step starts with an operator of its strength.
theorem spineStarts (strengthOf: Operator → Nat) (strength: Nat):
    (steps: Nat) → (expression: Expression) → (start: Expression) → (read: List Char) → Spine strengthOf strength (Succ steps) expression start read
      → ∃ (operator: Operator) => ∃ (more: List Char) => strengthOf operator = strength ∧ read = [' ', Spec.symbol operator, ' '] ++ more
  | Zero, expression, start, read, Witness operator (Witness left (Witness right (Witness leftRead (Witness rightRead (Both made (Both same (Both split (Both (Both atStart none) rest)))))))) =>
    Witness operator (Witness rightRead (Both same (rewrite split, none in rfl)))
  | Succ steps, expression, start, read, Witness operator (Witness left (Witness right (Witness leftRead (Witness rightRead (Both made (Both same (Both split (Both chain rest)))))))) =>
    match spineStarts strengthOf strength steps left start leftRead chain with
      | Witness first (Witness more (Both firstSame leftSplit)) =>
        Witness first (Witness (more ++ [' ', Spec.symbol operator, ' '] ++ rightRead) (Both firstSame (rewrite split, leftSplit in List.appendAssoc [' ', Spec.symbol first, ' '] more _)))

theorem readStepsStep (all: List (List Operator)) (fuel: Nat) (operators: List Operator) (tighter: List (List Operator)) (acc: Expression)
    (chars: List Char) (found: Operator) (after: List Char) (right: Expression) (rest: List Char)
    (stepped: stepOperator operators chars = Some (found, after)) (read: readLevel all fuel tighter after = Some (right, rest)):
    readSteps all (Succ fuel) operators tighter acc chars = readSteps all fuel operators tighter (Operation found acc right) rest :=
  rewrite stepped, read in rfl

theorem readStepsStop (all: List (List Operator)) (fuel: Nat) (operators: List Operator) (tighter: List (List Operator)) (acc: Expression)
    (chars: List Char) (none: stepOperator operators chars = None): readSteps all (Succ fuel) operators tighter acc chars = Some (acc, chars) :=
  rewrite none in rfl

--| Reading a chain's steps after its start, with enough fuel, gets to the
--| chain's expression, one fuel a step.
theorem loop (all: List (List Operator)) (strengthOf: Operator → Nat) (strength: Nat) (operators: List Operator) (tighter: List (List Operator))
    (exactHere: (operator: Operator) → (operator ∈ operators ↔ strengthOf operator = strength))
    (exactTighter: Exact strengthOf (strength + 1) tighter) (bound: Nat)
    (term: (right: Expression) → size right ≤ bound → Complete all strengthOf tighter (strength + 1) right):
    (steps: Nat) → (expression: Expression) → (start: Expression) → (read: List Char) → Spine strengthOf strength steps expression start read
      → size expression ≤ bound + 1 → (rest: List Char) → Stop strengthOf (strength + 1) rest
      → ∃ (least: Nat) => (fuel: Nat) → least ≤ fuel
        → readSteps all (fuel + steps) operators tighter start (read ++ rest) = readSteps all fuel operators tighter expression rest
  | Zero, expression, start, read, Both same none, small, rest, stop =>
    Witness 0 (fuel enough => rewrite same, none in rfl)
  | Succ steps, expression, start, read,
    Witness operator (Witness left (Witness right (Witness leftRead (Witness rightRead (Both made (Both same (Both split (Both chain (Both rightWritten (Both rightFollows rightBinds)))))))))),
    small, rest, stop =>
    let sizes: size expression = 1 + size left + size right := rewrite made in rfl
    let after := [' ', Spec.symbol operator, ' '] ++ (rightRead ++ rest)
    let afterStops: Stop strengthOf (strength + 1) after := rewrite <- same in stopStep strengthOf operator (rightRead ++ rest)
    match loop all strengthOf strength operators tighter exactHere exactTighter bound term steps left start leftRead chain (omega [sizes, small]) after afterStops with
      | Witness leftLeast leftLoop =>
        match term right (omega [sizes, small]) rightRead rest rightWritten rightFollows rightBinds exactTighter stop with
          | Witness rightLeast rightReads =>
            Witness (leftLeast + rightLeast) (fuel enough =>
              let member := (exactHere operator).backward same
              let shifted: fuel + Succ steps = Succ fuel + steps := omega
              let whole: read ++ rest = leftRead ++ after := rewrite split in List.appendAssoc leftRead _ rest
              let moved: readSteps all (fuel + Succ steps) operators tighter start (read ++ rest) = readSteps all (Succ fuel + steps) operators tighter start (leftRead ++ after) :=
                Eq.trans (Eq.cong (more => readSteps all more operators tighter start (read ++ rest)) shifted)
                  (Eq.cong (chars => readSteps all (Succ fuel + steps) operators tighter start chars) whole)
              let stepped := readStepsStep all fuel operators tighter left after operator (rightRead ++ rest) right rest
                (stepFound operators operator member (rightRead ++ rest)) (rightReads fuel (omega [enough]))
              Eq.trans moved (Eq.trans (leftLoop (Succ fuel) (omega [enough])) (Eq.trans stepped (Eq.cong (built => readSteps all fuel operators tighter built rest) (Eq.sym made)))))

theorem readParenthesised (all: List (List Operator)) (fuel: Nat) (inside: List Char) (inner: Expression) (after: List Char)
    (read: readLevel all fuel all inside = Some (inner, [')'] ++ after)): readOperand all fuel (['('] ++ inside) = Some (Parenthesised inner, after) :=
  rewrite read in rfl

theorem readLevelChain (all: List (List Operator)) (fuel: Nat) (operators: List Operator) (tighter: List (List Operator)) (chars: List Char)
    (first: Expression) (after: List Char) (read: readLevel all fuel tighter chars = Some (first, after)):
    readLevel all (Succ fuel) [operators, ..tighter] chars = readSteps all fuel operators tighter first after :=
  rewrite read in rfl

theorem bindsZero (strengthOf: Operator → Nat): (expression: Expression) → Spec.BindsAtLeast strengthOf 0 expression
  | Number value => Trivial
  | Operation operator left right => Nat.zeroLe (strengthOf operator)
  | Parenthesised inner => Trivial

theorem sizePositive: (expression: Expression) → size expression ≤ 0 → Void
  | Number value, small => omega
  | Operation operator left right, small => omega
  | Parenthesised inner, small => omega

--| What follows a chain's first operand stops it at the next strength.
theorem afterStart (strengthOf: Operator → Nat) (strength: Nat) (rest: List Char) (stop: Stop strengthOf strength rest):
    (steps: Nat) → (expression: Expression) → (start: Expression) → (stepsRead: List Char) → Spine strengthOf strength steps expression start stepsRead
      → Stop strengthOf (strength + 1) (stepsRead ++ rest)
  | Zero, expression, start, stepsRead, Both same none => rewrite none in stopUp strengthOf strength rest stop
  | Succ steps, expression, start, stepsRead, chain =>
    match spineStarts strengthOf strength steps expression start stepsRead chain with
      | Witness operator (Witness more (Both same split)) =>
        rewrite split, <- same in stopStep strengthOf operator (more ++ rest)

--| Completeness one size up, given it for smaller expressions: by the
--| levels, and at the last level by the operand.
theorem levelInner (all: List (List Operator)) (strengthOf: Operator → Nat) (exactAll: Exact strengthOf 0 all) (bound: Nat)
    (smaller: (levels: List (List Operator)) → (strength: Nat) → (expression: Expression) → size expression ≤ bound → Complete all strengthOf levels strength expression):
    (levels: List (List Operator)) → (strength: Nat) → (expression: Expression) → size expression ≤ bound + 1 → Complete all strengthOf levels strength expression
    := levels =>
  match levels with
    | [] => strength expression small =>
      match expression with
        | Number value => read rest written follows binds exact stop =>
          Witness 1 (fuel enough =>
            match fuel with
              | Zero => Void.exfalso (omega [enough])
              | Succ more => readNumber all more read value rest written (And.left stop))
        | Operation operator left right => read rest written follows binds exact stop => Void.exfalso (omega [binds, exact operator])
        | Parenthesised inner => read rest written follows binds exact stop =>
          match written with
            | Witness innerRead (Both split innerWritten) =>
              match smaller all 0 inner (omega [small]) innerRead ([')'] ++ rest) innerWritten follows (bindsZero strengthOf inner) exactAll (stopClose strengthOf rest) with
                | Witness least reads =>
                  Witness (Succ least) (fuel enough =>
                    match fuel with
                      | Zero => Void.exfalso (omega [enough])
                      | Succ more =>
                        let chars: read ++ rest = ['('] ++ (innerRead ++ ([')'] ++ rest)) :=
                          rewrite split in Eq.cong (Cons '(') (List.appendAssoc innerRead [')'] rest)
                        Eq.trans (Eq.cong (input => readOperand all more input) chars)
                          (readParenthesised all more (innerRead ++ ([')'] ++ rest)) inner rest (reads more (omega [enough]))))
    | [operators, ..tighter] => strength expression small => read rest written follows binds exact stop =>
      match spine strengthOf strength expression read written follows binds with
        | Witness start (Witness startRead (Witness stepsRead (Witness steps (Both chain (Both split (Both startWritten (Both startFollows (Both startBinds startSmaller)))))))) =>
          let restStops := afterStart strengthOf strength rest stop steps expression start stepsRead chain
          match levelInner all strengthOf exactAll bound smaller tighter (strength + 1) start (omega [startSmaller, small])
              startRead (stepsRead ++ rest) startWritten startFollows startBinds (And.right exact) restStops with
            | Witness firstLeast firstReads =>
              match loop all strengthOf strength operators tighter (And.left exact) (And.right exact) bound
                  (right rightSmall => smaller tighter (strength + 1) right rightSmall) steps expression start stepsRead chain small rest
                  (stopUp strengthOf strength rest stop) with
                | Witness loopLeast steps2 =>
                  Witness (Succ (firstLeast + loopLeast + steps + 1)) (fuel enough =>
                    match fuel with
                      | Zero => Void.exfalso (omega [enough])
                      | Succ more =>
                        let left := more - steps - 1
                        let shifted: more = Succ left + steps := omega [enough]
                        let chars: read ++ rest = startRead ++ (stepsRead ++ rest) := rewrite split in List.appendAssoc startRead stepsRead rest
                        let first := readLevelChain all more operators tighter (startRead ++ (stepsRead ++ rest)) start (stepsRead ++ rest)
                          (firstReads more (omega [enough]))
                        Eq.trans (Eq.cong (input => readLevel all (Succ more) [operators, ..tighter] input) chars)
                          (Eq.trans first
                            (Eq.trans (Eq.cong (moreFuel => readSteps all moreFuel operators tighter start (stepsRead ++ rest)) shifted)
                              (Eq.trans (steps2 (Succ left) (omega [enough]))
                                (readStepsStop all left operators tighter expression rest (stepNone strengthOf strength operators (And.left exact) rest stop))))))

theorem levelComplete (all: List (List Operator)) (strengthOf: Operator → Nat) (exactAll: Exact strengthOf 0 all):
    (bound: Nat) → (levels: List (List Operator)) → (strength: Nat) → (expression: Expression) → size expression ≤ bound → Complete all strengthOf levels strength expression
    := bound =>
  match bound with
    | Zero => levels strength expression small => Void.exfalso (sizePositive expression small)
    | Succ less => levelInner all strengthOf exactAll less (levelComplete all strengthOf exactAll less)

-- Unambiguity

--| Under rules whose strengths the levels `all` list exactly, a line
--| means at most one expression.
theorem meansUnique (all: List (List Operator)) (strengthOf: Operator → Nat) (exactAll: Exact strengthOf 0 all) (read: List Char)
    (one: Expression) (other: Expression) (means: Spec.Means strengthOf read one) (alsoMeans: Spec.Means strengthOf read other): one = other :=
  match levelComplete all strengthOf exactAll (size one) all 0 one (Nat.leRefl (size one)) read [] (And.left means) (And.right means)
      (bindsZero strengthOf one) exactAll (stopNil strengthOf) with
    | Witness oneLeast oneReads =>
      match levelComplete all strengthOf exactAll (size other) all 0 other (Nat.leRefl (size other)) read [] (And.left alsoMeans) (And.right alsoMeans)
          (bindsZero strengthOf other) exactAll (stopNil strengthOf) with
        | Witness otherLeast otherReads =>
          let fuel := oneLeast + otherLeast
          let both: Some (one, []) = Some (other, []) := Eq.trans (Eq.sym (oneReads fuel (omega))) (otherReads fuel (omega))
          Eq.cong (.fst) (Option.someInjective both)

--| Lines that each mean one expression mean one list of them.
theorem linesUnique (all: List (List Operator)) (strengthOf: Operator → Nat) (exactAll: Exact strengthOf 0 all):
    (lines: List (List Char)) → (ones: List Expression) → (others: List Expression)
      → List.All2 (Spec.Means strengthOf) lines ones → List.All2 (Spec.Means strengthOf) lines others → ones = others
  | [], [], [], none, alsoNone => rfl
  | [line, ..lines], [one, ..ones], [other, ..others], Both means rest, Both alsoMeans alsoRest =>
    rewrite meansUnique all strengthOf exactAll line one other means alsoMeans, linesUnique all strengthOf exactAll lines ones others rest alsoRest in rfl
  | [], [], [other, ..others], none, alsoNone => Void.exfalso alsoNone
  | [], [one, ..ones], others, none, alsoNone => Void.exfalso none
  | [line, ..lines], [], others, none, alsoNone => Void.exfalso none
  | [line, ..lines], [one, ..ones], [], means, alsoNone => Void.exfalso alsoNone

theorem samePrecedenceExact: Exact Spec.part1Strength 0 samePrecedence.levels :=
  Both
    (operator =>
      match operator with
        | Plus => { forward = member => rfl, backward = same => Inl rfl }
        | Times => { forward = member => rfl, backward = same => Inr (Inl rfl) })
    (operator => omega)

theorem differentOperators (one: Operator) (other: Operator) (different: (one == other) = False) (same: one = other): Void :=
  DecEq.soundFalse one other different same

theorem additionFirstExact: Exact Spec.part2Strength 0 additionFirst.levels :=
  Both
    (operator =>
      match operator with
        | Plus => {
          forward = member =>
            match member with
              | Inl same => Void.exfalso (differentOperators Times Plus rfl same)
              | Inr none => Void.exfalso none,
          backward = same => Void.exfalso (omega [same])
        }
        | Times => { forward = member => rfl, backward = same => Inl rfl })
    (Both
      (operator =>
        match operator with
          | Plus => { forward = member => rfl, backward = same => Inl rfl }
          | Times => {
            forward = member =>
              match member with
                | Inl same => Void.exfalso (differentOperators Plus Times rfl same)
                | Inr none => Void.exfalso none,
            backward = same => Void.exfalso (omega [same])
          })
      (operator =>
        match operator with
          | Plus => omega
          | Times => omega))
