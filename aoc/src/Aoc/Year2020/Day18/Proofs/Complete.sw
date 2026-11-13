--| The converse of `Parse.sw`: every line that means an expression under a
--| part's rules is read as it, and so is a whole input of such lines; and a
--| line means at most one expression, so the grammar is unambiguous. The proof
--| shows the program's own parser reads every expression the line means
--| (`Parse.Runs`, built from Std's completeness lemmas for the parser's
--| pieces), and a parser run from the same text gives one value, so two such
--| expressions are the same.
--|
--| The levels of operators are those of the program's parser, loosest
--| first, and `Exact` says they are all the operators, a strength a level.
--| `limit` bounds the length of what the parenthesised parser is asked to
--| read; each completeness lemma says how much is enough.

namespace Aoc.Year2020.Day18.Proofs
import Aoc.Year2020.Day18 (..)
import Aoc.Year2020.Day18 (Spec)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, Nat, Option, Parse, Result, Text, Void)

def size: Expression → Nat
  | Number value => 1
  | Operation operator left right => 1 + size left + size right
  | Parenthesised inner => 1 + size inner

--| The levels hold every operator, a strength a level, from `strength` up.
def Exact (strengthOf: Operator → Nat): (strength: Nat) → (levels: List (List Operator)) → Prop
  | strength, [] => ∀ (operator: Operator) => strengthOf operator < strength
  | strength, [operators, ..tighter] =>
    (∀ (operator: Operator) => (operator ∈ operators ↔ strengthOf operator = strength)) ∧ Exact strengthOf (strength + 1) tighter

--| What comes after an expression at `strength` doesn't continue it: no
--| digit, and no operator binding at least as strongly.
def Stop (strengthOf: Operator → Nat) (strength: Nat) (rest: List Char): Prop :=
  rest.takeWhile Parse.isDigit = []
    ∧ (∀ (operator: Operator) (more: List Char) => rest = [' ', Spec.symbol operator, ' '] ++ more → strengthOf operator < strength)

theorem symbolInjective (one other: Operator) (same: (Spec.symbol one == Spec.symbol other) = True): one = other :=
  match one, other with
    | Plus, Plus => rfl
    | Times, Times => rfl

def second: List Char → Char
  | [first, char, ..rest] => char
  | _ => ' '

def first: List Char → Char
  | [char, ..rest] => char
  | [] => ' '

theorem stopUp (strengthOf: Operator → Nat) (strength: Nat) (rest: List Char) (stop: Stop strengthOf strength rest): Stop strengthOf (strength + 1) rest :=
  Both (And.left stop) (other more same => omega [And.right stop other more same])

theorem stopStep (strengthOf: Operator → Nat) (operator: Operator) (more: List Char):
    Stop strengthOf (strengthOf operator + 1) ([' ', Spec.symbol operator, ' '] ++ more) :=
  Both rfl (other otherMore same =>
    let symbols: Spec.symbol operator = Spec.symbol other := Eq.cong second same
    let equal := symbolInjective other operator (rewrite symbols in DecEq.refl (Spec.symbol other))
    rewrite equal in omega)

theorem stopClose (strengthOf: Operator → Nat) (rest: List Char): Stop strengthOf 0 ([')'] ++ rest) :=
  Both rfl (other more same => cases)

theorem stopNil (strengthOf: Operator → Nat): Stop strengthOf 0 [] :=
  Both rfl (other more same => Void.exfalso (List.nilNotCons _ _ same))

theorem bindsZero (strengthOf: Operator → Nat) (expression: Expression): Spec.BindsAtLeast strengthOf 0 expression :=
  match expression with
    | Number value => Trivial
    | Operation operator left right => Nat.zeroLe (strengthOf operator)
    | Parenthesised inner => Trivial

theorem sizePositive (expression: Expression) (small: size expression ≤ 0): Void :=
  match expression with
    | Parenthesised inner => omega

-- The parser's pieces

--| What `self`, the parser for inside parentheses, reads: whatever is written
--| as an expression, with nothing after it that continues it, if it is
--| shorter than `limit`.
def SelfRuns (strengthOf: Operator → Nat) (self: () → {Parse} Expression) (limit: Nat): Prop :=
  ∀ (nestedRead nestedRest: List Char) (w: Expression) => Spec.Written w nestedRead → Spec.Follows strengthOf w
    → Stop strengthOf 0 nestedRest → nestedRead.length < limit → Parse.Runs self nestedRead nestedRest w

--| The parser for a level reads `expression`, written as `read`, up to `rest`.
def Complete (strengthOf: Operator → Nat) (self: () → {Parse} Expression) (limit: Nat) (levels: List (List Operator)) (strength: Nat)
    (expression: Expression): Prop :=
  ∀ (read rest: List Char) => read.length ≤ limit → Spec.Written expression read → Spec.Follows strengthOf expression
    → Spec.BindsAtLeast strengthOf strength expression → Exact strengthOf strength levels → Stop strengthOf strength rest
    → Parse.Runs (() => level self levels) read rest expression

theorem runsOperandNumber (self: () → {Parse} Expression) (read: List Char) (rest: List Char) (value: Nat) (written: Spec.NumberWritten read value)
    (noDigit: rest.takeWhile Parse.isDigit = []): Parse.Runs (() => operand self) read rest (Number value) :=
  let digitsRun := Parse.runsNat read rest (And.left written) (And.left (And.right written)) noDigit
  rewrite And.right (And.right written) in
    Parse.runsOneOfFirst
      (() =>
        let value := Parse.nat()
        Number value)
      [() =>
        Parse.char '('
        let inner := self()
        Parse.char ')'
        Parenthesised inner]
      read rest (Number (Parse.digitsValue read))
      (Parse.runsBind Parse.nat (value => Number value) read [] read rest (Parse.digitsValue read) (Number (Parse.digitsValue read))
        (Eq.sym (List.appendNil read)) digitsRun (Parse.runsPure (Number (Parse.digitsValue read)) rest))

theorem runsOperandParen (strengthOf: Operator → Nat) (self: () → {Parse} Expression) (limit: Nat) (selfRuns: SelfRuns strengthOf self limit)
    (innerRead: List Char) (rest: List Char) (inner: Expression) (written: Spec.Written inner innerRead) (follows: Spec.Follows strengthOf inner)
    (small: innerRead.length < limit):
    Parse.Runs (() => operand self) (['('] ++ (innerRead ++ [')'])) rest (Parenthesised inner) :=
  let paren: Parse.Runs (() =>
      Parse.char '('
      let inner := self()
      Parse.char ')'
      Parenthesised inner) (['('] ++ (innerRead ++ [')'])) rest (Parenthesised inner) :=
    Parse.runsBind (() => Parse.char '(')
      (u =>
        let inner := self()
        Parse.char ')'
        Parenthesised inner)
      ['('] (innerRead ++ [')']) (['('] ++ (innerRead ++ [')'])) rest () (Parenthesised inner) rfl (Parse.runsChar '(' ((innerRead ++ [')']) ++ rest))
      (Parse.runsBind self
        (inner =>
          Parse.char ')'
          Parenthesised inner)
        innerRead [')'] (innerRead ++ [')']) rest inner (Parenthesised inner) rfl
        (selfRuns innerRead ([')'] ++ rest) inner written follows (stopClose strengthOf rest) small)
        (Parse.runsBind (() => Parse.char ')') (u => Parenthesised inner) [')'] [] [')'] rest () (Parenthesised inner) (Eq.sym (List.appendNil [')']))
          (Parse.runsChar ')' rest) (Parse.runsPure (Parenthesised inner) rest)))
  Parse.runsOneOfNext
    (() =>
      let value := Parse.nat()
      Number value)
    (() =>
      Parse.char '('
      let inner := self()
      Parse.char ')'
      Parenthesised inner)
    [] (['('] ++ (innerRead ++ [')'])) rest (Parenthesised inner)
    (Parse.declinesBind Parse.nat (value => Number value) (['('] ++ (innerRead ++ [')']) ++ rest)
      (Parse.declinesNat (['('] ++ (innerRead ++ [')']) ++ rest) rfl))
    (Parse.runsOneOfFirst
      (() =>
        Parse.char '('
        let inner := self()
        Parse.char ')'
        Parenthesised inner)
      [] (['('] ++ (innerRead ++ [')'])) rest (Parenthesised inner) paren)

-- The operators

--| `operator` is not `other`: the words differ.
theorem absentOther: ∀ (one other: Operator) => (one == other) = False → ∀ (rest: List Char) =>
    Text.stripPrefixChars one.spaced.toList (other.spaced.toList ++ rest) = None
  | Plus, Plus, different, rest => cases
  | Plus, Times, different, rest => rfl
  | Times, Plus, different, rest => rfl
  | Times, Times, different, rest => cases

--| None of `before` is `operator`.
def NotOperator (operator: Operator): List Operator → Prop
  | [] => Unit
  | [other, ..more] => (other == operator) = False ∧ NotOperator operator more

theorem notOperatorSnoc (operator: Operator) (other: Operator) (different: (other == operator) = False)
    (before: List Operator) (none: NotOperator operator before): NotOperator operator (before ++ [other]) :=
  match before, none with
    | [], none => Both different Trivial
    | [first, ..more], Both here later => Both here (notOperatorSnoc operator other different more later)

theorem wordsAbsentBefore (operator: Operator) (rest: List Char)
    (before: List Operator) (none: NotOperator operator before):
    Parse.WordsAbsent (operator.spaced.toList ++ rest) (before.map (other => (other.spaced, other))) :=
  match before, none with
    | [], none => rfl
    | [other, ..more], Both different later => Both (absentOther other operator different rest) (wordsAbsentBefore operator rest more later)

--| `target`, one of `operators`, none of `before` being it: the parser for `before ++ operators`
--| reads its word and gives it.
theorem runsOperatorFrom (target: Operator) (rest: List Char) (before: List Operator) (notBefore: NotOperator target before)
    (operators: List Operator) (member: target ∈ operators):
    Parse.Runs (() => operator (before ++ operators)) target.spaced.toList rest target :=
  match operators with
    | [first, ..more] =>
      match same: first == target with
        | True =>
          let equal: first = target := same.read
          rewrite <- equal in
            rewrite List.mapAppend before [first, ..more] (other => (other.spaced, other)) in
              Parse.runsPick (before.map (other => (other.spaced, other))) first.spaced first (more.map (other => (other.spaced, other))) rest
                (wordsAbsentBefore first rest before (rewrite equal in notBefore))
        | False =>
          let later: target ∈ more :=
            match member with
              | Inl itIsFirst => cases
              | Inr found => found
          rewrite <- List.appendAssoc before [first] more in
            runsOperatorFrom target rest (before ++ [first]) (notOperatorSnoc target first same before notBefore) more later

theorem runsOperator (target: Operator) (rest: List Char) (operators: List Operator) (member: target ∈ operators):
    Parse.Runs (() => operator operators) [' ', Spec.symbol target, ' '] rest target :=
  let word := runsOperatorFrom target rest [] Trivial operators member
  rewrite spacedWritten target at word in word

--| No word of `operators` comes next, when no operator of the level does.
theorem wordsAbsentAll (rest: List Char)
    (operators: List Operator) (none: (∀ (other: Operator) => other ∈ operators → Text.stripPrefixChars other.spaced.toList rest = None)):
    Parse.WordsAbsent rest (operators.map (other => (other.spaced, other))) :=
  match operators, none with
    | [], none => rfl
    | [first, ..more], absent => Both (absent first (Inl rfl)) (wordsAbsentAll rest more (other member => absent other (Inr member)))

--| After an expression whose operators are `strength`, a `Stop` doesn't start one of them.
theorem stopAbsent (strengthOf: Operator → Nat) (strength: Nat) (rest: List Char) (stop: Stop strengthOf strength rest) (other: Operator)
    (same: strengthOf other = strength): Text.stripPrefixChars other.spaced.toList rest = None :=
  match found: Text.stripPrefixChars other.spaced.toList rest with
    | None => rfl
    | Some more =>
      let forward := Text.stripPrefixCharsForward other.spaced.toList rest found
      let split: rest = [' ', Spec.symbol other, ' '] ++ more := rewrite spacedWritten other at forward in forward
      Void.exfalso (omega [And.right stop other more split, same])

-- A level's chain

--| The steps of a chain at `strength`, as the parser reads them: each an operator of that
--| strength and a right side binding more strongly, smaller than `bound`.
def GoodSteps (strengthOf: Operator → Nat) (strength: Nat) (bound: Nat): List (List Char, (Expression → Expression → Expression, Expression)) → Prop
  | [] => Unit
  | [(read, (combine, right)), ..steps] =>
    (∃ (operator: Operator) => ∃ (rightRead: List Char) =>
      read = [' ', Spec.symbol operator, ' '] ++ rightRead
        ∧ strengthOf operator = strength
        ∧ combine = Operator.node operator
        ∧ Spec.Written right rightRead
        ∧ Spec.Follows strengthOf right
        ∧ Spec.BindsAtLeast strengthOf (strength + 1) right
        ∧ size right < bound)
      ∧ GoodSteps strengthOf strength bound steps

theorem goodStepsWeaken (strengthOf: Operator → Nat) (strength: Nat) (bound: Nat) (larger: Nat) (le: bound ≤ larger)
    (steps: List (List Char, (Expression → Expression → Expression, Expression))) (good: GoodSteps strengthOf strength bound steps): GoodSteps strengthOf strength larger steps :=
  match steps, good with
    | [], good => Trivial
    | [(read, (combine, right)), ..steps], Both (Witness operator (Witness rightRead (Both split (Both same (Both made (Both written (Both follows (Both binds small)))))))) later =>
      Both (Witness operator (Witness rightRead (Both split (Both same (Both made (Both written (Both follows (Both binds (omega [small, le])))))))))
        (goodStepsWeaken strengthOf strength bound larger le steps later)

theorem joinReadsSnoc (read: List Char) (value: a) (steps: List (List Char, a)):
    Parse.joinReads (steps ++ [(read, value)]) = Parse.joinReads steps ++ read :=
  match steps with
    | [] => rewrite List.appendNil read in rfl
    | [(first, v), ..steps] => rewrite joinReadsSnoc read value steps, List.appendAssoc first (Parse.joinReads steps) read in rfl

theorem stepValuesSnoc (read: List Char) (value: a) (steps: List (List Char, a)):
    Parse.stepValues (steps ++ [(read, value)]) = Parse.stepValues steps ++ [value] :=
  match steps with
    | [] => rfl
    | [(first, v), ..steps] => rewrite stepValuesSnoc read value steps in rfl

theorem chainFoldSnoc (start: Expression) (read: List Char) (combine: Expression → Expression → Expression) (right: Expression)
    (steps: List (List Char, (Expression → Expression → Expression, Expression))):
    Parse.chainFold start (Parse.stepValues (steps ++ [(read, (combine, right))])) = combine (Parse.chainFold start (Parse.stepValues steps)) right :=
  rewrite stepValuesSnoc read (combine, right) steps in
    List.foldLeftAppend (Parse.stepValues steps) start [(combine, right)] (left (c, r) => c left r)

theorem goodStepsSnoc (strengthOf: Operator → Nat) (strength: Nat) (bound: Nat) (read: List Char) (combine: Expression → Expression → Expression) (right: Expression)
    (steps: List (List Char, (Expression → Expression → Expression, Expression))) (good: GoodSteps strengthOf strength bound steps)
    (new: (∃ (operator: Operator) => ∃ (rightRead: List Char) =>
      read = [' ', Spec.symbol operator, ' '] ++ rightRead
        ∧ strengthOf operator = strength
        ∧ combine = Operator.node operator
        ∧ Spec.Written right rightRead
        ∧ Spec.Follows strengthOf right
        ∧ Spec.BindsAtLeast strengthOf (strength + 1) right
        ∧ size right < bound)):
    GoodSteps strengthOf strength bound (steps ++ [(read, (combine, right))]) :=
  match steps, good with
    | [], good => Both new Trivial
    | [(first, (c, r)), ..steps], Both here later => Both here (goodStepsSnoc strengthOf strength bound read combine right steps later new)

--| Every expression at a level is its first operand, binding more strongly, followed by a
--| chain of steps, the parser's.
theorem chainOf (strengthOf: Operator → Nat) (strength: Nat)
    (expression: Expression) (read: List Char) (written: Spec.Written expression read) (follows: Spec.Follows strengthOf expression)
    (binds: Spec.BindsAtLeast strengthOf strength expression): ∃ (start: Expression) => ∃ (startRead: List Char) => ∃ (steps: List (List Char, (Expression → Expression → Expression, Expression))) =>
      expression = Parse.chainFold start (Parse.stepValues steps) ∧ read = startRead ++ Parse.joinReads steps ∧ Spec.Written start startRead
        ∧ Spec.Follows strengthOf start ∧ Spec.BindsAtLeast strengthOf (strength + 1) start ∧ size start ≤ size expression
        ∧ GoodSteps strengthOf strength (size expression) steps :=
  match expression, written, follows with
    | Number value, written, follows =>
      Witness (Number value) (Witness read (Witness []
        (Both rfl (Both (Eq.sym (List.appendNil read)) (Both written (Both follows (Both Trivial (Both omega Trivial))))))))
    | Parenthesised inner, written, follows =>
      Witness (Parenthesised inner) (Witness read (Witness []
        (Both rfl (Both (Eq.sym (List.appendNil read)) (Both written (Both follows (Both Trivial (Both omega Trivial))))))))
    | Operation operator left right, Witness leftRead (Witness rightRead (Both split (Both leftWritten rightWritten))), Both leftBinds (Both rightBinds (Both leftFollows rightFollows)) =>
      if tighter: strength + 1 ≤ strengthOf operator then
        Witness (Operation operator left right) (Witness read (Witness []
          (Both rfl (Both (Eq.sym (List.appendNil read))
            (Both (Witness leftRead (Witness rightRead (Both split (Both leftWritten rightWritten))))
              (Both (Both leftBinds (Both rightBinds (Both leftFollows rightFollows))) (Both tighter (Both omega Trivial))))))))
      else
        let same: strengthOf operator = strength := omega [binds, tighter]
        match chainOf strengthOf strength left leftRead leftWritten leftFollows (rewrite <- same in leftBinds) with
          | Witness start (Witness startRead (Witness steps (Both made (Both leftSplit (Both startWritten (Both startFollows (Both startBinds (Both smaller good)))))))) =>
            let rightStep := ([' ', Spec.symbol operator, ' '] ++ rightRead, (Operator.node operator, right))
            Witness start (Witness startRead (Witness (steps ++ [rightStep])
              (Both (rewrite chainFoldSnoc start ([' ', Spec.symbol operator, ' '] ++ rightRead) (Operator.node operator) right steps, <- made in rfl)
                (Both (rewrite joinReadsSnoc ([' ', Spec.symbol operator, ' '] ++ rightRead) (Operator.node operator, right) steps, split, leftSplit in
                    List.appendAssoc startRead (Parse.joinReads steps) ([' ', Spec.symbol operator, ' '] ++ rightRead))
                  (Both startWritten (Both startFollows (Both startBinds (Both omega
                    (goodStepsSnoc strengthOf strength (size (Operation operator left right)) ([' ', Spec.symbol operator, ' '] ++ rightRead) (Operator.node operator) right steps
                      (goodStepsWeaken strengthOf strength (size left) (size (Operation operator left right)) omega steps good)
                      (Witness operator (Witness rightRead (Both rfl (Both same (Both rfl (Both rightWritten (Both rightFollows (Both (rewrite <- same in rightBinds) omega)))))))))))))))))

--| What follows the steps of a chain stops it at the next strength.
theorem afterSteps (strengthOf: Operator → Nat) (strength: Nat) (bound: Nat) (rest: List Char) (stop: Stop strengthOf strength rest)
    (steps: List (List Char, (Expression → Expression → Expression, Expression))) (good: GoodSteps strengthOf strength bound steps):
    Stop strengthOf (strength + 1) (Parse.joinReads steps ++ rest) :=
  match steps, good with
    | [], good => stopUp strengthOf strength rest stop
    | [(read, (combine, right)), ..steps], Both (Witness operator (Witness rightRead (Both split (Both same rest2)))) later =>
      rewrite split, List.appendAssoc ([' ', Spec.symbol operator, ' '] ++ rightRead) (Parse.joinReads steps) rest,
          List.appendAssoc [' ', Spec.symbol operator, ' '] rightRead (Parse.joinReads steps ++ rest), <- same in
        stopStep strengthOf operator (rightRead ++ (Parse.joinReads steps ++ rest))

--| The parser's chain steps run, for the steps of a chain, then decline.
theorem runsSteps (strengthOf: Operator → Nat) (strength: Nat) (operators: List Operator) (term: () → {Parse} Expression) (limit: Nat) (bound: Nat)
    (exactHere: ∀ (other: Operator) => (other ∈ operators ↔ strengthOf other = strength))
    (termRuns: ∀ (right: Expression) => size right < bound → ∀ (rightRead rest: List Char) => rightRead.length ≤ limit → Spec.Written right rightRead
      → Spec.Follows strengthOf right → Spec.BindsAtLeast strengthOf (strength + 1) right → Stop strengthOf (strength + 1) rest → Parse.Runs term rightRead rest right)
    (steps: List (List Char, (Expression → Expression → Expression, Expression))) (rest: List Char) (good: GoodSteps strengthOf strength bound steps)
    (short: (Parse.joinReads steps).length ≤ limit) (stop: Stop strengthOf strength rest):
    Parse.ManyRuns (() => Parse.chainStep term (() => Operator.node (operator operators))) steps rest :=
  match steps, good with
    | [], good =>
      Parse.declinesChainStep term (() => Operator.node (operator operators)) rest
        (Parse.declinesBind (() => operator operators) Operator.node rest
          (Parse.declinesPick (operators.map (other => (other.spaced, other))) rest
            (wordsAbsentAll rest operators (other member => stopAbsent strengthOf strength rest stop other ((exactHere other).forward member)))))
    | [(read, (combine, right)), ..steps], Both (Witness op (Witness rightRead (Both split (Both same (Both made (Both written (Both follows (Both binds small)))))))) later =>
      let readLength: read.length = 3 + rightRead.length := rewrite split in List.lengthAppend [' ', Spec.symbol op, ' '] rightRead
      let total: (Parse.joinReads [(read, (combine, right)), ..steps]).length = read.length + (Parse.joinReads steps).length :=
        List.lengthAppend read (Parse.joinReads steps)
      let afterStops := afterSteps strengthOf strength bound rest stop steps later
      let member := (exactHere op).backward same
      Both (rewrite split in List.consNotNil ' ' _)
        (Both
          (rewrite split, made in
            Parse.runsChainStep term (() => Operator.node (operator operators)) [' ', Spec.symbol op, ' '] rightRead (Parse.joinReads steps ++ rest)
              (Operator.node op) right
              (Parse.runsMap (() => operator operators) Operator.node [' ', Spec.symbol op, ' '] (rightRead ++ (Parse.joinReads steps ++ rest)) op
                (runsOperator op (rightRead ++ (Parse.joinReads steps ++ rest)) operators member))
              (termRuns right small rightRead (Parse.joinReads steps ++ rest) (omega [short, total, readLength]) written follows binds afterStops))
          (runsSteps strengthOf strength operators term limit bound exactHere termRuns steps rest later (omega [short, total, readLength]) stop))

-- Completeness

--| Completeness one size up, given it for smaller expressions: by the
--| levels, and at the last level by the operand.
theorem levelInner (strengthOf: Operator → Nat) (self: () → {Parse} Expression) (limit: Nat) (selfRuns: SelfRuns strengthOf self limit) (bound: Nat)
    (smaller: ∀ (levels: List (List Operator)) (strength: Nat) (expression: Expression) => size expression ≤ bound → Complete strengthOf self limit levels strength expression):
    ∀ (levels: List (List Operator)) (strength: Nat) (expression: Expression) => size expression ≤ bound + 1 → Complete strengthOf self limit levels strength expression
    := levels =>
  match levels with
    | [] => strength expression small =>
      match expression with
        | Number value => read rest short written follows binds exact stop => runsOperandNumber self read rest value written (And.left stop)
        | Operation operator left right => read rest short written follows binds exact stop => Void.exfalso (omega [binds, exact operator])
        | Parenthesised inner => read rest short written follows binds exact stop =>
          match written with
            | Witness innerRead (Both split innerWritten) =>
              let lengths: read.length = innerRead.length + 2 :=
                rewrite split, List.lengthAppend (['('] ++ innerRead) [')'] in rfl
              rewrite split in
                runsOperandParen strengthOf self limit selfRuns innerRead rest inner innerWritten follows (omega [short, lengths])
    | [operators, ..tighter] => strength expression small => read rest short written follows binds exact stop =>
      match chainOf strengthOf strength expression read written follows binds with
        | Witness start (Witness startRead (Witness steps (Both made (Both split (Both startWritten (Both startFollows (Both startBinds (Both startSmaller good)))))))) =>
          let lengths: read.length = startRead.length + (Parse.joinReads steps).length := rewrite split in List.lengthAppend startRead (Parse.joinReads steps)
          let afterStops := afterSteps strengthOf strength (size expression) rest stop steps good
          let runsFirst := levelInner strengthOf self limit selfRuns bound smaller tighter (strength + 1) start (omega [startSmaller, small])
            startRead (Parse.joinReads steps ++ rest) (omega [short, lengths]) startWritten startFollows startBinds (And.right exact) afterStops
          let manyRuns := runsSteps strengthOf strength operators (() => level self tighter) limit (size expression) (And.left exact)
            (right rightSmall rightRead rest2 rightShort rightWritten rightFollows rightBinds rightStop =>
              smaller tighter (strength + 1) right (omega [rightSmall, small]) rightRead rest2 rightShort rightWritten rightFollows rightBinds (And.right exact) rightStop)
            steps rest good (omega [short, lengths]) stop
          rewrite split, made in
            Parse.runsChainLeft (() => level self tighter) (() => Operator.node (operator operators)) startRead start steps rest runsFirst manyRuns

theorem levelComplete (strengthOf: Operator → Nat) (self: () → {Parse} Expression) (limit: Nat) (selfRuns: SelfRuns strengthOf self limit):
    ∀ (bound: Nat) (levels: List (List Operator)) (strength: Nat) (expression: Expression) => size expression ≤ bound → Complete strengthOf self limit levels strength expression
    := bound =>
  match bound with
    | Zero => levels strength expression small => Void.exfalso (sizePositive expression small)
    | Succ less => levelInner strengthOf self limit selfRuns less (levelComplete strengthOf self limit selfRuns less)

--| The program's parser reads any expression its levels allow, written out.
theorem runsExpression (all: List (List Operator)) (strengthOf: Operator → Nat) (exactAll: Exact strengthOf 0 all) (read: List Char) (rest: List Char)
    (expression: Expression) (written: Spec.Written expression read) (follows: Spec.Follows strengthOf expression) (stop: Stop strengthOf 0 rest):
    Parse.Runs (() => Parse.recursive (self => level self all)) read rest expression :=
  Parse.runsRecursive (self => level self all) (nestedRead nestedRest w => Spec.Written w nestedRead ∧ Spec.Follows strengthOf w ∧ Stop strengthOf 0 nestedRest)
    (self shown shownRest w (Both written2 (Both follows2 stop2)) nested =>
      levelComplete strengthOf self shown.length
        (nestedRead nestedRest v nestedWritten nestedFollows nestedStop short =>
          nested nestedRead nestedRest v (Both nestedWritten (Both nestedFollows nestedStop)) short)
        (size w) all 0 w (Nat.leRefl (size w)) shown shownRest (Nat.leRefl shown.length) written2 follows2 (bindsZero strengthOf w) exactAll stop2)
    read rest expression (Both written (Both follows stop))

-- Unambiguity

--| Under rules whose strengths the levels `all` list exactly, a line
--| means at most one expression: the parser gives one value for it.
theorem writtenUnique (all: List (List Operator)) (strengthOf: Operator → Nat) (exactAll: Exact strengthOf 0 all) (read: List Char)
    (one: Expression) (other: Expression) (means: Spec.Means strengthOf read one) (alsoMeans: Spec.Means strengthOf read other): one = other :=
  let ranOne := Parse.runsRun (() => Parse.recursive (self => level self all)) read one
    (runsExpression all strengthOf exactAll read [] one (And.left means) (And.right means) (stopNil strengthOf))
  let ranOther := Parse.runsRun (() => Parse.recursive (self => level self all)) read other
    (runsExpression all strengthOf exactAll read [] other (And.left alsoMeans) (And.right alsoMeans) (stopNil strengthOf))
  Result.okInjective (Eq.trans (Eq.sym ranOne) ranOther)

--| Input whose lines mean expressions under the rules is read as those
--| expressions, when the levels list the rules' operators exactly.
theorem parseComplete (input: Text) (precedence: Precedence) (strengthOf: Operator → Nat) (exact: Exact strengthOf 0 precedence.levels)
    (expressions: List Expression) (means: List.All2 (Spec.Means strengthOf) (input.lines.map Text.toList) expressions):
    Fail.toResult (() => parseHomework input precedence) = Ok ({ expressions }: Homework) :=
  rewrite Fail.toResultThen (() => Parse.eachLine input (() => precedence.expression)) (expressions => ({ expressions }: Homework)) in
    rewrite Parse.runsEachLine input (() => precedence.expression) expressions
      (List.all2Weaken
        (read expression (Both written follows) =>
          runsExpression precedence.levels strengthOf exact read [] expression written follows (stopNil strengthOf))
        _ _ means) in
      rfl

--| Lines that each mean one expression mean one list of them.
theorem linesUnique (all: List (List Operator)) (strengthOf: Operator → Nat) (exactAll: Exact strengthOf 0 all)
    (lines: List (List Char)) (ones others: List Expression) (none: List.All2 (Spec.Means strengthOf) lines ones) (alsoNone: List.All2 (Spec.Means strengthOf) lines others): ones = others :=
  match lines, ones, others, none, alsoNone with
    | [], [], [], none, alsoNone => rfl
    | [line, ..lines], [one, ..ones], [other, ..others], Both means rest, Both alsoMeans alsoRest =>
      rewrite writtenUnique all strengthOf exactAll line one other means alsoMeans, linesUnique all strengthOf exactAll lines ones others rest alsoRest in rfl
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
  different.read same

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
