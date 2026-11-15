--| `if`, bodies, blocks and statements read backwards: each parser, on
--| the tokens of its construct, gives the construct, given that the
--| parsers of its parts read theirs. The steps the read-back of a whole
--| tree is built from, after `ExpressionProofs.sw`'s for expressions.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (Bool, Eq, List, NonEmptyList, Option, Parse, Text, Void)

theorem runsKeyword ∀ (layout: Layout) (wanted: Keyword) (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (reserved: token.value.kind = Reserved wanted)
    (allowed: layout.allows token = True):
    Parse.Runs (() => keyword layout wanted) [token] rest () :=
  Parse.runsOne _
    (selectAllowed layout (keywordIs wanted))
    token
    ()
    rest
    (rewrite allowed, reserved in
      match wanted with
        | FnKeyword => rfl
        | LetKeyword => rfl
        | IfKeyword => rfl
        | ThenKeyword => rfl
        | ElseKeyword => rfl)

--| `else` is read where it may stand: on the line, deeper, or starting a
--| line at the statement's own column.
theorem runsElse ∀ (layout: Layout) (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (isElse: token.value.kind = Reserved ElseKeyword)
    (allowed: layout.allowsElse token = True):
    Parse.Runs (() => elseKeyword layout) [token] rest () :=
  state starts honest =>
    match runsSkip token rest state starts honest with
      | Witness m (Both ran after) => Witness m (Both (rewrite starts, isElse, allowed in ran) after)

--| `expressionRule` on an `if`: the keyword, the condition, `then`, a
--| body, `else`, a body.
theorem runsIf ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (ifToken thenToken elseToken: Parse.Located Token)
    (conditionTokens trueTokens falseTokens rest: List (Parse.Located Token))
    (condition: Expr) (whenTrue whenFalse: Body)
    (isIfToken: ifToken.value.kind = Reserved IfKeyword)
    (ifAllowed: layout.allows ifToken = True)
    (isThen: thenToken.value.kind = Reserved ThenKeyword)
    (thenAllowed: layout.allows thenToken = True)
    (isElse: elseToken.value.kind = Reserved ElseKeyword)
    (elseAllowed: layout.allowsElse elseToken = True)
    (runsCondition: Parse.Runs
      (() => self layout)
      conditionTokens
      ([thenToken, ..trueTokens ++ [elseToken, ..falseTokens]] ++ rest)
      condition)
    (runsTrue: Parse.Runs (() => body self layout) trueTokens ([elseToken, ..falseTokens] ++ rest) whenTrue)
    (runsFalse: Parse.Runs (() => body self layout) falseTokens rest whenFalse):
    Parse.Runs
      (() => expressionRule self layout)
      [ifToken, ..conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]]
      rest
      (If condition whenTrue whenFalse) :=
  state starts honest =>
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let condition1 := self layout
          keyword layout ThenKeyword
          let whenTrue1 := body self layout
          elseKeyword layout
          let whenFalse1 := body self layout
          If condition1 whenTrue1 whenFalse1)
        [ifToken]
        (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
        [ifToken, ..conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]]
        rest
        ()
        (If condition whenTrue whenFalse)
        rfl
        (runsSkip ifToken ((conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]) ++ rest))
        (Parse.runsBind
          (() => self layout)
          (condition1 =>
            keyword layout ThenKeyword
            let whenTrue1 := body self layout
            elseKeyword layout
            let whenFalse1 := body self layout
            If condition1 whenTrue1 whenFalse1)
          conditionTokens
          [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
          (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
          rest
          condition
          (If condition whenTrue whenFalse)
          rfl
          runsCondition
          (Parse.runsBind
            (() => keyword layout ThenKeyword)
            (found =>
              let whenTrue1 := body self layout
              elseKeyword layout
              let whenFalse1 := body self layout
              If condition whenTrue1 whenFalse1)
            [thenToken]
            (trueTokens ++ [elseToken, ..falseTokens])
            [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
            rest
            ()
            (If condition whenTrue whenFalse)
            rfl
            (runsKeyword layout ThenKeyword thenToken
              ((trueTokens ++ [elseToken, ..falseTokens]) ++ rest)
              isThen
              thenAllowed)
            (Parse.runsBind
              (() => body self layout)
              (whenTrue1 =>
                elseKeyword layout
                let whenFalse1 := body self layout
                If condition whenTrue1 whenFalse1)
              trueTokens
              [elseToken, ..falseTokens]
              (trueTokens ++ [elseToken, ..falseTokens])
              rest
              whenTrue
              (If condition whenTrue whenFalse)
              rfl
              runsTrue
              (Parse.runsBind
                (() => elseKeyword layout)
                (found => If condition whenTrue (body self layout))
                [elseToken]
                falseTokens
                [elseToken, ..falseTokens]
                rest
                ()
                (If condition whenTrue whenFalse)
                rfl
                (runsElse layout elseToken (falseTokens ++ rest) isElse elseAllowed)
                (Parse.runsMap
                  (() => body self layout)
                  (whenFalse1 => If condition whenTrue whenFalse1)
                  falseTokens
                  rest
                  whenFalse
                  runsFalse)))))
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, ifAllowed, isIfToken in ran) others)

--| An expression as a statement: its value, and the comment on its last
--| token unless it is an `if`.
theorem runsBareStatement ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (state: Parse.State (Parse.Located Token)) (value: Expr)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self layout) [first, ..others] rest value):
    Parse.RunsFrom state
      (() => bareStatement self layout state.at)
      [first, ..others]
      rest
      (Bare value (trailingFor value [first, ..others])) :=
  starts honest =>
    Parse.runsFromBind state
      (() => self layout)
      (value1 => Bare value1 (trailingSince state.at value1))
      [first, ..others]
      []
      [first, ..others]
      rest
      value
      (Bare value (trailingFor value [first, ..others]))
      (Eq.sym (List.appendNil [first, ..others]))
      runsValue
      (middle atRest honest1 offset =>
        Parse.runsFromBindAt middle
          (() => trailingSince state.at value)
          (trailing => Bare value trailing)
          []
          []
          []
          rest
          (trailingFor value [first, ..others])
          (Bare value (trailingFor value [first, ..others]))
          rfl
          (runsTrailingSince state.at middle value first others rest starts (omega [offset]))
          (middle3 atRest3 honest3 offset3 => Parse.runsPure _ rest middle3))
      starts
      honest

--| The body that is one expression, as `inlineBody` reads it.
def bodyOf (value: Expr) (tokens: List (Parse.Located Token)): Body :=
  { statements = [{ blankBefore = False, line = Bare value (trailingFor value tokens) }] }

theorem runsInlineBody ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (value: Expr)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self layout) [first, ..others] rest value):
    Parse.Runs (() => inlineBody self layout) [first, ..others] rest (bodyOf value [first, ..others]) :=
  state =>
    Parse.runsFromMark state
      (start =>
        let line := bareStatement self layout start
        { statements = [{ blankBefore = False, line }] })
      [first, ..others]
      rest
      (bodyOf value [first, ..others])
      (Parse.runsFromBindAt state
        (() => bareStatement self layout state.at)
        (line => { statements = [{ blankBefore = False, line }] })
        [first, ..others]
        []
        [first, ..others]
        rest
        (Bare value (trailingFor value [first, ..others]))
        (bodyOf value [first, ..others])
        (Eq.sym (List.appendNil [first, ..others]))
        (runsBareStatement self layout state value first others rest runsValue)
        (middle atRest honest1 offset => Parse.runsPure _ rest middle))

--| Whether a block follows at `layout`: the next token starts a line
--| deeper than the statement. What `bodyFuel` looks at.
def blockAhead (layout: Layout) (input: List (Parse.Located Token)): Bool := match layout, input with
  | InStatement column _, [token, .._] => token.value.startsLine && token.value.column > column
  | _, _ => False

theorem inlineBodyRun ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (state: Parse.State (Parse.Located Token))
    (inline: blockAhead layout state.at.rest = False):
    Parse.runFrom state (() => (bodyFuel (Succ more) self layout, Parse.mark()))
      = Parse.runFrom state (() => (inlineBody self layout, Parse.mark())) :=
  match layout with
    | InBrackets =>
      match state with
        | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
        | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rfl
    | InStatement column from =>
      match state with
        | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
        | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite inline in rfl

--| `body` where no block follows: one expression.
theorem runsBodyInline ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (value: Expr)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (inline: blockAhead layout [first, ..others] = False)
    (runsValue: Parse.Runs (() => self layout) [first, ..others] rest value):
    Parse.Runs (() => body self layout) [first, ..others] rest (bodyOf value [first, ..others]) :=
  state starts honest =>
    let ahead: blockAhead layout state.at.rest = False := rewrite starts in
      match layout with
        | InBrackets => rfl
        | InStatement column from => inline
    match runsInlineBody self layout value first others rest runsValue state starts honest with
      | Witness m (Both ran after) =>
        Witness m
          (Both
            (Eq.trans
              (Parse.runFromMark state (before => (bodyFuel (before.left + 1) self layout, Parse.mark())))
              (Eq.trans (inlineBodyRun state.at.left self layout state ahead) ran))
            after)

--| The column of the first of the tokens: a block's, when it starts one.
def firstColumn (input: List (Parse.Located Token)): Nat := match input with
  | [token, .._] => token.value.column
  | [] => 0

theorem blockBodyRun ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column from: Nat)
    (state: Parse.State (Parse.Located Token))
    (ahead: blockAhead (InStatement column from) state.at.rest = True):
    Parse.runFrom state (() => (bodyFuel (Succ more) self (InStatement column from), Parse.mark()))
      = Parse.runFrom state (() => (block more self (firstColumn state.at.rest), Parse.mark())) :=
  match state with
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite ahead in rfl

--| `body` where the next token starts a line deeper than the statement: a
--| block at that token's column. The block may nest as deep as there are
--| tokens left.
theorem runsBodyBlock ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (column from: Nat) (found: Body)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (deeper: (first.value.startsLine && first.value.column > column) = True)
    (runsBlock: ∀ (fuel: Nat) => rest.length + others.length < fuel
      → Parse.Runs (() => block fuel self first.value.column) [first, ..others] rest found):
    Parse.Runs (() => body self (InStatement column from)) [first, ..others] rest found :=
  state starts honest =>
    let lengths: state.at.rest.length = Succ (others.length + rest.length) :=
      rewrite starts in rewrite List.lengthAppend others rest in rfl
    let same: firstColumn state.at.rest = first.value.column := rewrite starts in rfl
    let step0 := blockBodyRun state.at.left self column from state (rewrite starts in deeper)
    let step := rewrite same at step0 in step0
    match runsBlock state.at.left (omega [honest, lengths]) state starts honest with
      | Witness m (Both ran after) =>
        Witness m
          (Both
            (Eq.trans
              (Parse.runFromMark state (before =>
                (bodyFuel (before.left + 1) self (InStatement column from), Parse.mark())))
              (Eq.trans step ran))
            after)

--| A statement's line that starts with `let`: a name, `=` and a body.
theorem runsLineLet ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (start: Parse.Mark (Parse.Located Token))
    (first named equals: Parse.Located Token) (bodyTokens rest: List (Parse.Located Token))
    (bound: Text) (found: Body)
    (isLet: first.value.kind = Reserved LetKeyword)
    (isName: named.value.kind = Name bound)
    (nameAllowed: layout.allows named = True)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: layout.allows equals = True)
    (runsBody: Parse.Runs (() => bodyFuel fuel self layout) bodyTokens rest found):
    Parse.Runs
      (() => statementLine fuel self layout start first.value.kind)
      [first, named, equals, ..bodyTokens]
      rest
      (Let bound found) :=
  rewrite isLet in
    Parse.runsBind
      (() => skip())
      (skipped =>
        let bound1 := name layout
        sign layout "'='" Defines
        Let bound1 (bodyFuel fuel self layout))
      [first]
      [named, equals, ..bodyTokens]
      [first, named, equals, ..bodyTokens]
      rest
      ()
      (Let bound found)
      rfl
      (runsSkip first ([named, equals, ..bodyTokens] ++ rest))
      (Parse.runsBind
        (() => name layout)
        (bound1 =>
          sign layout "'='" Defines
          Let bound1 (bodyFuel fuel self layout))
        [named]
        [equals, ..bodyTokens]
        [named, equals, ..bodyTokens]
        rest
        bound
        (Let bound found)
        rfl
        (runsName layout named bound ([equals, ..bodyTokens] ++ rest) isName nameAllowed)
        (Parse.runsBind
          (() => sign layout "'='" Defines)
          (signed => Let bound (bodyFuel fuel self layout))
          [equals]
          bodyTokens
          [equals, ..bodyTokens]
          rest
          ()
          (Let bound found)
          rfl
          (runsSign layout "'='" Defines equals (bodyTokens ++ rest) isEquals equalsAllowed)
          (Parse.runsMap
            (() => bodyFuel fuel self layout)
            (inner => Let bound inner)
            bodyTokens
            rest
            found
            runsBody)))

--| A statement's line that doesn't start with `let` is an expression.
theorem runsLineOther ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (state: Parse.State (Parse.Located Token)) (kind: Kind) (read rest: List (Parse.Located Token)) (line: Statement)
    (notLet: kind ≠ Reserved LetKeyword)
    (runs: Parse.RunsFrom state (() => bareStatement self layout state.at) read rest line):
    Parse.RunsFrom state (() => statementLine fuel self layout state.at kind) read rest line :=
  match kind, notLet with
    | Name text, notLet => runs
    | Number digits, notLet => runs
    | Str written, notLet => runs
    | Sign punctuation, notLet => runs
    | Op operator, notLet => runs
    | Stray text, notLet => runs
    | Reserved keyword, notLet =>
      match keyword, notLet with
        | LetKeyword, notLet => Void.exfalso (notLet rfl)
        | FnKeyword, notLet => runs
        | IfKeyword, notLet => runs
        | ThenKeyword, notLet => runs
        | ElseKeyword, notLet => runs

theorem runsLineBare ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (state: Parse.State (Parse.Located Token)) (value: Expr)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (notLet: first.value.kind ≠ Reserved LetKeyword)
    (runsValue: Parse.Runs (() => self layout) [first, ..others] rest value):
    Parse.RunsFrom state
      (() => statementLine fuel self layout state.at first.value.kind)
      [first, ..others]
      rest
      (Bare value (trailingFor value [first, ..others])) :=
  runsLineOther fuel self layout state first.value.kind
    [first, ..others]
    rest
    (Bare value (trailingFor value [first, ..others]))
    notLet
    (runsBareStatement self layout state value first others rest runsValue)

--| A statement: on tokens whose first starts a line at the block's column,
--| the own-line comments above that token, then the line read from them
--| at the statement's layout.
theorem runsStatement ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token)) (line: Statement)
    (atColumn: (first.value.startsLine && first.value.column == column) = True)
    (runsLine: ∀ (state: Parse.State (Parse.Located Token)) => Parse.RunsFrom state
      (() => statementLine fuel self (InStatement column first.offset) state.at first.value.kind)
      [first, ..others]
      rest
      line):
    Parse.Runs
      (() => statement fuel self column)
      [first, ..others]
      rest
      (notedStatement first.value.above line) :=
  state starts honest =>
    let core :=
      Parse.runsFromBindAt state
        (() => statementLine fuel self (InStatement column first.offset) state.at first.value.kind)
        (line1 => notedStatement first.value.above line1)
        [first, ..others]
        []
        [first, ..others]
        rest
        line
        (notedStatement first.value.above line)
        (Eq.sym (List.appendNil [first, ..others]))
        (runsLine state)
        (middle atRest honest1 offset => Parse.runsPure _ rest middle)
    match core starts honest with
      | Witness m (Both ran after) => Witness m (Both (rewrite starts, atColumn in ran) after)

--| Whether a statement of the block at `column` comes next: a token that
--| starts a line there.
def lineAhead (column: Nat) (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => token.value.startsLine && token.value.column == column
  | [] => False

theorem statementStops ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat)
    (state: Parse.State (Parse.Located Token))
    (none: lineAhead column state.at.rest = False):
    Parse.runFrom state (() => (Parse.optional (() => statement fuel self column), Parse.mark()))
      = Ok (None, state.at) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite none in rfl

--| A block ends at a token that doesn't start a line at its column, or at
--| the end: `statement` declines there.
theorem statementDeclines ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat)
    (input: List (Parse.Located Token))
    (none: lineAhead column input = False):
    Parse.Declines (() => statement fuel self column) input :=
  state starts honest => statementStops fuel self column state (rewrite starts in none)

--| A block: its statements one after another, up to where none starts.
--| The lines are each statement's notes and line, the first without a
--| blank line above it.
theorem runsBlock ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat)
    (firstRead: List (Parse.Located Token)) (first: List (Spaced Statement))
    (steps: List (List (Parse.Located Token), List (Spaced Statement))) (rest: List (Parse.Located Token))
    (runsFirst: Parse.Runs (() => statement fuel self column) firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => statement fuel self column) steps rest):
    Parse.Runs
      (() => block fuel self column)
      (firstRead ++ Parse.joinReads steps)
      rest
      { statements = withoutFirstBlank ([first, ..Parse.stepValues steps].concat) } :=
  Parse.runsMap
    (() => Parse.many1 (() => statement fuel self column))
    (lines => { statements = lines.toList.concat |> withoutFirstBlank })
    (firstRead ++ Parse.joinReads steps)
    rest
    (NonEmptyList.cons first (Parse.stepValues steps))
    (Parse.runsMany1 (() => statement fuel self column) firstRead first steps rest runsFirst manyRuns)

-- Declarations and the file.

--| A `let` declaration: a name, `=` and a body.
theorem runsDeclarationValue ∀ (layout: Layout)
    (first named equals: Parse.Located Token) (bodyTokens rest: List (Parse.Located Token))
    (declared: Text) (found: Body)
    (isLet: first.value.kind = Reserved LetKeyword)
    (isName: named.value.kind = Name declared)
    (nameAllowed: layout.allows named = True)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: layout.allows equals = True)
    (runsBody: Parse.Runs (() => body expression layout) bodyTokens rest found):
    Parse.Runs
      (() => declarationLine layout first.value.kind)
      [first, named, equals, ..bodyTokens]
      rest
      (Value declared found) :=
  rewrite isLet in
    Parse.runsBind
      (() => skip())
      (skipped =>
        let declared1 := name layout
        sign layout "'='" Defines
        Value declared1 (body expression layout))
      [first]
      [named, equals, ..bodyTokens]
      [first, named, equals, ..bodyTokens]
      rest
      ()
      (Value declared found)
      rfl
      (runsSkip first ([named, equals, ..bodyTokens] ++ rest))
      (Parse.runsBind
        (() => name layout)
        (declared1 =>
          sign layout "'='" Defines
          Value declared1 (body expression layout))
        [named]
        [equals, ..bodyTokens]
        [named, equals, ..bodyTokens]
        rest
        declared
        (Value declared found)
        rfl
        (runsName layout named declared ([equals, ..bodyTokens] ++ rest) isName nameAllowed)
        (Parse.runsBind
          (() => sign layout "'='" Defines)
          (signed => Value declared (body expression layout))
          [equals]
          bodyTokens
          [equals, ..bodyTokens]
          rest
          ()
          (Value declared found)
          rfl
          (runsSign layout "'='" Defines equals (bodyTokens ++ rest) isEquals equalsAllowed)
          (Parse.runsMap
            (() => body expression layout)
            (inner => Value declared inner)
            bodyTokens
            rest
            found
            runsBody)))

--| A `fn` declaration: a name, the parameters in brackets, `=` and a body.
theorem runsDeclarationFunction ∀ (layout: Layout)
    (first named open close equals: Parse.Located Token)
    (parameterTokens bodyTokens rest: List (Parse.Located Token))
    (declared: Text) (parameters: List Text) (found: Body)
    (isFn: first.value.kind = Reserved FnKeyword)
    (isName: named.value.kind = Name declared)
    (nameAllowed: layout.allows named = True)
    (opens: open.value.kind = Sign OpenParen)
    (openAllowed: layout.allows open = True)
    (closes: close.value.kind = Sign CloseParen)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: layout.allows equals = True)
    (runsParameters: Parse.Runs
      (() => Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma))
      parameterTokens
      ([close, equals, ..bodyTokens] ++ rest)
      parameters)
    (runsBody: Parse.Runs (() => body expression layout) bodyTokens rest found):
    Parse.Runs
      (() => declarationLine layout first.value.kind)
      [first, named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
      rest
      (Function declared parameters found) :=
  rewrite isFn in
    Parse.runsBind
      (() => skip())
      (skipped =>
        let declared1 := name layout
        sign layout "'('" OpenParen
        let parameters1 := Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma)
        sign InBrackets "')'" CloseParen
        sign layout "'='" Defines
        Function declared1 parameters1 (body expression layout))
      [first]
      [named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
      [first, named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
      rest
      ()
      (Function declared parameters found)
      rfl
      (runsSkip first ([named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]] ++ rest))
      (Parse.runsBind
        (() => name layout)
        (declared1 =>
          sign layout "'('" OpenParen
          let parameters1 := Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma)
          sign InBrackets "')'" CloseParen
          sign layout "'='" Defines
          Function declared1 parameters1 (body expression layout))
        [named]
        [open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
        [named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
        rest
        declared
        (Function declared parameters found)
        rfl
        (runsName layout named declared
          ([open, ..parameterTokens ++ [close, equals, ..bodyTokens]] ++ rest)
          isName
          nameAllowed)
        (Parse.runsBind
          (() => sign layout "'('" OpenParen)
          (signed =>
            let parameters1 := Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma)
            sign InBrackets "')'" CloseParen
            sign layout "'='" Defines
            Function declared parameters1 (body expression layout))
          [open]
          (parameterTokens ++ [close, equals, ..bodyTokens])
          [open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
          rest
          ()
          (Function declared parameters found)
          rfl
          (runsSign layout "'('" OpenParen open
            ((parameterTokens ++ [close, equals, ..bodyTokens]) ++ rest)
            opens
            openAllowed)
          (Parse.runsBind
            (() => Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma))
            (parameters1 =>
              sign InBrackets "')'" CloseParen
              sign layout "'='" Defines
              Function declared parameters1 (body expression layout))
            parameterTokens
            [close, equals, ..bodyTokens]
            (parameterTokens ++ [close, equals, ..bodyTokens])
            rest
            parameters
            (Function declared parameters found)
            rfl
            runsParameters
            (Parse.runsBind
              (() => sign InBrackets "')'" CloseParen)
              (signed =>
                sign layout "'='" Defines
                Function declared parameters (body expression layout))
              [close]
              [equals, ..bodyTokens]
              [close, equals, ..bodyTokens]
              rest
              ()
              (Function declared parameters found)
              rfl
              (runsSign InBrackets "')'" CloseParen close ([equals, ..bodyTokens] ++ rest) closes rfl)
              (Parse.runsBind
                (() => sign layout "'='" Defines)
                (signed => Function declared parameters (body expression layout))
                [equals]
                bodyTokens
                [equals, ..bodyTokens]
                rest
                ()
                (Function declared parameters found)
                rfl
                (runsSign layout "'='" Defines equals (bodyTokens ++ rest) isEquals equalsAllowed)
                (Parse.runsMap
                  (() => body expression layout)
                  (inner => Function declared parameters inner)
                  bodyTokens
                  rest
                  found
                  runsBody))))))

--| A declaration: on tokens whose first starts a line at column 0, the
--| own-line comments above that token, then the declaration read from
--| them (or its tokens as written, `notedDeclaration`).
theorem runsDeclaration ∀ (source: Text)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token)) (parsed: Declaration)
    (atMargin: (first.value.startsLine && first.value.column == 0) = True)
    (runsLine: Parse.Runs
      (() => declarationLine (InStatement 0 first.offset) first.value.kind)
      [first, ..others]
      rest
      parsed):
    Parse.Runs
      (() => declaration source)
      [first, ..others]
      rest
      (notedDeclaration source first.value.above [first, ..others] parsed) :=
  state starts honest =>
    let core :=
      Parse.runsFromBind state
        (() => declarationLine (InStatement 0 first.offset) first.value.kind)
        (parsed1 =>
          let finish := Parse.mark()
          notedDeclaration source first.value.above (state.at.rest.take (finish.offset - state.at.offset)) parsed1)
        [first, ..others]
        []
        [first, ..others]
        rest
        parsed
        (notedDeclaration source first.value.above [first, ..others] parsed)
        (Eq.sym (List.appendNil [first, ..others]))
        runsLine
        (middle atRest honest1 offset =>
          let count: middle.at.offset - state.at.offset = [first, ..others].length := omega [offset]
          let taken: state.at.rest.take (middle.at.offset - state.at.offset) = [first, ..others] :=
            rewrite count, starts in List.takeAppend [first, ..others] rest
          Parse.runsFromMark middle
            (finish =>
              notedDeclaration source first.value.above (state.at.rest.take (finish.offset - state.at.offset)) parsed)
            []
            rest
            (notedDeclaration source first.value.above [first, ..others] parsed)
            (rewrite taken in Parse.runsPure _ rest middle))
    match core starts honest with
      | Witness m (Both ran after) => Witness m (Both (rewrite starts, atMargin in ran) after)

--| Whether a declaration comes next: a token that starts a line at
--| column 0.
def marginAhead (input: List (Parse.Located Token)): Bool := lineAhead 0 input

theorem declarationStops ∀ (source: Text) (state: Parse.State (Parse.Located Token))
    (none: marginAhead state.at.rest = False):
    Parse.runFrom state (() => (Parse.optional (() => declaration source), Parse.mark())) = Ok (None, state.at) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite none in rfl

--| The declarations end at a token that doesn't start a line at column 0,
--| or at the end of the file.
theorem declarationDeclines ∀ (source: Text) (input: List (Parse.Located Token))
    (none: marginAhead input = False):
    Parse.Declines (() => declaration source) input :=
  state starts honest => declarationStops source state (rewrite starts in none)

--| The file: its declarations one after another to the end of the tokens,
--| then the comments after the last.
theorem runsSourceFile ∀ (source: Text) (endTrivia: List Trivia)
    (steps: List (List (Parse.Located Token), List (Spaced Declaration)))
    (manyRuns: Parse.ManyRuns (() => declaration source) steps []):
    Parse.Runs
      (() => sourceFile source endTrivia)
      (Parse.joinReads steps)
      []
      (fileOf (Parse.stepValues steps).concat endTrivia) :=
  Parse.runsBind
    (() => Parse.many (() => declaration source))
    (found => fileEnd found.concat endTrivia)
    (Parse.joinReads steps)
    []
    (Parse.joinReads steps)
    []
    (Parse.stepValues steps)
    (fileOf (Parse.stepValues steps).concat endTrivia)
    (Eq.sym (List.appendNil (Parse.joinReads steps)))
    (Parse.runsMany (() => declaration source) steps [] manyRuns)
    (state starts honest =>
      Witness state.at (Both (rewrite starts in rfl) (Both starts (Both (rewrite starts at honest in honest) rfl))))

--| `parse` on a source that lexes, whose tokens `sourceFile` reads to the
--| end as `file`, gives `file`.
theorem parseReads ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (runs: Parse.Runs (() => sourceFile source lexed.endTrivia) lexed.tokens [] file):
    parse source = Ok file :=
  let whole := Parse.runsWhole lexed.tokens (() => sourceFile source lexed.endTrivia) file runs
  rewrite lexes, whole in rfl

-- An `if` whose branches are each one expression, from its spelling.

theorem operatorOfReserved ∀ (layout: Layout) (level: Nat) (token: Parse.Located Token) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    operatorOf layout level token = None :=
  rewrite reserved in rfl

--| A keyword ends an expression: it is no call, field or operator.
theorem endsAtReserved ∀ (layout: Layout) (token: Parse.Located Token) (keyword: Keyword)
    (rest: List (Parse.Located Token))
    (reserved: token.value.kind = Reserved keyword):
    EndsExpression layout [token, ..rest] :=
  Both
    (match allowed: layout.allows token with
      | True => rewrite reserved in rfl
      | False => rfl)
    (rewrite operatorOfReserved layout 1 token keyword reserved,
        operatorOfReserved layout 2 token keyword reserved,
        operatorOfReserved layout 3 token keyword reserved,
        operatorOfReserved layout 4 token keyword reserved,
        operatorOfReserved layout 5 token keyword reserved,
        operatorOfReserved layout 6 token keyword reserved in
      rfl)

--| `body` reads back a body that is one expression, given that `self`
--| reads the expression.
theorem runsInlineSpelled ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (found: Body) (tokens rest: List (Parse.Located Token))
    (shaped: ShapedInline found)
    (spelled: SpelledInline layout found tokens)
    (ends: EndsExpression layout rest)
    (small: tokens.length < bound):
    Parse.Runs (() => body self layout) tokens rest found :=
  match found, shaped, spelled with
    | { statements = [{ blankBefore, line = Bare value trailing }] }, shaped, Both noBlank (Both trails (Both inline valueSpelled)) =>
      match spelledStart layout value tokens shaped valueSpelled with
        | Witness first (Witness others (Both split startKind)) =>
          let runsValue := nested layout value tokens rest shaped valueSpelled ends small
          let inline2 := rewrite split at inline in inline
          let runsValue2 := rewrite split at runsValue in runsValue
          rewrite noBlank, trails, split in runsBodyInline self layout value first others rest inline2 runsValue2

--| `expressionRule` reads back an `if` whose branches are each one
--| expression, given that `self` reads the expressions nested in it.
theorem runsIfSpelled ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (condition: Expr) (whenTrue whenFalse: Body) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped (If condition whenTrue whenFalse))
    (spelled: Spelled layout (If condition whenTrue whenFalse) tokens)
    (ends: EndsExpression layout rest)
    (small: tokens.length <= bound):
    Parse.Runs (() => expressionRule self layout) tokens rest (If condition whenTrue whenFalse) :=
  match shaped, spelled with
    | Both conditionShaped (Both trueShaped falseShaped), Witness ifToken (Witness conditionTokens (Witness thenToken (Witness trueTokens (Witness elseToken (Witness falseTokens (Both split (Both isIfToken (Both ifAllowed (Both isThen (Both thenAllowed (Both isElse (Both elseAllowed (Both conditionSpelled (Both trueSpelled falseSpelled)))))))))))))) =>
      let inner := List.lengthAppend trueTokens [elseToken, ..falseTokens]
      let outer := List.lengthAppend conditionTokens [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
      let size: tokens.length = Succ (conditionTokens.length + Succ (trueTokens.length + Succ falseTokens.length)) :=
        rewrite split, outer, inner in rfl
      rewrite split in
        runsIf self layout ifToken thenToken elseToken conditionTokens trueTokens falseTokens rest condition whenTrue
          whenFalse
          isIfToken
          ifAllowed
          isThen
          thenAllowed
          isElse
          elseAllowed
          (nested layout condition conditionTokens
            ([thenToken, ..trueTokens ++ [elseToken, ..falseTokens]] ++ rest)
            conditionShaped
            conditionSpelled
            (endsAtReserved layout thenToken ThenKeyword ((trueTokens ++ [elseToken, ..falseTokens]) ++ rest) isThen)
            (omega [size, small]))
          (runsInlineSpelled self layout bound nested whenTrue trueTokens
            ([elseToken, ..falseTokens] ++ rest)
            trueShaped
            trueSpelled
            (endsAtReserved layout elseToken ElseKeyword (falseTokens ++ rest) isElse)
            (omega [size, small]))
          (runsInlineSpelled self layout bound nested whenFalse falseTokens rest falseShaped falseSpelled ends
            (omega [size, small]))

-- A function's parameters.

theorem noneOfNotSome ∀ (found: Option ()) (none: found.isSome = False): found = None := match found, none with
  | None, none => rfl

theorem commaDeclines ∀ (input: List (Parse.Located Token))
    (absent: signAhead Comma input = False):
    Parse.Declines (() => sign InBrackets "','" Comma) input :=
  match input, absent with
    | [], absent => Parse.declinesOneEnd "','" (selectAllowed InBrackets (signIs Comma))
    | [token, ..later], absent =>
      Parse.declinesOne "','"
        (selectAllowed InBrackets (signIs Comma))
        token
        later
        (noneOfNotSome (signIs Comma token.value.kind) absent)

--| The rounds of a parameter list after its first name: each a comma and
--| a name, giving the name.
def ParameterSteps: (steps: List (List (Parse.Located Token), Text)) → Prop
  | [] => True
  | [(read, parameter), ..more] =>
    (∃ (comma: Parse.Located Token) => ∃ (named: Parse.Located Token) => read = [comma, named]
      ∧ comma.value.kind = Sign Comma
      ∧ named.value.kind = Name parameter)
      ∧ ParameterSteps more

theorem parameterRounds ∀ (steps: List (List (Parse.Located Token), Text)) (rest: List (Parse.Located Token))
    (spelled: ParameterSteps steps)
    (ends: signAhead Comma rest = False):
    Parse.ManyRuns (() => Parse.sepStep (() => name InBrackets) (() => sign InBrackets "','" Comma)) steps rest :=
  match steps, spelled with
    | [], spelled =>
      Parse.declinesSepStep
        (() => name InBrackets)
        (() => sign InBrackets "','" Comma)
        rest
        (commaDeclines rest ends)
    | [(read, parameter), ..more], Both (Witness comma (Witness named (Both split (Both isComma isName)))) later =>
      Both
        (rewrite split in (same => cases))
        (Both
          (rewrite split in
            Parse.runsSepStep
              (() => name InBrackets)
              (() => sign InBrackets "','" Comma)
              [comma]
              [named]
              (Parse.joinReads more ++ rest)
              parameter
              (runsSign InBrackets "','" Comma comma ([named] ++ (Parse.joinReads more ++ rest)) isComma rfl)
              (runsName InBrackets named parameter (Parse.joinReads more ++ rest) isName rfl))
          (parameterRounds more rest later ends))

--| A function's parameters: a name, then a comma and a name any number
--| of times, up to a token that is no comma.
theorem runsParameters ∀ (first: Parse.Located Token) (parameter: Text)
    (steps: List (List (Parse.Located Token), Text)) (rest: List (Parse.Located Token))
    (isName: first.value.kind = Name parameter)
    (spelled: ParameterSteps steps)
    (ends: signAhead Comma rest = False):
    Parse.Runs
      (() => Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma))
      ([first] ++ Parse.joinReads steps)
      rest
      [parameter, ..Parse.stepValues steps] :=
  Parse.runsSepBy
    (() => name InBrackets)
    (() => sign InBrackets "','" Comma)
    [first]
    parameter
    steps
    rest
    (runsName InBrackets first parameter (Parse.joinReads steps ++ rest) isName rfl)
    (parameterRounds steps rest spelled ends)

--| No parameters: the next token is not a name.
theorem runsNoParameters ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (notName: nameOf token.value.kind = None):
    Parse.Runs (() => Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma)) [] [token, ..rest] [] :=
  Parse.runsSepByNone
    (() => name InBrackets)
    (() => sign InBrackets "','" Comma)
    [token, ..rest]
    (Parse.declinesOne "a name" (selectAllowed InBrackets nameOf) token rest (rewrite notName in rfl))
