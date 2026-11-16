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
    Parse.Runs (() => keyword layout wanted) [token] rest (layout.comments token) :=
  Parse.runsOne _
    (selectComments layout (keywordIs wanted))
    token
    (layout.comments token)
    rest
    (rewrite allowed, reserved then
      match wanted with
        | FnKeyword => byComputing
        | LetKeyword => byComputing
        | IfKeyword => byComputing
        | ThenKeyword => byComputing
        | ElseKeyword => byComputing)

--| `else` is read where it may stand: on the line, deeper, or starting a
--| line at the statement's own column.
theorem runsElse ∀ (layout: Layout) (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (isElse: token.value.kind = Reserved ElseKeyword)
    (allowed: layout.allowsElse token = True):
    Parse.Runs (() => elseKeyword layout) [token] rest (layout.comments token) :=
  state starts honest =>
    let core := Parse.runsMap (() => skip()) (skipped => layout.comments token) [token] rest () (runsSkip token rest)
    match core state starts honest with | (m, ran, after) => (m, (rewrite starts, isElse, allowed then ran), after)

--| `expressionRule` on an `if`: the keyword, the condition, `then`, a
--| body, `else`, a body, each keyword's comments in the tree.
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
      (If
        (layout.comments ifToken)
        condition
        (layout.comments thenToken)
        whenTrue
        (layout.comments elseToken)
        whenFalse) :=
  state starts honest =>
    let ifComments := layout.comments ifToken
    let thenComments := layout.comments thenToken
    let elseComments := layout.comments elseToken
    let read := If ifComments condition thenComments whenTrue elseComments whenFalse
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let condition1 := self layout
          let thenComments1 := keyword layout ThenKeyword
          let whenTrue1 := body self layout
          let elseComments1 := elseKeyword layout
          let whenFalse1 := body self layout
          If ifComments condition1 thenComments1 whenTrue1 elseComments1 whenFalse1)
        [ifToken]
        (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
        [ifToken, ..conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]]
        rest
        ()
        read
        byComputing
        (runsSkip ifToken ((conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]) ++ rest))
        (Parse.runsBind
          (() => self layout)
          (condition1 =>
            let thenComments1 := keyword layout ThenKeyword
            let whenTrue1 := body self layout
            let elseComments1 := elseKeyword layout
            let whenFalse1 := body self layout
            If ifComments condition1 thenComments1 whenTrue1 elseComments1 whenFalse1)
          conditionTokens
          [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
          (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
          rest
          condition
          read
          byComputing
          runsCondition
          (Parse.runsBind
            (() => keyword layout ThenKeyword)
            (thenComments1 =>
              let whenTrue1 := body self layout
              let elseComments1 := elseKeyword layout
              let whenFalse1 := body self layout
              If ifComments condition thenComments1 whenTrue1 elseComments1 whenFalse1)
            [thenToken]
            (trueTokens ++ [elseToken, ..falseTokens])
            [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
            rest
            thenComments
            read
            byComputing
            (runsKeyword layout ThenKeyword thenToken
              ((trueTokens ++ [elseToken, ..falseTokens]) ++ rest)
              isThen
              thenAllowed)
            (Parse.runsBind
              (() => body self layout)
              (whenTrue1 =>
                let elseComments1 := elseKeyword layout
                let whenFalse1 := body self layout
                If ifComments condition thenComments whenTrue1 elseComments1 whenFalse1)
              trueTokens
              [elseToken, ..falseTokens]
              (trueTokens ++ [elseToken, ..falseTokens])
              rest
              whenTrue
              read
              byComputing
              runsTrue
              (Parse.runsBind
                (() => elseKeyword layout)
                (elseComments1 =>
                  let whenFalse1 := body self layout
                  If ifComments condition thenComments whenTrue elseComments1 whenFalse1)
                [elseToken]
                falseTokens
                [elseToken, ..falseTokens]
                rest
                elseComments
                read
                byComputing
                (runsElse layout elseToken (falseTokens ++ rest) isElse elseAllowed)
                (Parse.runsMap
                  (() => body self layout)
                  (whenFalse1 => If ifComments condition thenComments whenTrue elseComments whenFalse1)
                  falseTokens
                  rest
                  whenFalse
                  runsFalse)))))
    match core state starts honest with
      | (m, ran, others) => (m, (rewrite starts, ifAllowed, isIfToken then ran), others)

--| An expression as a statement.
theorem runsBareStatement ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (value: Expr) (tokens rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self layout) tokens rest value)
    (headed: layout.headed value = value):
    Parse.Runs (() => bareStatement self layout) tokens rest (Bare value) :=
  rewrite <- headed then
    Parse.runsMap (() => self layout) (value1 => Bare (layout.headed value1)) tokens rest value runsValue

--| The body that is one expression, as `inlineBody` reads it.
def bodyOf (value: Expr): Body := { statements = [{ blankBefore = False, line = Bare value }] }

theorem runsInlineBody ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (value: Expr) (tokens rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self layout) tokens rest value)
    (headed: layout.headed value = value):
    Parse.Runs (() => inlineBody self layout) tokens rest (bodyOf value) :=
  Parse.runsMap
    (() => bareStatement self layout)
    (line => { statements = [{ blankBefore = False, line }] })
    tokens
    rest
    (Bare value)
    (runsBareStatement self layout value tokens rest runsValue headed)

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
        | { at = { rest = [], offset, left }, furthest, expected, messages } => byComputing
        | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => byComputing
    | InStatement column from =>
      match state with
        | { at = { rest = [], offset, left }, furthest, expected, messages } => byComputing
        | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } =>
          rewrite inline then byComputing

--| The column of the first of the tokens: a block's, when it starts one.
def firstColumn (input: List (Parse.Located Token)): Nat := match input with
  | [token, .._] => token.value.column
  | [] => 0

theorem blockBodyRun ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (column from: Nat) (state: Parse.State (Parse.Located Token))
    (ahead: blockAhead (InStatement column from) state.at.rest = True):
    Parse.runFrom state (() => (bodyFuel (Succ more) self (InStatement column from), Parse.mark()))
      = Parse.runFrom state (() => (block more self (firstColumn state.at.rest), Parse.mark())) :=
  match state with
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite ahead then byComputing

--| A statement's line that starts with `let`: a name, `=` and a body.
theorem runsLineLet ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (first named equals: Parse.Located Token) (bodyTokens rest: List (Parse.Located Token)) (bound: Text) (found: Body)
    (isLet: first.value.kind = Reserved LetKeyword)
    (isName: named.value.kind = Name bound)
    (nameAllowed: layout.allows named = True)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: layout.allows equals = True)
    (runsBody: Parse.Runs (() => bodyFuel fuel self layout) bodyTokens rest found):
    Parse.Runs
      (() => statementLine fuel self layout first first.value.kind)
      [first, named, equals, ..bodyTokens]
      rest
      (Let (layout.comments first) bound (layout.comments named) (layout.comments equals) found) :=
  let letComments := layout.comments first
  let nameComments := layout.comments named
  let equalsComments := layout.comments equals
  let read := Let letComments bound nameComments equalsComments found
  rewrite isLet then
    Parse.runsBind
      (() => skip())
      (skipped =>
        let (bound1, nameComments1) := name layout
        let equals1 := sign layout "'='" Defines
        Let letComments bound1 nameComments1 equals1 (bodyFuel fuel self layout))
      [first]
      [named, equals, ..bodyTokens]
      [first, named, equals, ..bodyTokens]
      rest
      ()
      read
      byComputing
      (runsSkip first ([named, equals, ..bodyTokens] ++ rest))
      (Parse.runsBind
        (() => name layout)
        (named1 =>
          let (bound1, nameComments1) := named1
          let equals1 := sign layout "'='" Defines
          Let letComments bound1 nameComments1 equals1 (bodyFuel fuel self layout))
        [named]
        [equals, ..bodyTokens]
        [named, equals, ..bodyTokens]
        rest
        (bound, nameComments)
        read
        byComputing
        (runsName layout named bound ([equals, ..bodyTokens] ++ rest) isName nameAllowed)
        (Parse.runsBind
          (() => sign layout "'='" Defines)
          (equals1 => Let letComments bound nameComments equals1 (bodyFuel fuel self layout))
          [equals]
          bodyTokens
          [equals, ..bodyTokens]
          rest
          equalsComments
          read
          byComputing
          (runsSign layout "'='" Defines equals (bodyTokens ++ rest) isEquals equalsAllowed)
          (Parse.runsMap
            (() => bodyFuel fuel self layout)
            (inner => Let letComments bound nameComments equalsComments inner)
            bodyTokens
            rest
            found
            runsBody)))

--| A statement's line that doesn't start with `let` is an expression.
theorem runsLineOther ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (first: Parse.Located Token) (kind: Kind) (read rest: List (Parse.Located Token)) (line: Statement)
    (notLet: kind ≠ Reserved LetKeyword)
    (runs: Parse.Runs (() => bareStatement self layout) read rest line):
    Parse.Runs (() => statementLine fuel self layout first kind) read rest line :=
  match kind, notLet with
    | Name text, notLet => runs
    | Number digits, notLet => runs
    | Str written, notLet => runs
    | Sign punctuation, notLet => runs
    | Op operator, notLet => runs
    | Stray text, notLet => runs
    | Reserved keyword, notLet =>
      match keyword, notLet with
        | LetKeyword, notLet => (notLet byComputing).impossible
        | FnKeyword, notLet => runs
        | IfKeyword, notLet => runs
        | ThenKeyword, notLet => runs
        | ElseKeyword, notLet => runs

theorem runsLineBare ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (value: Expr)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (notLet: first.value.kind ≠ Reserved LetKeyword)
    (runsValue: Parse.Runs (() => self layout) [first, ..others] rest value)
    (headed: layout.headed value = value):
    Parse.Runs (() => statementLine fuel self layout first first.value.kind) [first, ..others] rest (Bare value) :=
  runsLineOther fuel self layout first first.value.kind
    [first, ..others]
    rest
    (Bare value)
    notLet
    (runsBareStatement self layout value [first, ..others] rest runsValue headed)

--| A statement: on tokens whose first starts a line at the block's column,
--| the own-line comments above that token, then the line read from them
--| at the statement's layout.
theorem runsStatement ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token)) (line: Statement)
    (atColumn: (first.value.startsLine && first.value.column == column) = True)
    (runsLine: Parse.Runs
      (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
      [first, ..others]
      rest
      line):
    Parse.Runs (() => statement fuel self column) [first, ..others] rest (notedStatement first.value.above line) :=
  state starts honest =>
    let core :=
      Parse.runsFromBindAt state
        (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
        (line1 => notedStatement first.value.above line1)
        [first, ..others]
        []
        [first, ..others]
        rest
        line
        (notedStatement first.value.above line)
        (Eq.flipped (List.appendNil [first, ..others]))
        (runsLine state)
        (middle atRest honest1 offset => Parse.runsPure _ rest middle)
    match core starts honest with | (m, ran, after) => (m, (rewrite starts, atColumn then ran), after)

--| Whether a statement of the block at `column` comes next: a token that
--| starts a line there.
def lineAhead (column: Nat) (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => token.value.startsLine && token.value.column == column
  | [] => False

theorem statementStops ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (column: Nat) (state: Parse.State (Parse.Located Token))
    (none: lineAhead column state.at.rest = False):
    Parse.runFrom state (() => (Parse.optional (() => statement fuel self column), Parse.mark()))
      = Ok (None, state.at) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => byComputing
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite none then byComputing

--| A block ends at a token that doesn't start a line at its column, or at
--| the end: `statement` declines there.
theorem statementDeclines ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (column: Nat) (input: List (Parse.Located Token))
    (none: lineAhead column input = False):
    Parse.Declines (() => statement fuel self column) input :=
  state starts honest => statementStops fuel self column state (rewrite starts then none)

--| A keyword that follows a body inside an `if`: `then` after a
--| condition that ends in a block, `else` after a block branch.
def closesBlock: Kind → Bool
  | Reserved ThenKeyword => True
  | Reserved ElseKeyword => True
  | _ => False

--| Whether `then` or `else` comes next. Either may start a line at the
--| column of the block before it, and ends that block there.
def closerAhead (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => closesBlock token.value.kind
  | [] => False

theorem bareDeclines ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (input: List (Parse.Located Token))
    (declines: Parse.Declines (() => self layout) input):
    Parse.Declines (() => bareStatement self layout) input :=
  Parse.declinesBind (() => self layout) (value => Bare (layout.headed value)) input declines

--| A line that starts with `then` or `else` is no statement: it is
--| neither a `let` nor the start of an expression.
theorem closerLineDeclines ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (first: Parse.Located Token) (later: List (Parse.Located Token))
    (declines: DeclinesNested self) (kind: Kind)
    (isKind: first.value.kind = kind)
    (closes: closesBlock kind = True):
    Parse.Declines (() => statementLine fuel self layout first kind) [first, ..later] :=
  match kind, isKind, closes with
    | Reserved ThenKeyword, isKind, closes =>
      bareDeclines self layout [first, ..later] (declines layout first later ThenKeyword isKind (same => cases))
    | Reserved ElseKeyword, isKind, closes =>
      bareDeclines self layout [first, ..later] (declines layout first later ElseKeyword isKind (same => cases))

--| `statement` declines where its line does, on a token that starts a
--| line at the block's column.
theorem statementLineDeclines ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat)
    (first: Parse.Located Token) (later: List (Parse.Located Token))
    (atColumn: (first.value.startsLine && first.value.column == column) = True)
    (declinesLine: Parse.Declines
      (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
      [first, ..later]):
    Parse.Declines (() => statement fuel self column) [first, ..later] :=
  state starts honest =>
    let step: Parse.runFrom state (() => (Parse.optional (() => statement fuel self column), Parse.mark()))
      = Parse.runFrom state (() =>
        (
          Parse.optional (() =>
            notedStatement first.value.above
              (statementLine fuel self (InStatement column first.offset) first first.value.kind)),
          Parse.mark()
        )) :=
      rewrite starts, atColumn then byComputing
    Eq.trans step
      (Parse.declinesBind
        (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
        (line => notedStatement first.value.above line)
        [first, ..later]
        declinesLine
        state
        starts
        honest)

--| A block ends at `then` or `else`, wherever the keyword stands: even
--| starting a line at the block's own column, where a statement would,
--| `statement` declines, given that the expression parser does there.
theorem statementDeclinesCloser ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (column: Nat) (input: List (Parse.Located Token))
    (declines: DeclinesNested self)
    (closer: closerAhead input = True):
    Parse.Declines (() => statement fuel self column) input :=
  match ahead: lineAhead column input with
    | False => statementDeclines fuel self column input ahead
    | True =>
      match input, closer, ahead with
        | [first, ..later], closer, ahead =>
          statementLineDeclines fuel self column first later ahead
            (closerLineDeclines fuel self
              (InStatement column first.offset)
              first
              later
              declines
              first.value.kind
              byComputing
              closer)

--| Where a block at `column` ends: no token starts a line there, or the
--| token that does is `then` or `else`.
def BlockEnds (column: Nat) (rest: List (Parse.Located Token)): Prop :=
  lineAhead column rest = False ∨ closerAhead rest = True

theorem statementDeclinesEnd ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (column: Nat) (input: List (Parse.Located Token))
    (declines: DeclinesNested self)
    (ends: BlockEnds column input):
    Parse.Declines (() => statement fuel self column) input :=
  match ends with
    | Inl none => statementDeclines fuel self column input none
    | Inr closer => statementDeclinesCloser fuel self column input declines closer

--| A block: its statements one after another, up to where none starts.
--| The lines are each statement's notes and line, the first without a
--| blank line above it.
theorem runsBlock ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat)
    (firstRead: List (Parse.Located Token)) (first: List (Spaced Statement))
    (steps: List (List (Parse.Located Token), List (Spaced Statement))) (rest: List (Parse.Located Token))
    (runsFirst: Parse.Runs (() => statement fuel self column) firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => statement fuel self column) steps rest):
    Parse.Runs (() => block fuel self column) (firstRead ++ Parse.joinReads steps) rest {
      statements = withoutFirstBlank ([first, ..Parse.stepValues steps].concat)
    } :=
  Parse.runsMap
    (() => Parse.many1 (() => statement fuel self column))
    (lines => { statements = lines.toList.concat |> withoutFirstBlank })
    (firstRead ++ Parse.joinReads steps)
    rest
    (NonEmptyList.cons first (Parse.stepValues steps))
    (Parse.runsMany1 (() => statement fuel self column) firstRead first steps rest runsFirst manyRuns)

-- Declarations and the file.

--| A `let` declaration: a name, `=` and a body.
theorem runsDeclarationValue ∀ (layout: Layout) (first named equals: Parse.Located Token)
    (bodyTokens rest: List (Parse.Located Token)) (declared: Text) (found: Body)
    (isLet: first.value.kind = Reserved LetKeyword)
    (isName: named.value.kind = Name declared)
    (nameAllowed: layout.allows named = True)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: layout.allows equals = True)
    (runsBody: Parse.Runs (() => body expression layout) bodyTokens rest found):
    Parse.Runs
      (() => declarationLine layout first)
      [first, named, equals, ..bodyTokens]
      rest
      (Value (layout.comments first) declared (layout.comments named) (layout.comments equals) found) :=
  let letComments := layout.comments first
  let nameComments := layout.comments named
  let equalsComments := layout.comments equals
  let read := Value letComments declared nameComments equalsComments found
  rewrite isLet then
    Parse.runsBind
      (() => skip())
      (skipped =>
        let (declared1, nameComments1) := name layout
        let equals1 := sign layout "'='" Defines
        Value letComments declared1 nameComments1 equals1 (body expression layout))
      [first]
      [named, equals, ..bodyTokens]
      [first, named, equals, ..bodyTokens]
      rest
      ()
      read
      byComputing
      (runsSkip first ([named, equals, ..bodyTokens] ++ rest))
      (Parse.runsBind
        (() => name layout)
        (named1 =>
          let (declared1, nameComments1) := named1
          let equals1 := sign layout "'='" Defines
          Value letComments declared1 nameComments1 equals1 (body expression layout))
        [named]
        [equals, ..bodyTokens]
        [named, equals, ..bodyTokens]
        rest
        (declared, nameComments)
        read
        byComputing
        (runsName layout named declared ([equals, ..bodyTokens] ++ rest) isName nameAllowed)
        (Parse.runsBind
          (() => sign layout "'='" Defines)
          (equals1 => Value letComments declared nameComments equals1 (body expression layout))
          [equals]
          bodyTokens
          [equals, ..bodyTokens]
          rest
          equalsComments
          read
          byComputing
          (runsSign layout "'='" Defines equals (bodyTokens ++ rest) isEquals equalsAllowed)
          (Parse.runsMap
            (() => body expression layout)
            (inner => Value letComments declared nameComments equalsComments inner)
            bodyTokens
            rest
            found
            runsBody)))

--| A `fn` declaration: a name, the parameters in brackets, `=` and a body.
theorem runsDeclarationFunction ∀ (layout: Layout) (first named open close equals: Parse.Located Token)
    (parameterTokens bodyTokens rest: List (Parse.Located Token)) (declared: Text)
    (listed: Option ((Text, Comments), List (Comments, (Text, Comments)))) (found: Body)
    (isFn: first.value.kind = Reserved FnKeyword)
    (isName: named.value.kind = Name declared)
    (nameAllowed: layout.allows named = True)
    (opens: open.value.kind = Sign OpenParen)
    (openAllowed: layout.allows open = True)
    (closes: close.value.kind = Sign CloseParen)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: layout.allows equals = True)
    (runsParameters: Parse.Runs
      (() => Parse.optional parameterList)
      parameterTokens
      ([close, equals, ..bodyTokens] ++ rest)
      listed)
    (runsBody: Parse.Runs (() => body expression layout) bodyTokens rest found):
    Parse.Runs
      (() => declarationLine layout first)
      [first, named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
      rest
      (Function
        (layout.comments first)
        declared
        (layout.comments named)
        (layout.comments open)
        (parametersOf listed)
        (Layout.comments InBrackets close)
        (layout.comments equals)
        found) :=
  let fnComments := layout.comments first
  let nameComments := layout.comments named
  let opened := layout.comments open
  let closed := Layout.comments InBrackets close
  let equalsComments := layout.comments equals
  let read := Function fnComments declared nameComments opened (parametersOf listed) closed equalsComments found
  rewrite isFn then
    Parse.runsBind
      (() => skip())
      (skipped =>
        let (declared1, nameComments1) := name layout
        let open1 := sign layout "'('" OpenParen
        let parameters1 := parametersOf (Parse.optional parameterList)
        let close1 := sign InBrackets "')'" CloseParen
        let equals1 := sign layout "'='" Defines
        Function fnComments declared1 nameComments1 open1 parameters1 close1 equals1 (body expression layout))
      [first]
      [named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
      [first, named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
      rest
      ()
      read
      byComputing
      (runsSkip first ([named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]] ++ rest))
      (Parse.runsBind
        (() => name layout)
        (named1 =>
          let (declared1, nameComments1) := named1
          let open1 := sign layout "'('" OpenParen
          let parameters1 := parametersOf (Parse.optional parameterList)
          let close1 := sign InBrackets "')'" CloseParen
          let equals1 := sign layout "'='" Defines
          Function fnComments declared1 nameComments1 open1 parameters1 close1 equals1 (body expression layout))
        [named]
        [open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
        [named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
        rest
        (declared, nameComments)
        read
        byComputing
        (runsName layout named declared
          ([open, ..parameterTokens ++ [close, equals, ..bodyTokens]] ++ rest)
          isName
          nameAllowed)
        (Parse.runsBind
          (() => sign layout "'('" OpenParen)
          (open1 =>
            let parameters1 := parametersOf (Parse.optional parameterList)
            let close1 := sign InBrackets "')'" CloseParen
            let equals1 := sign layout "'='" Defines
            Function fnComments declared nameComments open1 parameters1 close1 equals1 (body expression layout))
          [open]
          (parameterTokens ++ [close, equals, ..bodyTokens])
          [open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
          rest
          opened
          read
          byComputing
          (runsSign layout "'('" OpenParen open
            ((parameterTokens ++ [close, equals, ..bodyTokens]) ++ rest)
            opens
            openAllowed)
          (Parse.runsBind
            (() => parametersOf (Parse.optional parameterList))
            (parameters1 =>
              let close1 := sign InBrackets "')'" CloseParen
              let equals1 := sign layout "'='" Defines
              Function fnComments declared nameComments opened parameters1 close1 equals1 (body expression layout))
            parameterTokens
            [close, equals, ..bodyTokens]
            (parameterTokens ++ [close, equals, ..bodyTokens])
            rest
            (parametersOf listed)
            read
            byComputing
            (Parse.runsMap
              (() => Parse.optional parameterList)
              parametersOf
              parameterTokens
              ([close, equals, ..bodyTokens] ++ rest)
              listed
              runsParameters)
            (Parse.runsBind
              (() => sign InBrackets "')'" CloseParen)
              (close1 =>
                let equals1 := sign layout "'='" Defines
                Function fnComments declared nameComments opened
                  (parametersOf listed)
                  close1
                  equals1
                  (body expression layout))
              [close]
              [equals, ..bodyTokens]
              [close, equals, ..bodyTokens]
              rest
              closed
              read
              byComputing
              (runsSign InBrackets "')'" CloseParen close ([equals, ..bodyTokens] ++ rest) closes byComputing)
              (Parse.runsBind
                (() => sign layout "'='" Defines)
                (equals1 =>
                  Function fnComments declared nameComments opened
                    (parametersOf listed)
                    closed
                    equals1
                    (body expression layout))
                [equals]
                bodyTokens
                [equals, ..bodyTokens]
                rest
                equalsComments
                read
                byComputing
                (runsSign layout "'='" Defines equals (bodyTokens ++ rest) isEquals equalsAllowed)
                (Parse.runsMap
                  (() => body expression layout)
                  (inner =>
                    Function fnComments declared nameComments opened (parametersOf listed) closed equalsComments inner)
                  bodyTokens
                  rest
                  found
                  runsBody))))))

--| A declaration: on tokens whose first starts a line at column 0, the
--| own-line comments above that token, then the declaration read from
--| them.
theorem runsDeclaration ∀ (first: Parse.Located Token) (others rest: List (Parse.Located Token)) (parsed: Declaration)
    (atMargin: (first.value.startsLine && first.value.column == 0) = True)
    (runsLine: Parse.Runs (() => declarationLine (InStatement 0 first.offset) first) [first, ..others] rest parsed):
    Parse.Runs (() => declaration()) [first, ..others] rest (notedDeclaration first.value.above parsed) :=
  state starts honest =>
    let core :=
      Parse.runsFromBindAt state
        (() => declarationLine (InStatement 0 first.offset) first)
        (parsed1 => notedDeclaration first.value.above parsed1)
        [first, ..others]
        []
        [first, ..others]
        rest
        parsed
        (notedDeclaration first.value.above parsed)
        (Eq.flipped (List.appendNil [first, ..others]))
        (runsLine state)
        (middle atRest honest1 offset => Parse.runsPure _ rest middle)
    match core starts honest with | (m, ran, after) => (m, (rewrite starts, atMargin then ran), after)

--| Whether a declaration comes next: a token that starts a line at
--| column 0.
def marginAhead (input: List (Parse.Located Token)): Bool := lineAhead 0 input

theorem declarationStops ∀ (state: Parse.State (Parse.Located Token))
    (none: marginAhead state.at.rest = False):
    Parse.runFrom state (() => (Parse.optional declaration, Parse.mark())) = Ok (None, state.at) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => byComputing
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite none then byComputing

--| The declarations end at a token that doesn't start a line at column 0,
--| or at the end of the file.
theorem declarationDeclines ∀ (input: List (Parse.Located Token))
    (none: marginAhead input = False):
    Parse.Declines declaration input :=
  state starts honest => declarationStops state (rewrite starts then none)

--| The file: its declarations one after another to the end of the tokens,
--| then the comments after the last.
theorem runsSourceFile ∀ (endTrivia: List Trivia) (steps: List (List (Parse.Located Token), List (Spaced Declaration)))
    (manyRuns: Parse.ManyRuns declaration steps []):
    Parse.Runs
      (() => sourceFile endTrivia)
      (Parse.joinReads steps)
      []
      (fileOf (Parse.stepValues steps).concat endTrivia) :=
  Parse.runsBind
    (() => Parse.many declaration)
    (found => fileEnd found.concat endTrivia)
    (Parse.joinReads steps)
    []
    (Parse.joinReads steps)
    []
    (Parse.stepValues steps)
    (fileOf (Parse.stepValues steps).concat endTrivia)
    (Eq.flipped (List.appendNil (Parse.joinReads steps)))
    (Parse.runsMany declaration steps [] manyRuns)
    (state starts honest =>
      (state.at, (rewrite starts then byComputing), starts, (rewrite starts at honest then honest), byComputing))

--| `parse` on a source that lexes, whose tokens `sourceFile` reads to the
--| end as `file`, gives `file`.
theorem parseReads ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (runs: Parse.Runs (() => sourceFile lexed.endTrivia) lexed.tokens [] file):
    parse source = Ok file :=
  let whole := Parse.runsWhole lexed.tokens (() => sourceFile lexed.endTrivia) file runs
  rewrite lexes, whole then byComputing

-- An `if` whose branches are each one expression, from its spelling.

theorem operatorOfReserved ∀ (layout: Layout) (level: Nat) (token: Parse.Located Token) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    operatorOf layout level token = None :=
  rewrite reserved then byComputing

--| A keyword ends an expression: it is no call, field or operator.
theorem endsAtReserved ∀ (layout: Layout) (token: Parse.Located Token)
    (keyword: Keyword) (rest: List (Parse.Located Token))
    (reserved: token.value.kind = Reserved keyword):
    EndsExpression layout [token, ..rest] :=
  (
    (match allowed: layout.allows token with
      | True => rewrite reserved then byComputing
      | False => byComputing),
    (rewrite operatorOfReserved layout 1 token keyword reserved,
        operatorOfReserved layout 2 token keyword reserved,
        operatorOfReserved layout 3 token keyword reserved,
        operatorOfReserved layout 4 token keyword reserved,
        operatorOfReserved layout 5 token keyword reserved,
        operatorOfReserved layout 6 token keyword reserved then
      byComputing)
  )

--| A keyword that may follow a body follows anything.
theorem afterCloser ∀ (layout: Layout) (tokens: List (Parse.Located Token)) (token: Parse.Located Token)
    (rest: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword)
    (closes: closesBlock (Reserved keyword) = True):
    After layout tokens [token, ..rest] :=
  (
    (endsAtReserved layout token keyword rest reserved),
    (match layout with
      | InBrackets => byComputing
      | InStatement column from => Inl (rewrite reserved then closes))
  )

theorem closerReserved ∀ (kind: Kind)
    (closes: closesBlock kind = True):
    ∃ (keyword: Keyword) => kind = Reserved keyword :=
  match kind, closes with
    | Reserved ThenKeyword, closes => (ThenKeyword, byComputing)
    | Reserved ElseKeyword, closes => (ElseKeyword, byComputing)

theorem operatorOfUnallowed ∀ (layout: Layout) (level: Nat) (token: Parse.Located Token)
    (unallowed: layout.allows token = False):
    operatorOf layout level token = None :=
  match kind: token.value.kind with
    | Op operator =>
      match same: operator.level == level with
        | True => rewrite unallowed then byComputing
        | False => byComputing
    | Name text => byComputing
    | Number digits => byComputing
    | Str written => byComputing
    | Reserved keyword => byComputing
    | Sign punctuation => byComputing
    | Stray text => byComputing

--| A token the layout turns away ends an expression.
theorem endsUnallowed ∀ (layout: Layout) (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (unallowed: layout.allows token = False):
    EndsExpression layout [token, ..rest] :=
  (
    (rewrite unallowed then byComputing),
    (rewrite operatorOfUnallowed layout 1 token unallowed,
        operatorOfUnallowed layout 2 token unallowed,
        operatorOfUnallowed layout 3 token unallowed,
        operatorOfUnallowed layout 4 token unallowed,
        operatorOfUnallowed layout 5 token unallowed,
        operatorOfUnallowed layout 6 token unallowed then
      byComputing)
  )

--| A line start no deeper than `column`, seen from a statement at a
--| `deeper` column that it isn't the first token of (`same`): not allowed
--| there, no deeper, and not at that column.
theorem lowLine ∀ (startsLine: Bool) (indent column deeper: Nat) (same: Bool)
    (low: (startsLine && indent <= column) = True)
    (below: column < deeper)
    (apart: same = False):
    (not startsLine || indent > deeper || same) = False
      ∧ (startsLine && indent <= deeper) = True
      ∧ (startsLine && indent == deeper) = False :=
  match startsLine, low with
    | True, low =>
      let shallow: (indent > deeper) = False := arithmetic [low, below]
      ((rewrite shallow, apart then byComputing), (arithmetic [low, below]), (arithmetic [low, below]))

--| What may follow a statement may follow the last line of a block
--| inside it, and ends the block: the tokens `[first, ..others]` of a line
--| at a `deeper` column, the last of the statement's.
theorem afterDeeper ∀ (column from deeper: Nat) (front: List (Parse.Located Token))
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (below: column < deeper)
    (settled: Settled (InStatement column from) (front ++ [first, ..others]) rest):
    After (InStatement deeper first.offset) [first, ..others] rest ∧ BlockEnds deeper rest :=
  match rest, settled with
    | [], settled => (((((byComputing, byComputing)), byComputing)), (Inl byComputing))
    | [next, ..more], Inl closes =>
      match closerReserved next.value.kind closes with
        | Witness keyword reserved => (
          (((endsAtReserved (InStatement deeper first.offset) next keyword more reserved), (Inl closes))),
          (Inr closes)
        )
    | [next, ..more], Inr (Both low clear) =>
      match notAtBack next.offset front [first, ..others] clear with
        | Both apart othersClear =>
          match lowLine next.value.startsLine next.value.column column deeper
            (next.offset == first.offset)
            low
            below
            apart with
            | Both unallowed (Both lower elsewhere) => (
              ((
                (endsUnallowed (InStatement deeper first.offset) next more unallowed),
                (Inr ((lower, apart, othersClear)))
              )),
              (Inl elsewhere)
            )

--| A body that is one expression, spelled as such, is spelled as a body
--| before whatever may follow its expression.
theorem inlineSpelledBody ∀ (layout: Layout) (found: Body) (tokens rest: List (Parse.Located Token))
    (shaped: ShapedBody found)
    (spelled: SpelledInline layout found tokens)
    (after: After layout tokens rest):
    SpelledBody layout found tokens rest :=
  match found, shaped, spelled with
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both valueShaped none) closed, Both noBlank
        (Both inline (Both valueSpelled headed)) =>
      match spelledStart layout value tokens valueShaped valueSpelled with
        | Witness first (Witness others (Both split startKind)) =>
          Inl
            ((
              noBlank,
              first,
              others,
              split,
              (rewrite <- split then inline),
              valueShaped,
              (rewrite <- split then valueSpelled),
              (rewrite <- split then after),
              headed
            ))

--| `expressionRule` reads back an `if`, its branches bodies of either
--| kind, given that `self` reads the expressions nested in it.
theorem runsIfSpelled ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (declines: DeclinesNested self)
    (ifComments: Comments) (condition: Expr) (thenComments: Comments) (whenTrue: Body) (elseComments: Comments)
    (whenFalse: Body) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped (If ifComments condition thenComments whenTrue elseComments whenFalse))
    (spelled: Spelled layout (If ifComments condition thenComments whenTrue elseComments whenFalse) tokens)
    (after: After layout tokens rest)
    (small: tokens.length <= bound):
    Parse.Runs
      (() => expressionRule self layout)
      tokens
      rest
      (If ifComments condition thenComments whenTrue elseComments whenFalse) :=
  match shaped, spelled with
    | (conditionShaped, trueShaped, falseShaped), (ifToken, conditionTokens, thenToken, trueTokens, elseToken,
        falseTokens, split, isIfToken, ifAllowed, isThen, thenAllowed, isElse, elseAllowed, conditionSpelled,
        trueSpelled, falseSpelled, ifCommented, thenCommented, elseCommented) =>
      let inner := List.lengthAppend trueTokens [elseToken, ..falseTokens]
      let outer := List.lengthAppend conditionTokens [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
      let size: tokens.length = Succ (conditionTokens.length + Succ (trueTokens.length + Succ falseTokens.length)) :=
        rewrite split, outer, inner then byComputing
      let settled: Settled layout
        [ifToken, ..conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]]
        rest :=
        rewrite <- split then after.right
      let settledFalse: Settled layout falseTokens rest :=
        settledBack layout
          [elseToken]
          falseTokens
          rest
          (settledBack layout trueTokens
            [elseToken, ..falseTokens]
            rest
            (settledBack layout
              [thenToken]
              (trueTokens ++ [elseToken, ..falseTokens])
              rest
              (settledBack layout conditionTokens
                [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
                rest
                (settledBack layout
                  [ifToken]
                  (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
                  rest
                  settled))))
      rewrite split, ifCommented, thenCommented, elseCommented then
        runsIf self layout ifToken thenToken elseToken conditionTokens trueTokens falseTokens rest condition whenTrue
            whenFalse isIfToken ifAllowed isThen thenAllowed isElse elseAllowed
            (nested layout condition conditionTokens
              ([thenToken, ..trueTokens ++ [elseToken, ..falseTokens]] ++ rest)
              conditionShaped
              conditionSpelled
              (afterCloser layout conditionTokens thenToken
                ((trueTokens ++ [elseToken, ..falseTokens]) ++ rest)
                ThenKeyword
                isThen
                byComputing)
              (arithmetic [size, small]))
            (runsBodyNested self layout bound nested declines whenTrue trueTokens
              ([elseToken, ..falseTokens] ++ rest)
              trueShaped
              (trueSpelled
                ([elseToken, ..falseTokens] ++ rest)
                (afterCloser layout trueTokens elseToken (falseTokens ++ rest) ElseKeyword isElse byComputing))
              (arithmetic [size, small]))
            (runsBodyNested self layout bound nested declines whenFalse falseTokens rest falseShaped
              (falseSpelled rest ((after.left, settledFalse)))
              (arithmetic [size, small]))

-- A function's parameters.

theorem noneOfNotSome ∀ (found: Option ()) (none: found.isSome = False): found = None := match found, none with
  | None, none => byComputing

theorem commaDeclines ∀ (input: List (Parse.Located Token))
    (absent: signAhead Comma input = False):
    Parse.Declines (() => sign InBrackets "','" Comma) input :=
  match input, absent with
    | [], absent => Parse.declinesOneEnd "','" (selectComments InBrackets (signIs Comma))
    | [token, ..later], absent =>
      Parse.declinesOne "','"
        (selectComments InBrackets (signIs Comma))
        token
        later
        (rewrite noneOfNotSome (signIs Comma token.value.kind) absent then byComputing)

--| The rounds of a parameter list after its first name: each a comma and
--| a name, giving the comma's comments and the name with its own.
def ParameterSteps: (steps: List (List (Parse.Located Token), (Comments, (Text, Comments)))) → Prop
  | [] => True
  | [(read, found), ..more] =>
    (∃ (comma: Parse.Located Token) => ∃ (named: Parse.Located Token) => ∃ (parameter: Text) => read = [comma, named]
      ∧ comma.value.kind = Sign Comma
      ∧ named.value.kind = Name parameter
      ∧ found = (Layout.comments InBrackets comma, (parameter, Layout.comments InBrackets named)))
      ∧ ParameterSteps more

theorem parameterRounds ∀
    (steps: List (List (Parse.Located Token), (Comments, (Text, Comments)))) (rest: List (Parse.Located Token))
    (spelled: ParameterSteps steps)
    (ends: signAhead Comma rest = False):
    Parse.ManyRuns parameterStep steps rest :=
  match steps, spelled with
    | [], spelled =>
      Parse.declinesBind
        (() => sign InBrackets "','" Comma)
        (comma =>
          let named := name InBrackets
          (comma, named))
        rest
        (commaDeclines rest ends)
    | [(read, found), ..more], Both
        (Witness comma (Witness named (Witness parameter (Both split (Both isComma (Both isName valued))))))
        later =>
      let commaComments := Layout.comments InBrackets comma
      (
        (rewrite split then (same => cases)),
        (rewrite split, valued then
          Parse.runsBind
            (() => sign InBrackets "','" Comma)
            (comma1 =>
              let named1 := name InBrackets
              (comma1, named1))
            [comma]
            [named]
            [comma, named]
            (Parse.joinReads more ++ rest)
            commaComments
            (commaComments, (parameter, Layout.comments InBrackets named))
            byComputing
            (runsSign InBrackets "','" Comma comma ([named] ++ (Parse.joinReads more ++ rest)) isComma byComputing)
            (Parse.runsMap
              (() => name InBrackets)
              (named1 => (commaComments, named1))
              [named]
              (Parse.joinReads more ++ rest)
              (parameter, Layout.comments InBrackets named)
              (runsName InBrackets named parameter (Parse.joinReads more ++ rest) isName byComputing))),
        (parameterRounds more rest later ends)
      )

--| A function's parameters: a name, then a comma and a name any number
--| of times, up to a token that is no comma.
theorem runsParameters ∀ (first: Parse.Located Token) (parameter: Text)
    (steps: List (List (Parse.Located Token), (Comments, (Text, Comments)))) (rest: List (Parse.Located Token))
    (isName: first.value.kind = Name parameter)
    (spelled: ParameterSteps steps)
    (ends: signAhead Comma rest = False):
    Parse.Runs
      (() => Parse.optional parameterList)
      ([first] ++ Parse.joinReads steps)
      rest
      (Some ((parameter, Layout.comments InBrackets first), Parse.stepValues steps)) :=
  let head := (parameter, Layout.comments InBrackets first)
  Parse.runsOptional parameterList
    ([first] ++ Parse.joinReads steps)
    rest
    (head, Parse.stepValues steps)
    (Parse.runsBind
      (() => name InBrackets)
      (first1 =>
        let others := Parse.many parameterStep
        (first1, others))
      [first]
      (Parse.joinReads steps)
      ([first] ++ Parse.joinReads steps)
      rest
      head
      (head, Parse.stepValues steps)
      byComputing
      (runsName InBrackets first parameter (Parse.joinReads steps ++ rest) isName byComputing)
      (Parse.runsMap
        (() => Parse.many parameterStep)
        (others => (head, others))
        (Parse.joinReads steps)
        rest
        (Parse.stepValues steps)
        (Parse.runsMany parameterStep steps rest (parameterRounds steps rest spelled ends))))

--| No parameters: the next token is not a name.
theorem runsNoParameters ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (notName: nameOf token.value.kind = None):
    Parse.Runs (() => Parse.optional parameterList) [] [token, ..rest] None :=
  Parse.declinesRuns parameterList
    [token, ..rest]
    (Parse.declinesBind
      (() => name InBrackets)
      (first =>
        let others := Parse.many parameterStep
        (first, others))
      [token, ..rest]
      (Parse.declinesOne "a name" (selectWithComments InBrackets nameOf) token rest (rewrite notName then byComputing)))

-- An instance of `runsExpression` with an `if`: the six tokens of
-- `if a then b else c`.

def exampleIf: Expr :=
  If Comments.none
    (Var "a" Comments.none)
    Comments.none
    { statements = [{ blankBefore = False, line = Bare (Var "b" Comments.none) }] }
    Comments.none
    { statements = [{ blankBefore = False, line = Bare (Var "c" Comments.none) }] }

theorem runsIfExample: Parse.run
      [
        exampleToken (Reserved IfKeyword) 0,
        exampleToken (Name "a") 3,
        exampleToken (Reserved ThenKeyword) 5,
        exampleToken (Name "b") 10,
        exampleToken (Reserved ElseKeyword) 12,
        exampleToken (Name "c") 17
      ]
      (() => expression InBrackets)
      = Ok exampleIf :=
  let a := exampleToken (Name "a") 3
  let b := exampleToken (Name "b") 10
  let c := exampleToken (Name "c") 17
  Parse.runsRun
    (() => expression InBrackets)
    [
      exampleToken (Reserved IfKeyword) 0,
      a,
      exampleToken (Reserved ThenKeyword) 5,
      b,
      exampleToken (Reserved ElseKeyword) 12,
      c
    ]
    exampleIf
    (runsExpression InBrackets exampleIf
      [
        exampleToken (Reserved IfKeyword) 0,
        a,
        exampleToken (Reserved ThenKeyword) 5,
        b,
        exampleToken (Reserved ElseKeyword) 12,
        c
      ]
      []
      (Both byComputing
        (Both (Both (Both byComputing byComputing) byComputing) (Both (Both byComputing byComputing) byComputing)))
      (Witness
        (exampleToken (Reserved IfKeyword) 0)
        (Witness
          [a]
          (Witness
            (exampleToken (Reserved ThenKeyword) 5)
            (Witness
              [b]
              (Witness
                (exampleToken (Reserved ElseKeyword) 12)
                (Witness
                  [c]
                  (Both byComputing
                    (Both byComputing
                      (Both byComputing
                        (Both byComputing
                          (Both byComputing
                            (Both byComputing
                              (Both byComputing
                                (Both
                                  (Witness a (Both byComputing (Both byComputing (Both byComputing byComputing))))
                                  (Both
                                    (rest after =>
                                      inlineSpelledBody InBrackets
                                        (bodyOf (Var "b" Comments.none))
                                        [b]
                                        rest
                                        (Both (Both byComputing byComputing) byComputing)
                                        (Both byComputing
                                          (Both byComputing
                                            (Both
                                              (Witness b
                                                (Both byComputing (Both byComputing (Both byComputing byComputing))))
                                              byComputing)))
                                        after)
                                    (Both
                                      (rest after =>
                                        inlineSpelledBody InBrackets
                                          (bodyOf (Var "c" Comments.none))
                                          [c]
                                          rest
                                          (Both (Both byComputing byComputing) byComputing)
                                          (Both byComputing
                                            (Both byComputing
                                              (Both
                                                (Witness c
                                                  (Both byComputing (Both byComputing (Both byComputing byComputing))))
                                                byComputing)))
                                          after)
                                      (Both byComputing (Both byComputing byComputing))))))))))))))))))
      (Both (Both byComputing byComputing) byComputing))

-- An instance with a block branch, as a statement at column 0:
--     if a then
--         b
--         else c
-- The `else` starts a line at its block's column and ends the block.

def exampleLineToken (kind: Kind) (column offset: Nat): Parse.Located Token :=
  { value = { kind, startsLine = True, column, above = [], trailing = None }, offset, length = 1 }

theorem runsIfBlockExample: Parse.run
      [
        exampleLineToken (Reserved IfKeyword) 0 0,
        exampleToken (Name "a") 3,
        exampleToken (Reserved ThenKeyword) 5,
        exampleLineToken (Name "b") 4 14,
        exampleLineToken (Reserved ElseKeyword) 4 20,
        exampleToken (Name "c") 25
      ]
      (() => expression (InStatement 0 0))
      = Ok exampleIf :=
  let a := exampleToken (Name "a") 3
  let b := exampleLineToken (Name "b") 4 14
  let c := exampleToken (Name "c") 25
  Parse.runsRun
    (() => expression (InStatement 0 0))
    [
      exampleLineToken (Reserved IfKeyword) 0 0,
      a,
      exampleToken (Reserved ThenKeyword) 5,
      b,
      exampleLineToken (Reserved ElseKeyword) 4 20,
      c
    ]
    exampleIf
    (runsExpression
      (InStatement 0 0)
      exampleIf
      [
        exampleLineToken (Reserved IfKeyword) 0 0,
        a,
        exampleToken (Reserved ThenKeyword) 5,
        b,
        exampleLineToken (Reserved ElseKeyword) 4 20,
        c
      ]
      []
      (Both byComputing
        (Both (Both (Both byComputing byComputing) byComputing) (Both (Both byComputing byComputing) byComputing)))
      (Witness
        (exampleLineToken (Reserved IfKeyword) 0 0)
        (Witness
          [a]
          (Witness
            (exampleToken (Reserved ThenKeyword) 5)
            (Witness
              [b]
              (Witness
                (exampleLineToken (Reserved ElseKeyword) 4 20)
                (Witness
                  [c]
                  (Both byComputing
                    (Both byComputing
                      (Both byComputing
                        (Both byComputing
                          (Both byComputing
                            (Both byComputing
                              (Both byComputing
                                (Both
                                  (Witness a (Both byComputing (Both byComputing (Both byComputing byComputing))))
                                  (Both
                                    (rest after =>
                                      match afterDeeper 0 0 4 [] b [] rest (arithmetic []) after.right with
                                        | Both afterLine blockEnds =>
                                          Inr
                                            (Both byComputing
                                              (Witness b
                                                (Witness []
                                                  (Witness []
                                                    (Both byComputing
                                                      (Both byComputing
                                                        (Both
                                                          (same => cases)
                                                          (Both byComputing
                                                            (Both
                                                              (Witness b
                                                                (Both byComputing
                                                                  (Both byComputing (Both byComputing byComputing))))
                                                              (Both afterLine
                                                                (Both byComputing
                                                                  (Both byComputing blockEnds)))))))))))))
                                    (Both
                                      (rest after =>
                                        inlineSpelledBody
                                          (InStatement 0 0)
                                          (bodyOf (Var "c" Comments.none))
                                          [c]
                                          rest
                                          (Both (Both byComputing byComputing) byComputing)
                                          (Both byComputing
                                            (Both byComputing
                                              (Both
                                                (Witness c
                                                  (Both byComputing (Both byComputing (Both byComputing byComputing))))
                                                byComputing)))
                                          after)
                                      (Both byComputing (Both byComputing byComputing))))))))))))))))))
      ((((byComputing, byComputing)), byComputing)))

-- Bodies and blocks from their spelling. The `if` inside an expression is
-- read back by `runsExpression` where its branches are each one
-- expression; a block is covered here as the body of a `let` or of a
-- declaration, to any depth.

--| The lines of a block's first statement lose the blank line above them.
def firstBlank (isFirst: Bool) (lines: List (Spaced Statement)): List (Spaced Statement) := match isFirst with
  | True => withoutFirstBlank lines
  | False => lines

--| `tokens`, followed by `rest`, spell the body `found` after `=` at
--| `layout`: one expression that doesn't start a line deeper than the
--| statement, before what may follow it (`After`); or a block, whose
--| first token starts a line deeper, of statements at that token's column.
def SpelledBody (layout: Layout) (found: Body) (tokens rest: List (Parse.Located Token)): Prop := match found with
  | { statements } =>
    SpelledOne layout statements tokens rest
      ∨ (blockAhead layout tokens = True ∧ SpelledLines (firstColumn tokens) True [] statements tokens rest)

--| `tokens`, followed by `rest`, spell the one line of a body that is an
--| expression on its keyword's line (`bodyOf`), which holds no comments
--| above its first token outside brackets (`Layout.headed` changes
--| nothing: the parser clears them there).
-- By the lines' own shape, not as "some `bodyOf value`": `Spelled` asks
-- this of an `if`'s branches, so the value has to be a part of them.
def SpelledOne (layout: Layout) (lines: List (Spaced Statement)) (tokens rest: List (Parse.Located Token)): Prop :=
  match lines with
    | [{ blankBefore, line = Bare value }] =>
      blankBefore = False
        ∧ (∃ (first: Parse.Located Token) => ∃ (others: List (Parse.Located Token)) => tokens = [first, ..others]
          ∧ blockAhead layout [first, ..others] = False
          ∧ Shaped value
          ∧ Spelled layout value [first, ..others]
          ∧ After layout [first, ..others] rest
          ∧ layout.headed value = value)
    | _ => False

--| `tokens`, followed by `rest`, spell the lines of a block at `column`
--| that come after the notes in `pending` (the block's first lines if
--| `isFirst`): each statement's first token starts a line at the column
--| and carries the notes above the statement and its blank line; a `let`
--| is its keyword, a name, `=` and a body; any other statement is an
--| expression, before what may follow it (`After`); and after the last
--| the block ends (`BlockEnds`).
def SpelledLines (column: Nat) (isFirst: Bool)
    (pending lines: List (Spaced Statement)) (tokens rest: List (Parse.Located Token)):
    Prop :=
  match lines with
    | [] => tokens = [] ∧ pending = [] ∧ BlockEnds column rest
    | [{ blankBefore, line = StatementNote comment }, ..more] =>
      SpelledLines column isFirst (pending ++ [{ blankBefore, line = StatementNote comment }]) more tokens rest
    | [{ blankBefore, line = Let letComments name nameComments equalsComments inner }, ..more] =>
      ∃ (first: Parse.Located Token) => ∃ (named: Parse.Located Token) => ∃ (equals: Parse.Located Token) =>
        ∃ (bodyTokens: List (Parse.Located Token)) => ∃ (later: List (Parse.Located Token)) => tokens
          = [first, named, equals, ..bodyTokens ++ later]
          ∧ (first.value.startsLine && first.value.column == column) = True
          ∧ first.value.kind = Reserved LetKeyword
          ∧ named.value.kind = Name name
          ∧ (InStatement column first.offset).allows named = True
          ∧ equals.value.kind = Sign Defines
          ∧ (InStatement column first.offset).allows equals = True
          ∧ letComments = (InStatement column first.offset).comments first
          ∧ nameComments = (InStatement column first.offset).comments named
          ∧ equalsComments = (InStatement column first.offset).comments equals
          ∧ firstBlank isFirst
            (notedStatement first.value.above (Let letComments name nameComments equalsComments inner))
            = pending ++ [{ blankBefore, line = Let letComments name nameComments equalsComments inner }]
          ∧ SpelledBody (InStatement column first.offset) inner bodyTokens (later ++ rest)
          ∧ SpelledLines column False [] more later rest
    | [{ blankBefore, line = Bare value }, ..more] =>
      ∃ (first: Parse.Located Token) => ∃ (others: List (Parse.Located Token)) =>
        ∃ (later: List (Parse.Located Token)) => tokens = [first, ..others ++ later]
          ∧ (first.value.startsLine && first.value.column == column) = True
          ∧ first.value.kind ≠ Reserved LetKeyword
          ∧ firstBlank isFirst (notedStatement first.value.above (Bare value))
            = pending ++ [{ blankBefore, line = Bare value }]
          ∧ Spelled (InStatement column first.offset) value [first, ..others]
          ∧ After (InStatement column first.offset) [first, ..others] (later ++ rest)
          ∧ SpelledLines column False [] more later rest

theorem firstBlankAppend ∀ (isFirst: Bool) (group later: List (Spaced Statement))
    (some: group ≠ []):
    firstBlank isFirst (group ++ later) = firstBlank isFirst group ++ later :=
  match isFirst with
    | False => byComputing
    | True =>
      match group, some with
        | [], some => (some byComputing).impossible
        | [head, ..tail], some => byComputing

--| A statement's lines are never none: they end with the statement.
theorem groupSome ∀ (isFirst: Bool) (group pending: List (Spaced Statement)) (last: Spaced Statement)
    (noted: firstBlank isFirst group = pending ++ [last]):
    group ≠ [] :=
  same =>
    let empty := rewrite same at noted then noted
    match isFirst, pending, empty with
      | True, [], empty => cases
      | False, [head, ..tail], empty => cases

theorem runsBodyFuelInline ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (value: Expr) (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (inline: blockAhead layout [first, ..others] = False)
    (runsValue: Parse.Runs (() => self layout) [first, ..others] rest value)
    (headed: layout.headed value = value):
    Parse.Runs (() => bodyFuel (Succ more) self layout) [first, ..others] rest (bodyOf value) :=
  state starts honest =>
    let ahead: blockAhead layout state.at.rest = False :=
      rewrite starts then
        match layout with
          | InBrackets => byComputing
          | InStatement column from => inline
    match runsInlineBody self layout value [first, ..others] rest runsValue headed state starts honest with
      | Witness m (Both ran after) => (m, (Eq.trans (inlineBodyRun more self layout state ahead) ran), after)

theorem runsBodyFuelBlock ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column from: Nat)
    (found: Body) (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (deeper: (first.value.startsLine && first.value.column > column) = True)
    (runsBlock: Parse.Runs (() => block more self first.value.column) [first, ..others] rest found):
    Parse.Runs (() => bodyFuel (Succ more) self (InStatement column from)) [first, ..others] rest found :=
  state starts honest =>
    let same: firstColumn state.at.rest = first.value.column := rewrite starts then byComputing
    let step0 := blockBodyRun more self column from state (rewrite starts then deeper)
    let step := rewrite same at step0 then step0
    match runsBlock state starts honest with | Witness m (Both ran after) => (m, (Eq.trans step ran), after)

--| The statements of a block read back, as the rounds of the block's
--| repetition: each round reads a statement's tokens and gives its lines,
--| and the lines together are the block's.
theorem linesRun ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat)
    (nested: ReadsNested self bound)
    (declines: DeclinesNested self)
    (column: Nat) (isFirst: Bool) (pending lines: List (Spaced Statement))
    (tokens rest: List (Parse.Located Token)) (fuel: Nat)
    (shaped: ShapedLines lines)
    (spelled: SpelledLines column isFirst pending lines tokens rest)
    (enough: tokens.length <= fuel)
    (short: tokens.length < bound):
    ∃ (steps: List (List (Parse.Located Token), List (Spaced Statement))) => Parse.joinReads steps = tokens
      ∧ Parse.ManyRuns (() => statement fuel self column) steps rest
      ∧ firstBlank isFirst (Parse.stepValues steps).concat = pending ++ lines :=
  match lines, shaped, spelled with
    | [], shaped, Both noTokens (Both noPending ends) => (
      [],
      noTokens.flipped,
      (statementDeclinesEnd fuel self column rest declines ends),
      (rewrite noPending then
        match isFirst with
          | True => byComputing
          | False => byComputing)
    )
    | [{ blankBefore, line = StatementNote comment }, ..more], Both lineShaped moreShaped, spelled =>
      match linesRun self bound nested declines column isFirst
        (pending ++ [{ blankBefore, line = StatementNote comment }])
        more
        tokens
        rest
        fuel
        moreShaped
        spelled
        enough
        short with
        | Witness steps (Both joined (Both runs values)) => (
          steps,
          joined,
          runs,
          (Eq.trans values (List.appendAssoc pending [{ blankBefore, line = StatementNote comment }] more))
        )
    | [{ blankBefore, line = Bare value }, ..more], Both valueShaped moreShaped, Witness first
        (Witness others
          (Witness later
            (Both split (Both atColumn (Both notLet (Both noted (Both valueSpelled (Both ends laterSpelled)))))))) =>
      let sizes := List.lengthAppend others later
      let whole: tokens.length = Succ (others.length + later.length) := rewrite split, sizes then byComputing
      match linesRun self bound nested declines column False [] more later rest fuel moreShaped laterSpelled
        (arithmetic [whole, enough])
        (arithmetic [whole, short]) with
        | Witness steps (Both joined (Both runs values)) =>
          let values2: (Parse.stepValues steps).concat = more := values
          (
            [([first, ..others], notedStatement first.value.above (Bare value)), ..steps],
            (rewrite split, joined then byComputing),
            ((
              (same => cases),
              (rewrite joined then
                runsStatement fuel self column first others
                  (later ++ rest)
                  (Bare value)
                  atColumn
                  (runsLineBare fuel self
                    (InStatement column first.offset)
                    value
                    first
                    others
                    (later ++ rest)
                    notLet
                    (nested
                      (InStatement column first.offset)
                      value
                      [first, ..others]
                      (later ++ rest)
                      valueShaped
                      valueSpelled
                      ends
                      (arithmetic [whole, short]))
                    (spelledHeaded
                      (InStatement column first.offset)
                      value
                      [first, ..others]
                      valueShaped
                      valueSpelled
                      (startAbove column first)))),
              runs
            )),
            (Eq.trans
              (firstBlankAppend isFirst
                (notedStatement first.value.above (Bare value))
                (Parse.stepValues steps).concat
                (groupSome isFirst
                  (notedStatement first.value.above (Bare value))
                  pending
                  { blankBefore, line = Bare value }
                  noted))
              (rewrite noted, values2 then List.appendAssoc pending [{ blankBefore, line = Bare value }] more))
          )
    | [{ blankBefore, line = Let letComments name nameComments equalsComments inner }, ..more], Both innerShaped
          moreShaped, Witness first
        (Witness named
          (Witness equals
            (Witness bodyTokens
              (Witness later
                (Both split
                  (Both atColumn
                    (Both isLet
                      (Both isName
                        (Both nameAllowed
                          (Both isEquals
                            (Both equalsAllowed
                              (Both letCommented
                                (Both nameCommented
                                  (Both equalsCommented (Both noted (Both innerSpelled laterSpelled)))))))))))))))) =>
      let line := Let letComments name nameComments equalsComments inner
      let sizes := List.lengthAppend bodyTokens later
      let whole: tokens.length = Succ (Succ (Succ (bodyTokens.length + later.length))) :=
        rewrite split, sizes then byComputing
      match linesRun self bound nested declines column False [] more later rest fuel moreShaped laterSpelled
        (arithmetic [whole, enough])
        (arithmetic [whole, short]) with
        | Witness steps (Both joined (Both runs values)) =>
          let values2: (Parse.stepValues steps).concat = more := values
          (
            [([first, named, equals, ..bodyTokens], notedStatement first.value.above line), ..steps],
            (rewrite split, joined then byComputing),
            ((
              (same => cases),
              (rewrite joined, letCommented, nameCommented, equalsCommented then
                runsStatement fuel self column first
                  [named, equals, ..bodyTokens]
                  (later ++ rest)
                  (Let
                    ((InStatement column first.offset).comments first)
                    name
                    ((InStatement column first.offset).comments named)
                    ((InStatement column first.offset).comments equals)
                    inner)
                  atColumn
                  (runsLineLet fuel self
                    (InStatement column first.offset)
                    first
                    named
                    equals
                    bodyTokens
                    (later ++ rest)
                    name
                    inner
                    isLet
                    isName
                    nameAllowed
                    isEquals
                    equalsAllowed
                    (runsBodySpelled self bound nested declines
                      (InStatement column first.offset)
                      inner
                      bodyTokens
                      (later ++ rest)
                      fuel
                      innerShaped
                      innerSpelled
                      (arithmetic [whole, enough])
                      (arithmetic [whole, short])))),
              runs
            )),
            (Eq.trans
              (firstBlankAppend isFirst
                (notedStatement first.value.above line)
                (Parse.stepValues steps).concat
                (groupSome isFirst (notedStatement first.value.above line) pending { blankBefore, line } noted))
              (rewrite noted, values2 then List.appendAssoc pending [{ blankBefore, line }] more))
          )

--| What spells a body reads back: `bodyFuel`, with fuel above the body's
--| tokens, reads exactly them and gives the body, given that `self` reads
--| the expressions in it.
theorem runsBodySpelled ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat)
    (nested: ReadsNested self bound)
    (declines: DeclinesNested self)
    (layout: Layout) (found: Body) (tokens rest: List (Parse.Located Token)) (fuel: Nat)
    (shaped: ShapedBody found)
    (spelled: SpelledBody layout found tokens rest)
    (enough: tokens.length < fuel)
    (short: tokens.length < bound):
    Parse.Runs (() => bodyFuel fuel self layout) tokens rest found :=
  match fuel with
    | Succ more =>
      match found, shaped, spelled with
        | { statements }, shaped, Inl one =>
          match statements, one with
            | [{ blankBefore, line = Bare value }], Both noBlank
                (Witness first
                  (Witness others (Both split (Both inline (Both valueShaped (Both valueSpelled ends)))))) =>
              rewrite noBlank, split then
                runsBodyFuelInline more self layout value first others rest inline
                  (nested layout value
                    [first, ..others]
                    rest
                    valueShaped
                    valueSpelled
                    ends.left
                    (rewrite split at short then short))
                  ends.right
        | { statements }, Both shaped closed, Inr (Both ahead lines) =>
          match linesRun self bound nested declines
            (firstColumn tokens)
            True
            []
            statements
            tokens
            rest
            more
            shaped
            lines
            (arithmetic [enough])
            short with
            | Witness steps (Both joined (Both runs values)) =>
              match layout, tokens, steps, ahead, joined, runs, values with
                | InStatement column from, [first, ..others], [(read, group), ..later], ahead, joined, Both some
                    (Both runsFirst runsLater), values =>
                  let values2: withoutFirstBlank ([group, ..Parse.stepValues later].concat) = statements := values
                  rewrite <- values2 then
                    runsBodyFuelBlock more self column from
                      { statements = withoutFirstBlank ([group, ..Parse.stepValues later].concat) }
                      first
                      others
                      rest
                      ahead
                      (rewrite <- joined then
                        runsBlock more self first.value.column read group later rest runsFirst runsLater)

--| `body`, read with the expression parser of an induction (`self`),
--| reads back what spells a body, a block too: what an `if` whose branch
--| is a block needs.
theorem runsBodyNested ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (declines: DeclinesNested self)
    (found: Body) (tokens rest: List (Parse.Located Token))
    (shaped: ShapedBody found)
    (spelled: SpelledBody layout found tokens rest)
    (short: tokens.length < bound):
    Parse.Runs (() => body self layout) tokens rest found :=
  state starts honest =>
    let lengths: state.at.rest.length = tokens.length + rest.length := rewrite starts then List.lengthAppend tokens rest
    match runsBodySpelled self bound nested declines layout found tokens rest
      (state.at.left + 1)
      shaped
      spelled
      (arithmetic [honest, lengths])
      short
      state
      starts
      honest with
      | (m, ran, after) => (
        m,
        (Eq.trans (Parse.runFromMark state (before => (bodyFuel (before.left + 1) self layout, Parse.mark()))) ran),
        after
      )

--| `body` reads back what spells a body.
theorem runsBody ∀ (layout: Layout) (found: Body) (tokens rest: List (Parse.Located Token))
    (shaped: ShapedBody found)
    (spelled: SpelledBody layout found tokens rest):
    Parse.Runs (() => body expression layout) tokens rest found :=
  runsBodyNested expression layout
    (Succ tokens.length)
    (nestedLayout nestedExpr nestedTokens nestedRest nestedShaped nestedSpelled nestedAfter shorter =>
      runsExpression nestedLayout nestedExpr nestedTokens nestedRest nestedShaped nestedSpelled nestedAfter)
    expressionDeclines
    found
    tokens
    rest
    shaped
    spelled
    (arithmetic [])

-- Declarations from their spelling.

--| The parser reads back a `let` declaration: on its keyword starting a
--| line at column 0, a name, `=` and tokens that spell its body,
--| `declaration` gives it after the notes above it.
theorem runsValueSpelled ∀ (first named equals: Parse.Located Token) (bodyTokens rest: List (Parse.Located Token))
    (declared: Text) (found: Body)
    (atMargin: (first.value.startsLine && first.value.column == 0) = True)
    (isLet: first.value.kind = Reserved LetKeyword)
    (isName: named.value.kind = Name declared)
    (nameAllowed: (InStatement 0 first.offset).allows named = True)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: (InStatement 0 first.offset).allows equals = True)
    (shaped: ShapedBody found)
    (spelled: SpelledBody (InStatement 0 first.offset) found bodyTokens rest):
    Parse.Runs
      (() => declaration())
      [first, named, equals, ..bodyTokens]
      rest
      (notedDeclaration first.value.above
        (Value
          ((InStatement 0 first.offset).comments first)
          declared
          ((InStatement 0 first.offset).comments named)
          ((InStatement 0 first.offset).comments equals)
          found)) :=
  runsDeclaration first
    [named, equals, ..bodyTokens]
    rest
    (Value
      ((InStatement 0 first.offset).comments first)
      declared
      ((InStatement 0 first.offset).comments named)
      ((InStatement 0 first.offset).comments equals)
      found)
    atMargin
    (runsDeclarationValue
      (InStatement 0 first.offset)
      first
      named
      equals
      bodyTokens
      rest
      declared
      found
      isLet
      isName
      nameAllowed
      isEquals
      equalsAllowed
      (runsBody (InStatement 0 first.offset) found bodyTokens rest shaped spelled))

--| The parser reads back a `fn` declaration: its keyword starting a line
--| at column 0, a name, the parameters in brackets (as the parameter
--| parser reads them, `runsParameters`), `=` and tokens that spell its
--| body.
theorem runsFunctionSpelled ∀ (first named open close equals: Parse.Located Token)
    (parameterTokens bodyTokens rest: List (Parse.Located Token)) (declared: Text)
    (listed: Option ((Text, Comments), List (Comments, (Text, Comments)))) (found: Body)
    (atMargin: (first.value.startsLine && first.value.column == 0) = True)
    (isFn: first.value.kind = Reserved FnKeyword)
    (isName: named.value.kind = Name declared)
    (nameAllowed: (InStatement 0 first.offset).allows named = True)
    (opens: open.value.kind = Sign OpenParen)
    (openAllowed: (InStatement 0 first.offset).allows open = True)
    (closes: close.value.kind = Sign CloseParen)
    (isEquals: equals.value.kind = Sign Defines)
    (equalsAllowed: (InStatement 0 first.offset).allows equals = True)
    (runsNames: Parse.Runs
      (() => Parse.optional parameterList)
      parameterTokens
      ([close, equals, ..bodyTokens] ++ rest)
      listed)
    (shaped: ShapedBody found)
    (spelled: SpelledBody (InStatement 0 first.offset) found bodyTokens rest):
    Parse.Runs
      (() => declaration())
      [first, named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
      rest
      (notedDeclaration first.value.above
        (Function
          ((InStatement 0 first.offset).comments first)
          declared
          ((InStatement 0 first.offset).comments named)
          ((InStatement 0 first.offset).comments open)
          (parametersOf listed)
          (Layout.comments InBrackets close)
          ((InStatement 0 first.offset).comments equals)
          found)) :=
  runsDeclaration first
    [named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]]
    rest
    (Function
      ((InStatement 0 first.offset).comments first)
      declared
      ((InStatement 0 first.offset).comments named)
      ((InStatement 0 first.offset).comments open)
      (parametersOf listed)
      (Layout.comments InBrackets close)
      ((InStatement 0 first.offset).comments equals)
      found)
    atMargin
    (runsDeclarationFunction
      (InStatement 0 first.offset)
      first
      named
      open
      close
      equals
      parameterTokens
      bodyTokens
      rest
      declared
      listed
      found
      isFn
      isName
      nameAllowed
      opens
      openAllowed
      closes
      isEquals
      equalsAllowed
      runsNames
      (runsBody (InStatement 0 first.offset) found bodyTokens rest shaped spelled))
