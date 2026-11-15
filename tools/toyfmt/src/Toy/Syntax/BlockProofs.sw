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
