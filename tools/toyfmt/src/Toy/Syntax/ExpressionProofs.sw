--| The expression parser read backwards: on tokens that spell an
--| expression (`Spelled`) of the shape the parser gives (`Shaped`),
--| `expression` gives that expression back. Built from std's completeness
--| lemmas (`Parse.Runs`), `Parse.runsOperators` for the operator chains.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std.Parse.Associativity (LeftAssociative)
import Std.Parse.OperatorTree (Joined, Operand)
import Std (Bool, Eq, List, Option, Parse, Text, Void)

theorem runsSkip ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token)):
    Parse.Runs (() => skip()) [token] rest () :=
  Parse.runsMap
    (() => Parse.next (token => True))
    (skipped => ())
    [token]
    rest
    (Some token)
    (Parse.runsNext (token => True) token rest byComputing)

theorem runsSign ∀ (layout: Layout) (what: Text) (wanted: Punctuation)
    (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (signed: token.value.kind = Sign wanted)
    (allowed: layout.allows token = True):
    Parse.Runs (() => sign layout what wanted) [token] rest (layout.comments token) :=
  Parse.runsOne what
    (selectComments layout (signIs wanted))
    token
    (layout.comments token)
    rest
    (rewrite allowed, signed then
      match wanted with
        | OpenParen => byComputing
        | CloseParen => byComputing
        | OpenSquare => byComputing
        | CloseSquare => byComputing
        | Comma => byComputing
        | Dot => byComputing
        | Colon => byComputing
        | Defines => byComputing)

theorem runsName ∀ (layout: Layout) (token: Parse.Located Token) (text: Text) (rest: List (Parse.Located Token))
    (named: token.value.kind = Name text)
    (allowed: layout.allows token = True):
    Parse.Runs (() => name layout) [token] rest (text, layout.comments token) :=
  Parse.runsOne "a name"
    (selectWithComments layout nameOf)
    token
    (text, layout.comments token)
    rest
    (rewrite allowed, named)

theorem runsAtomNumber ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (digits: Text) (rest: List (Parse.Located Token))
    (numbered: token.value.kind = Number digits)
    (allowed: layout.allows token = True):
    Parse.Runs (() => atom self layout) [token] rest (NumberLiteral digits (layout.comments token)) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts
    (
      (state.advance rest 1).at,
      (rewrite starts, allowed, numbered, starts),
      byComputing,
      (arithmetic [honest, lengths]),
      byComputing
    )

theorem runsAtomString ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (written: Text) (rest: List (Parse.Located Token))
    (quoted: token.value.kind = Str written)
    (allowed: layout.allows token = True):
    Parse.Runs (() => atom self layout) [token] rest (StringLiteral written (layout.comments token)) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts
    (
      (state.advance rest 1).at,
      (rewrite starts, allowed, quoted, starts),
      byComputing,
      (arithmetic [honest, lengths]),
      byComputing
    )

theorem runsAtomBracketed ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (open close: Parse.Located Token) (innerTokens rest: List (Parse.Located Token)) (inner: Expr)
    (opens: open.value.kind = Sign OpenParen)
    (allowed: layout.allows open = True)
    (closes: close.value.kind = Sign CloseParen)
    (runsInner: Parse.Runs (() => self InBrackets) innerTokens [close, ..rest] inner):
    Parse.Runs
      (() => atom self layout)
      [open, ..innerTokens ++ [close]]
      rest
      (Bracketed (layout.comments open) inner ((Layout.comments InBrackets close).closing inner.endsWithComment)) :=
  state starts honest =>
    let opened := layout.comments open
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let inner := self InBrackets
          let close := sign InBrackets "')'" CloseParen
          Bracketed opened inner (close.closing inner.endsWithComment))
        [open]
        (innerTokens ++ [close])
        [open, ..innerTokens ++ [close]]
        rest
        ()
        (Bracketed opened inner ((Layout.comments InBrackets close).closing inner.endsWithComment))
        byComputing
        (runsSkip open ((innerTokens ++ [close]) ++ rest))
        (Parse.runsBind
          (() => self InBrackets)
          (inner =>
            let close := sign InBrackets "')'" CloseParen
            Bracketed opened inner (close.closing inner.endsWithComment))
          innerTokens
          [close]
          (innerTokens ++ [close])
          rest
          inner
          (Bracketed opened inner ((Layout.comments InBrackets close).closing inner.endsWithComment))
          byComputing
          runsInner
          (Parse.runsMap
            (() => sign InBrackets "')'" CloseParen)
            (closed => Bracketed opened inner (closed.closing inner.endsWithComment))
            [close]
            rest
            (Layout.comments InBrackets close)
            (runsSign InBrackets "')'" CloseParen close rest closes byComputing)))
    match core state starts honest with | (m, ran, others) => (m, (rewrite starts, allowed, opens then ran), others)

--| A round of `suffixesFrom` that reads a field: `.`, a name, and on from
--| the target with the field.
theorem runsSuffixesField ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (dot named: Parse.Located Token) (field: Text) (after rest: List (Parse.Located Token)) (value: Expr)
    (dotted: dot.value.kind = Sign Dot)
    (dotAllowed: layout.allows dot = True)
    (isName: named.value.kind = Name field)
    (nameAllowed: layout.allows named = True)
    (runsMore: Parse.Runs
      (() => suffixesFrom more self layout (Field target (layout.comments dot) field (layout.comments named)))
      after
      rest
      value):
    Parse.Runs (() => suffixesFrom (Succ more) self layout target) [dot, named, ..after] rest value :=
  state starts honest =>
    let dotted1 := layout.comments dot
    let read := Field target dotted1 field (layout.comments named)
    let core :=
      Parse.runsBind
        (() =>
          Parse.optional (() =>
            skip()
            let (named, nameComments) := name layout
            Field target dotted1 named nameComments))
        (suffixesAfter more self layout target)
        [dot, named]
        after
        [dot, named, ..after]
        rest
        (Some read)
        value
        byComputing
        (Parse.runsOptional
          (() =>
            skip()
            let (named, nameComments) := name layout
            Field target dotted1 named nameComments)
          [dot, named]
          (after ++ rest)
          read
          (Parse.runsBind
            (() => skip())
            (skipped =>
              let (named, nameComments) := name layout
              Field target dotted1 named nameComments)
            [dot]
            [named]
            [dot, named]
            (after ++ rest)
            ()
            read
            byComputing
            (runsSkip dot [named, ..after ++ rest])
            (Parse.runsMap
              (() => name layout)
              (found =>
                let (named, nameComments) := found
                Field target dotted1 named nameComments)
              [named]
              (after ++ rest)
              (field, layout.comments named)
              (runsName layout named field (after ++ rest) isName nameAllowed))))
        runsMore
    match core state starts honest with | (m, ran, others) => (m, (rewrite starts, dotAllowed, dotted then ran), others)

--| A round of `negationsFrom` that reads a `-`.
theorem runsNegation ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (minus: Parse.Located Token) (tokens rest: List (Parse.Located Token)) (operand: Expr)
    (isMinusSign: minus.value.kind = Op Minus)
    (allowed: layout.allows minus = True)
    (runsOperand: Parse.Runs (() => negationsFrom more self layout) tokens rest operand):
    Parse.Runs
      (() => negationsFrom (Succ more) self layout)
      [minus, ..tokens]
      rest
      (Negate (layout.comments minus) operand) :=
  state starts honest =>
    let signed := layout.comments minus
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped => Negate signed (negationsFrom more self layout))
        [minus]
        tokens
        [minus, ..tokens]
        rest
        ()
        (Negate signed operand)
        byComputing
        (runsSkip minus (tokens ++ rest))
        (Parse.runsMap
          (() => negationsFrom more self layout)
          (inner => Negate signed inner)
          tokens
          rest
          operand
          runsOperand)
    match core state starts honest with
      | (m, ran, others) => (m, (rewrite starts, allowed, isMinusSign then ran), others)

--| An atom, then its suffixes: what `negationsFrom` reads once the `-`s
--| are done. The suffix loop's fuel is the tokens left, so `runsSuffixes`
--| is asked for any fuel above what it reads.
theorem runsAtomThenSuffixes ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (atomTokens more rest: List (Parse.Located Token)) (first value: Expr)
    (runsAtom: Parse.Runs (() => atom self layout) atomTokens (more ++ rest) first)
    (runsSuffixes: ∀ (fuel: Nat) => more.length < fuel
      → Parse.Runs (() => suffixesFrom fuel self layout first) more rest value):
    Parse.Runs
      (() =>
        let first := atom self layout
        suffixesFrom (Parse.mark().left + 1) self layout first)
      (atomTokens ++ more)
      rest
      value :=
  state =>
    Parse.runsFromBind state
      (() => atom self layout)
      (first => suffixesFrom (Parse.mark().left + 1) self layout first)
      atomTokens
      more
      (atomTokens ++ more)
      rest
      first
      value
      byComputing
      runsAtom
      (middle atRest honest offset =>
        let lengths: middle.at.rest.length = more.length + rest.length :=
          rewrite atRest then List.lengthAppend more rest
        Parse.runsFromMark middle
          (at => suffixesFrom (at.left + 1) self layout first)
          more
          rest
          value
          (runsSuffixes (middle.at.left + 1) (arithmetic [honest, lengths]) middle))

--| An expression that `atom` and `suffixesFrom` read: an atom with its
--| calls and fields.
def Expr.isPostfix: Expr → Bool
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ _ _ => True
  | ListLiteral _ _ _ _ => True
  | Call _ _ _ _ _ => True
  | Field _ _ _ _ => True
  | _ => False

--| An operand of an operator chain: a postfix expression, or `-` before
--| an operand.
def Expr.isOperand: Expr → Bool
  | Negate _ _ => True
  | expr => expr.isPostfix

--| An operator chain or an operand: any expression but an `if`, which
--| stands only as a whole expression.
def Expr.isChain: Expr → Bool
  | Binary _ _ _ _ => True
  | expr => expr.isOperand

--| The level of a chain's outermost operator; 7, past every level, for an
--| operand.
def Expr.chainLevel: Expr → Nat
  | Binary operator _ _ _ => operator.level
  | _ => 7

--| The shape of the expressions the parser gives: a field's target is a
--| postfix expression, `-` stands before an operand, and an operator's
--| sides are grouped by precedence, the same level chaining from the left.
--| An `if`'s branches, blocks included, hold expressions of that shape
--| and end in a statement, not a comment line (`ShapedBody`). A closing
--| bracket holds a trailing comment only where rule N leaves one
--| (`settledCloser`): the parser builds its comments with
--| `Comments.closing`.
def Shaped: Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ inner close => Shaped inner ∧ settledCloser inner.endsWithComment close = True
  | Field target _ _ _ => target.isPostfix = True ∧ Shaped target
  | Negate _ operand => operand.isOperand = True ∧ Shaped operand
  | Binary operator _ left right =>
    operator.level ≤ left.chainLevel
      ∧ operator.level < right.chainLevel
      ∧ left.isChain = True
      ∧ right.isChain = True
      ∧ Shaped left
      ∧ Shaped right
  | ListLiteral open items trailingComma close =>
    ShapedItems items ∧ settledCloser (itemsEndWithComment open items) close = True
  | Call callee open arguments trailingComma close =>
    callee.isPostfix = True
      ∧ Shaped callee
      ∧ ShapedItems arguments
      ∧ settledCloser (itemsEndWithComment open arguments) close = True
  | If _ condition _ whenTrue _ whenFalse => Shaped condition ∧ ShapedBody whenTrue ∧ ShapedBody whenFalse

--| Each expression in the body is of the parser's shape.
def ShapedBody: Body → Prop
  | { statements } => ShapedLines statements ∧ ClosedLines statements

--| A statement that isn't a comment line.
def Coded: Statement → Prop
  | StatementNote _ => False
  | _ => True

--| There is a last line, and it is a statement: a body never ends in a
--| comment line (a comment below the last statement belongs to what
--| comes after the body).
def ClosedLines: List (Spaced Statement) → Prop
  | [] => False
  | [{ line, .. }] => Coded line
  | [_, ..rest] => ClosedLines rest

def ShapedLines: List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => ShapedStatement line ∧ ShapedLines rest

def ShapedStatement: Statement → Prop
  | Let _ _ _ _ inner => ShapedBody inner
  | Bare value => Shaped value
  | StatementNote _ => True

--| Each item is of the parser's shape.
def ShapedItems: List Expr → Prop
  | [] => True
  | [value, ..rest] => Shaped value ∧ ShapedItems rest

--| A closing bracket's comments, as the parser builds them, are what
--| rule N leaves there.
theorem closingSettled ∀ (close: Comments) (before: Bool): settledCloser before (close.closing before) = True :=
  match close, before with
    | { above, after = None }, _ => byComputing
    | { above = [], after = Some comment }, False => byComputing
    | { above = [], after = Some comment }, True => byComputing
    | { above = [first, ..rest], after = Some comment }, _ => byComputing

--| On comments rule N would leave on a closing bracket, the parser's
--| `Comments.closing` changes nothing.
theorem closingSame ∀ (close: Comments) (before: Bool)
    (settled: settledCloser before close = True):
    close.closing before = close :=
  match close, before, settled with
    | { above, after = None }, _, _ => byComputing
    | { above = [], after = Some comment }, True, _ => byComputing
    | { above = [first, ..rest], after = Some comment }, _, _ => byComputing

--| `tokens` spell `expr` at `layout`: its tokens in order, each of the kind
--| the expression has there and standing where the layout allows it
--| (anywhere, inside brackets), and each token's comments in the tree
--| those the parser takes from it (`Layout.comments`). An `if`'s `else` may
--| also start a line at the statement's column, and each of its branches
--| is spelled as a body (`SpelledBody`: one expression or a block)
--| whatever comes after it that may (`After`). A list or call has no
--| trailing comma: the printer writes none. For the forms `Shaped`
--| covers.
def Spelled (layout: Layout) (expr: Expr) (tokens: List (Parse.Located Token)): Prop := match expr with
  | Var name comments =>
    ∃ (token: Parse.Located Token) => tokens = [token]
      ∧ token.value.kind = Name name
      ∧ layout.allows token = True
      ∧ comments = layout.comments token
  | NumberLiteral digits comments =>
    ∃ (token: Parse.Located Token) => tokens = [token]
      ∧ token.value.kind = Number digits
      ∧ layout.allows token = True
      ∧ comments = layout.comments token
  | StringLiteral written comments =>
    ∃ (token: Parse.Located Token) => tokens = [token]
      ∧ token.value.kind = Str written
      ∧ layout.allows token = True
      ∧ comments = layout.comments token
  | Bracketed opened inner closed =>
    ∃ (open: Parse.Located Token) => ∃ (innerTokens: List (Parse.Located Token)) => ∃ (close: Parse.Located Token) =>
      tokens = [open, ..innerTokens ++ [close]]
        ∧ open.value.kind = Sign OpenParen
        ∧ layout.allows open = True
        ∧ close.value.kind = Sign CloseParen
        ∧ Spelled InBrackets inner innerTokens
        ∧ opened = layout.comments open
        ∧ closed = Layout.comments InBrackets close
  | Field target dotComments name nameComments =>
    ∃ (targetTokens: List (Parse.Located Token)) => ∃ (dot: Parse.Located Token) => ∃ (named: Parse.Located Token) =>
      tokens = targetTokens ++ [dot, named]
        ∧ dot.value.kind = Sign Dot
        ∧ layout.allows dot = True
        ∧ named.value.kind = Name name
        ∧ layout.allows named = True
        ∧ Spelled layout target targetTokens
        ∧ dotComments = layout.comments dot
        ∧ nameComments = layout.comments named
  | Negate minusComments operand =>
    ∃ (minus: Parse.Located Token) => ∃ (operandTokens: List (Parse.Located Token)) => tokens = [minus, ..operandTokens]
      ∧ minus.value.kind = Op Minus
      ∧ layout.allows minus = True
      ∧ Spelled layout operand operandTokens
      ∧ minusComments = layout.comments minus
  | Binary operator signComments left right =>
    ∃ (leftTokens: List (Parse.Located Token)) => ∃ (sign: Parse.Located Token) =>
      ∃ (rightTokens: List (Parse.Located Token)) => tokens = leftTokens ++ [sign, ..rightTokens]
        ∧ sign.value.kind = Op operator
        ∧ layout.allows sign = True
        ∧ Spelled layout left leftTokens
        ∧ Spelled layout right rightTokens
        ∧ signComments = layout.comments sign
  | ListLiteral opened items trailingComma closed =>
    ∃ (open: Parse.Located Token) => ∃ (itemTokens: List (Parse.Located Token)) => ∃ (close: Parse.Located Token) =>
      tokens = [open, ..itemTokens ++ [close]]
        ∧ open.value.kind = Sign OpenSquare
        ∧ layout.allows open = True
        ∧ close.value.kind = Sign CloseSquare
        ∧ SpelledItems items itemTokens
        ∧ opened = layout.comments open
        ∧ closed = Layout.comments InBrackets close
        ∧ trailingComma = False
  | Call callee opened arguments trailingComma closed =>
    ∃ (calleeTokens: List (Parse.Located Token)) => ∃ (open: Parse.Located Token) =>
      ∃ (argumentTokens: List (Parse.Located Token)) => ∃ (close: Parse.Located Token) => tokens
        = calleeTokens ++ [open, ..argumentTokens ++ [close]]
        ∧ open.value.kind = Sign OpenParen
        ∧ layout.allows open = True
        ∧ close.value.kind = Sign CloseParen
        ∧ Spelled layout callee calleeTokens
        ∧ SpelledItems arguments argumentTokens
        ∧ opened = layout.comments open
        ∧ closed = Layout.comments InBrackets close
        ∧ trailingComma = False
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    ∃ (ifToken: Parse.Located Token) => ∃ (conditionTokens: List (Parse.Located Token)) =>
      ∃ (thenToken: Parse.Located Token) => ∃ (trueTokens: List (Parse.Located Token)) =>
        ∃ (elseToken: Parse.Located Token) => ∃ (falseTokens: List (Parse.Located Token)) => tokens
          = [ifToken, ..conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]]
          ∧ ifToken.value.kind = Reserved IfKeyword
          ∧ layout.allows ifToken = True
          ∧ thenToken.value.kind = Reserved ThenKeyword
          ∧ layout.allows thenToken = True
          ∧ elseToken.value.kind = Reserved ElseKeyword
          ∧ layout.allowsElse elseToken = True
          ∧ Spelled layout condition conditionTokens
          ∧ (∀ (rest: List (Parse.Located Token)) => After layout trueTokens rest
            → SpelledBody layout whenTrue trueTokens rest)
          ∧ (∀ (rest: List (Parse.Located Token)) => After layout falseTokens rest
            → SpelledBody layout whenFalse falseTokens rest)
          ∧ ifComments = layout.comments ifToken
          ∧ thenComments = layout.comments thenToken
          ∧ elseComments = layout.comments elseToken

--| None of `tokens` is at `offset`.
def NotAt (offset: Nat): List (Parse.Located Token) → Prop
  | [] => True
  | [token, ..more] => (offset == token.offset) = False ∧ NotAt offset more

--| What follows an expression that is a whole statement, body or
--| condition (where an `if` may stand) ends every block inside it:
--| nothing, `then` or `else`, or a token that starts a line no deeper than
--| the statement and isn't one of the expression's own `tokens` (a
--| statement's first token is known by its offset). Inside brackets there
--| are no blocks.
def Settled (layout: Layout) (tokens rest: List (Parse.Located Token)): Prop := match layout with
  | InBrackets => True
  | InStatement column _ =>
    match rest with
      | [] => True
      | [next, .._] =>
        closesBlock next.value.kind = True
          ∨ ((next.value.startsLine && next.value.column <= column) = True ∧ NotAt next.offset tokens)

--| What may follow an expression read as a whole (`expression`, not an
--| operand): nothing that continues it, and nothing that would go on a
--| block inside it.
def After (layout: Layout) (tokens rest: List (Parse.Located Token)): Prop :=
  EndsExpression layout rest ∧ Settled layout tokens rest

theorem afterBrackets ∀ (tokens rest: List (Parse.Located Token))
    (ends: EndsExpression InBrackets rest):
    After InBrackets tokens rest :=
  (ends, byComputing)

theorem notAtBack ∀ (offset: Nat) (front back: List (Parse.Located Token))
    (clear: NotAt offset (front ++ back)):
    NotAt offset back :=
  match front, clear with
    | [], clear => clear
    | [head, ..tail], Both _ rest => notAtBack offset tail back rest

--| What settles some tokens settles the last of them.
theorem settledBack ∀ (layout: Layout) (front back rest: List (Parse.Located Token))
    (settled: Settled layout (front ++ back) rest):
    Settled layout back rest :=
  match layout, settled with
    | InBrackets, settled => byComputing
    | InStatement column from, settled =>
      match rest, settled with
        | [], settled => byComputing
        | [next, ..more], Inl closes => Inl closes
        | [next, ..more], Inr (Both low clear) => Inr ((low, (notAtBack next.offset front back clear)))

--| `tokens` spell a body that is one expression, at `layout`: the
--| expression, not starting a line deeper than the statement (which would
--| start a block).
def SpelledInline (layout: Layout) (found: Body) (tokens: List (Parse.Located Token)): Prop := match found with
  | { statements = [{ blankBefore, line = Bare value }] } =>
    blankBefore = False ∧ blockAhead layout tokens = False ∧ Spelled layout value tokens ∧ layout.headed value = value
  | _ => False

--| `tokens` spell the items of a list or the arguments of a call, between
--| the brackets: each value, and a comma after each but the last.
def SpelledItems (items: List Expr) (tokens: List (Parse.Located Token)): Prop := match items with
  | [] => tokens = []
  | [value] => Spelled InBrackets value tokens
  | [value, next, ..more] =>
    ∃ (valueTokens: List (Parse.Located Token)) => ∃ (commaToken: Parse.Located Token) =>
      ∃ (laterTokens: List (Parse.Located Token)) => tokens = valueTokens ++ [commaToken, ..laterTokens]
        ∧ commaToken.value.kind = Sign Comma
        ∧ Spelled InBrackets value valueTokens
        ∧ SpelledItems [next, ..more] laterTokens

--| What may follow an expression at `layout`: no call or field of its last
--| operand, and no operator.
def EndsExpression (layout: Layout) (rest: List (Parse.Located Token)): Prop :=
  endsSuffixes (suffixKind layout rest) = True ∧ Parse.operatorAhead (operatorLevels layout) 0 rest = False

--| What the expression parser is assumed to do for the nested expressions
--| of one being read: it reads each well-shaped, well-spelled expression of
--| fewer than `bound` tokens, at any layout, before anything that may
--| follow it.
def ReadsNested (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat): Prop :=
  ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token)) => Shaped expr
    → Spelled layout expr tokens
    → After layout tokens rest
    → tokens.length < bound
    → Parse.Runs (() => self layout) tokens rest expr

--| Whether a `-` the layout allows comes next: what `negationsFrom` reads.
def minusAhead (layout: Layout) (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => isMinus layout token
  | [] => False

--| Whether an `if` the layout allows comes next: what makes
--| `expressionRule` read an `if`.
def ifAhead (layout: Layout) (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => isIf layout token
  | [] => False

--| A postfix expression starts with neither `-` nor `if`.
theorem postfixStart ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (postfix: expr.isPostfix = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens):
    minusAhead layout (tokens ++ rest) = False ∧ ifAhead layout (tokens ++ rest) = False :=
  match expr with
    | Var name comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => rewrite split, kind, allowed then (byComputing, byComputing)
    | NumberLiteral digits comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => rewrite split, kind, allowed then (byComputing, byComputing)
    | StringLiteral written comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => rewrite split, kind, allowed then (byComputing, byComputing)
    | Bracketed opened inner closed =>
      match spelled with
        | (open, innerTokens, close, split, opens, allowed, others) =>
          rewrite split, opens, allowed then (byComputing, byComputing)
    | Field target dotComments name nameComments =>
      match spelled with
        | (targetTokens, dot, named, split, dotted, dotAllowed, isName, nameAllowed, spelledTarget, dotCommented,
            nameCommented) =>
          rewrite split, List.appendAssoc targetTokens [dot, named] rest then
            postfixStart layout target targetTokens [dot, named, ..rest] shaped.left shaped.right spelledTarget
    | ListLiteral opened listed trailingComma closed =>
      match spelled with
        | (open, itemTokens, close, split, opens, allowed, others) =>
          rewrite split, opens, allowed then (byComputing, byComputing)
    | Call callee opened arguments trailingComma closed =>
      match spelled with
        | (calleeTokens, open, argumentTokens, close, split, opens, allowed, closes, spelledCallee, spelledArguments,
            openCommented, closeCommented) =>
          rewrite split, List.appendAssoc calleeTokens [open, ..argumentTokens ++ [close]] rest then
            postfixStart layout callee calleeTokens
              ([open, ..argumentTokens ++ [close]] ++ rest)
              shaped.left
              shaped.right.left
              spelledCallee

theorem negationsEndRun ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (input: List (Parse.Located Token))
    (noMinus: minusAhead layout input = False) (state: Parse.State (Parse.Located Token))
    (starts: state.at.rest = input):
    Parse.runFrom state (() => (negationsFrom fuel self layout, Parse.mark()))
      = Parse.runFrom state (() => (postfix self layout, Parse.mark())) :=
  match fuel with
    | Zero => byComputing
    | Succ more =>
      rewrite starts then
        match input with
          | [] => byComputing
          | [token, ..later] => rewrite noMinus

--| With no `-` next, `negationsFrom` reads a postfix expression.
theorem runsNegationsEnd ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (tokens rest: List (Parse.Located Token)) (value: Expr)
    (noMinus: minusAhead layout (tokens ++ rest) = False)
    (runsPostfix: Parse.Runs (() => postfix self layout) tokens rest value):
    Parse.Runs (() => negationsFrom fuel self layout) tokens rest value :=
  state starts honest =>
    match runsPostfix state starts honest with
      | (m, ran, others) =>
        (m, (Eq.trans (negationsEndRun fuel self layout (tokens ++ rest) noMinus state starts) ran), others)

theorem operatorOfSign ∀ (layout: Layout) (level: Nat) (token: Parse.Located Token) (punctuation: Punctuation)
    (signed: token.value.kind = Sign punctuation):
    operatorOf layout level token = None :=
  rewrite signed

--| No operator is ahead where a punctuation sign comes next.
theorem noOperatorAtSign ∀ (layout: Layout) (lowest: Nat) (token: Parse.Located Token)
    (punctuation: Punctuation) (rest: List (Parse.Located Token))
    (signed: token.value.kind = Sign punctuation):
    Parse.operatorAhead (operatorLevels layout) lowest [token, ..rest] = False :=
  rewrite operatorOfSign layout 1 token punctuation signed,
      operatorOfSign layout 2 token punctuation signed,
      operatorOfSign layout 3 token punctuation signed,
      operatorOfSign layout 4 token punctuation signed,
      operatorOfSign layout 5 token punctuation signed,
      operatorOfSign layout 6 token punctuation signed

theorem endsAtClose ∀ (close: Parse.Located Token) (rest: List (Parse.Located Token))
    (closes: close.value.kind = Sign CloseParen):
    EndsExpression InBrackets [close, ..rest] :=
  ((rewrite closes), (noOperatorAtSign InBrackets 0 close CloseParen rest closes))

--| `postfix`'s atom and suffix loop read a postfix expression as the start
--| of a longer one: after its tokens the loop holds the expression, and
--| `continues` says what it does with `more`, the tokens after. By
--| induction on the expression: a field's target is such a start, and the
--| field is the loop's next round.
theorem runsPostfixPrefix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens more rest: List (Parse.Located Token)) (value: Expr)
    (postfix: expr.isPostfix = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (small: tokens.length <= bound)
    (continues: ∀ (fuel: Nat) => more.length < fuel
      → Parse.Runs (() => suffixesFrom fuel self layout expr) more rest value):
    Parse.Runs
      (() =>
        let first := atom self layout
        suffixesFrom (Parse.mark().left + 1) self layout first)
      (tokens ++ more)
      rest
      value :=
  match expr with
    | Var name comments =>
      match spelled with
        | (token, split, kind, allowed, commented) =>
          rewrite commented at continues then
            rewrite split then
              runsAtomThenSuffixes self layout
                [token]
                more
                rest
                (Var name (layout.comments token))
                value
                (runsAtomName self layout token name (more ++ rest) kind allowed)
                continues
    | NumberLiteral digits comments =>
      match spelled with
        | (token, split, kind, allowed, commented) =>
          rewrite commented at continues then
            rewrite split then
              runsAtomThenSuffixes self layout
                [token]
                more
                rest
                (NumberLiteral digits (layout.comments token))
                value
                (runsAtomNumber self layout token digits (more ++ rest) kind allowed)
                continues
    | StringLiteral written comments =>
      match spelled with
        | (token, split, kind, allowed, commented) =>
          rewrite commented at continues then
            rewrite split then
              runsAtomThenSuffixes self layout
                [token]
                more
                rest
                (StringLiteral written (layout.comments token))
                value
                (runsAtomString self layout token written (more ++ rest) kind allowed)
                continues
    | Bracketed opened inner closed =>
      match spelled with
        | (open, innerTokens, close, split, opens, allowed, closes, spelledInner, openCommented, closeCommented) =>
          let size: tokens.length = (innerTokens ++ [close]).length + 1 := rewrite split
          let sizes: (innerTokens ++ [close]).length = innerTokens.length + 1 := List.lengthAppend innerTokens [close]
          let settled: settledCloser inner.endsWithComment (Layout.comments InBrackets close) = True :=
            rewrite <- closeCommented then shaped.right
          let ranAtom :=
            runsAtomBracketed self layout open close innerTokens
              (more ++ rest)
              inner
              opens
              allowed
              closes
              (nested InBrackets inner innerTokens
                [close, ..more ++ rest]
                shaped.left
                spelledInner
                (afterBrackets innerTokens [close, ..more ++ rest] (endsAtClose close (more ++ rest) closes))
                (arithmetic [small, size, sizes]))
          rewrite openCommented, closeCommented at continues then
            rewrite split then
              runsAtomThenSuffixes self layout
                [open, ..innerTokens ++ [close]]
                more
                rest
                (Bracketed (layout.comments open) inner (Layout.comments InBrackets close))
                value
                (rewrite closingSame (Layout.comments InBrackets close) inner.endsWithComment settled at ranAtom then
                  ranAtom)
                continues
    | Field target dotComments name nameComments =>
      match spelled with
        | (targetTokens, dot, named, split, dotted, dotAllowed, isName, nameAllowed, spelledTarget, dotCommented,
            nameCommented) =>
          let size: tokens.length = targetTokens.length + 2 :=
            rewrite split then List.lengthAppend targetTokens [dot, named]
          rewrite dotCommented, nameCommented at continues then
            rewrite split, List.appendAssoc targetTokens [dot, named] more then
              runsPostfixPrefix self layout bound nested target targetTokens
                [dot, named, ..more]
                rest
                value
                shaped.left
                shaped.right
                spelledTarget
                (arithmetic [small, size])
                (fuel enough =>
                  match fuel with
                    | Succ less =>
                      runsSuffixesField less self layout target dot named name more rest value dotted dotAllowed isName
                          nameAllowed
                          (continues less (arithmetic [enough])))
    | ListLiteral opened listed trailingComma closed =>
      match spelled with
        | (open, itemTokens, close, split, opens, allowed, closes, spelledItems, openCommented, closeCommented,
            bareComma) =>
          let size: tokens.length = (itemTokens ++ [close]).length + 1 := rewrite split
          let sizes: (itemTokens ++ [close]).length = itemTokens.length + 1 := List.lengthAppend itemTokens [close]
          let settled: settledCloser
            (itemsEndWithComment (layout.comments open) listed)
            (Layout.comments InBrackets close)
            = True :=
            rewrite <- openCommented, <- closeCommented then shaped.right
          let ranAtom :=
            runsAtomList self layout open itemTokens
              (more ++ rest)
              close
              listed
              False
              opens
              allowed
              (runsItems self bound nested listed itemTokens
                (more ++ rest)
                close
                CloseSquare
                closes
                byComputing
                shaped.left
                spelledItems
                (arithmetic [small, size, sizes]))
          rewrite openCommented, closeCommented, bareComma at continues then
            rewrite split then
              runsAtomThenSuffixes self layout
                [open, ..itemTokens ++ [close]]
                more
                rest
                (ListLiteral (layout.comments open) listed False (Layout.comments InBrackets close))
                value
                (rewrite closingSame
                      (Layout.comments InBrackets close)
                      (itemsEndWithComment (layout.comments open) listed)
                      settled at ranAtom then
                  ranAtom)
                continues
    | Call callee opened arguments trailingComma closed =>
      match spelled with
        | (calleeTokens, open, argumentTokens, close, split, opens, allowed, closes, spelledCallee, spelledArguments,
            openCommented, closeCommented, bareComma) =>
          let size: tokens.length = calleeTokens.length + ((argumentTokens ++ [close]).length + 1) :=
            rewrite split then List.lengthAppend calleeTokens [open, ..argumentTokens ++ [close]]
          let sizes: (argumentTokens ++ [close]).length = argumentTokens.length + 1 :=
            List.lengthAppend argumentTokens [close]
          let settled: settledCloser
            (itemsEndWithComment (layout.comments open) arguments)
            (Layout.comments InBrackets close)
            = True :=
            rewrite <- openCommented, <- closeCommented then shaped.right.right.right
          rewrite openCommented, closeCommented, bareComma at continues then
            rewrite split, List.appendAssoc calleeTokens [open, ..argumentTokens ++ [close]] more then
              runsPostfixPrefix self layout bound nested callee calleeTokens
                ([open, ..argumentTokens ++ [close]] ++ more)
                rest
                value
                shaped.left
                shaped.right.left
                spelledCallee
                (arithmetic [small, size])
                (fuel enough =>
                  match fuel with
                    | Succ less =>
                      runsSuffixesCall less self layout callee open argumentTokens close more rest arguments False value
                          opens allowed
                          (runsItems self bound nested arguments argumentTokens
                            (more ++ rest)
                            close
                            CloseParen
                            closes
                            byComputing
                            shaped.right.right.left
                            spelledArguments
                            (arithmetic [small, size, sizes]))
                          (continues less (arithmetic [enough, List.lengthAppend (argumentTokens ++ [close]) more]))
                          settled)

theorem runsNegationsPostfix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (fuel: Nat) (tokens rest: List (Parse.Located Token))
    (postfix: expr.isPostfix = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    Parse.Runs (() => negationsFrom fuel self layout) tokens rest expr :=
  runsNegationsEnd fuel self layout tokens rest expr
    (postfixStart layout expr tokens rest postfix shaped spelled).left
    (Parse.runsBind
      (() => Parse.note (Parse.Problem.Expected "an expression"))
      (noted =>
        let first := atom self layout
        suffixesFrom (Parse.mark().left + 1) self layout first)
      []
      tokens
      tokens
      rest
      ()
      expr
      byComputing
      (Parse.runsNote (Parse.Problem.Expected "an expression") (tokens ++ rest))
      (rewrite <- List.appendNil tokens then
        runsPostfixPrefix self layout bound nested expr tokens [] rest expr postfix shaped spelled small
          (fuel positive => runsSuffixesEnd fuel self layout expr rest ends)))

--| `negationsFrom` reads an operand: its `-`s, then the postfix expression
--| under them.
theorem runsNegations ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (fuel: Nat) (tokens rest: List (Parse.Located Token))
    (operand: expr.isOperand = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound)
    (enough: tokens.length < fuel):
    Parse.Runs (() => negationsFrom fuel self layout) tokens rest expr :=
  match expr with
    | Negate minusComments inner =>
      match spelled, fuel with
        | (minus, operandTokens, split, kind, allowed, spelledInner, minusCommented), Succ more =>
          let size: tokens.length = operandTokens.length + 1 := rewrite split
          rewrite split, minusCommented then
            runsNegation more self layout minus operandTokens rest inner kind allowed
              (runsNegations self layout bound nested inner more operandTokens rest shaped.left shaped.right
                  spelledInner ends
                  (arithmetic [small, size])
                  (arithmetic [enough, size]))
    | Var name comments =>
      runsNegationsPostfix self layout bound nested
        (Var name comments)
        fuel
        tokens
        rest
        byComputing
        shaped
        spelled
        ends
        small
    | NumberLiteral digits comments =>
      runsNegationsPostfix self layout bound nested
        (NumberLiteral digits comments)
        fuel
        tokens
        rest
        byComputing
        shaped
        spelled
        ends
        small
    | StringLiteral written comments =>
      runsNegationsPostfix self layout bound nested
        (StringLiteral written comments)
        fuel
        tokens
        rest
        byComputing
        shaped
        spelled
        ends
        small
    | Bracketed opened inner closed =>
      runsNegationsPostfix self layout bound nested
        (Bracketed opened inner closed)
        fuel
        tokens
        rest
        byComputing
        shaped
        spelled
        ends
        small
    | Field target dotComments name nameComments =>
      runsNegationsPostfix self layout bound nested
        (Field target dotComments name nameComments)
        fuel
        tokens
        rest
        byComputing
        shaped
        spelled
        ends
        small
    | ListLiteral opened listed trailingComma closed =>
      runsNegationsPostfix self layout bound nested
        (ListLiteral opened listed trailingComma closed)
        fuel
        tokens
        rest
        byComputing
        shaped
        spelled
        ends
        small
    | Call callee opened arguments trailingComma closed =>
      runsNegationsPostfix self layout bound nested
        (Call callee opened arguments trailingComma closed)
        fuel
        tokens
        rest
        byComputing
        shaped
        spelled
        ends
        small

--| `operand` reads an operand that is spelled and shaped as one, where no
--| call or field follows it.
theorem runsOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (isOperand: expr.isOperand = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    Parse.Runs (() => operand self layout) tokens rest expr :=
  state starts honest =>
    let lengths: state.at.rest.length = tokens.length + rest.length := rewrite starts then List.lengthAppend tokens rest
    Parse.runsFromMark state
      (at => negationsFrom (at.left + 1) self layout)
      tokens
      rest
      expr
      (runsNegations self layout bound nested expr
        (state.at.left + 1)
        tokens
        rest
        isOperand
        shaped
        spelled
        ends
        small
        (arithmetic [honest, lengths])
        state)
      starts
      honest

--| What `operatorOf` gives at `level` for the token of `operator`.
def operatorAt (operator: Operator) (comments: Comments) (level: Nat): Option (Expr → Expr → Expr) :=
  if operator.level == level then Some (Binary operator comments) else None

theorem operatorOfOp ∀ (layout: Layout) (level: Nat) (sign: Parse.Located Token) (operator: Operator)
    (kind: sign.value.kind = Op operator)
    (allowed: layout.allows sign = True):
    operatorOf layout level sign = operatorAt operator (layout.comments sign) level :=
  rewrite kind, allowed then
    match same: operator.level == level with
      | True => byComputing
      | False => byComputing

theorem levelRange ∀ (operator: Operator): 1 <= operator.level ∧ operator.level <= 6 := match operator with
  | Or => ((arithmetic []), (arithmetic []))
  | And => ((arithmetic []), (arithmetic []))
  | EqualTo => ((arithmetic []), (arithmetic []))
  | NotEqual => ((arithmetic []), (arithmetic []))
  | LessThan => ((arithmetic []), (arithmetic []))
  | LessEqual => ((arithmetic []), (arithmetic []))
  | Append => ((arithmetic []), (arithmetic []))
  | Plus => ((arithmetic []), (arithmetic []))
  | Minus => ((arithmetic []), (arithmetic []))
  | Times => ((arithmetic []), (arithmetic []))
  | Divide => ((arithmetic []), (arithmetic []))
  | Remainder => ((arithmetic []), (arithmetic []))

--| The token of an operator the layout allows is found at its level's
--| place in `operatorLevels`, chaining from the left.
theorem operatorFound ∀ (layout: Layout) (sign: Parse.Located Token) (operator: Operator)
    (kind: sign.value.kind = Op operator)
    (allowed: layout.allows sign = True):
    Parse.operatorFrom sign 0 (operatorLevels layout)
      = Some (operator.level - 1, LeftAssociative, Binary operator (layout.comments sign)) :=
  let at1 := operatorOfOp layout 1 sign operator kind allowed
  let at2 := operatorOfOp layout 2 sign operator kind allowed
  let at3 := operatorOfOp layout 3 sign operator kind allowed
  let at4 := operatorOfOp layout 4 sign operator kind allowed
  let at5 := operatorOfOp layout 5 sign operator kind allowed
  let at6 := operatorOfOp layout 6 sign operator kind allowed
  match operator with
    | Or => rewrite at1
    | And => rewrite at1, at2
    | EqualTo => rewrite at1, at2, at3
    | NotEqual => rewrite at1, at2, at3
    | LessThan => rewrite at1, at2, at3
    | LessEqual => rewrite at1, at2, at3
    | Append => rewrite at1, at2, at3, at4
    | Plus => rewrite at1, at2, at3, at4, at5
    | Minus => rewrite at1, at2, at3, at4, at5
    | Times => rewrite at1, at2, at3, at4, at5, at6
    | Divide => rewrite at1, at2, at3, at4, at5, at6
    | Remainder => rewrite at1, at2, at3, at4, at5, at6

theorem chainTreeOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (isOperand: expr.isOperand = True)
    (level: expr.chainLevel = 7)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    ∃ (tree: Parse.OperatorTree (Parse.Located Token) Expr) => tree.reads = tokens
      ∧ tree.value = expr
      ∧ tree.Formed (operatorLevels layout) 6
      ∧ tree.RunsEach (() => operand self layout) rest
      ∧ tree.top 6 + 1 = expr.chainLevel
      ∧ (∀ (below: Nat) => below + 1 <= expr.chainLevel → below < 6 → below < tree.bound 6) :=
  (
    (Operand tokens expr),
    byComputing,
    byComputing,
    byComputing,
    (runsOperand self layout bound nested expr tokens rest isOperand shaped spelled ends small),
    level.flipped,
    (below fits under => under)
  )

--| An operator chain as the tree `Parse.runsOperators` reads: its
--| operators in the tree's shape, each at its level's place, and its
--| operands read by `operand` where they stand.
theorem chainTree ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (chain: expr.isChain = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: endsSuffixes (suffixKind layout rest) = True)
    (small: tokens.length <= bound):
    ∃ (tree: Parse.OperatorTree (Parse.Located Token) Expr) => tree.reads = tokens
      ∧ tree.value = expr
      ∧ tree.Formed (operatorLevels layout) 6
      ∧ tree.RunsEach (() => operand self layout) rest
      ∧ tree.top 6 + 1 = expr.chainLevel
      ∧ (∀ (below: Nat) => below + 1 <= expr.chainLevel → below < 6 → below < tree.bound 6) :=
  match expr with
    | Binary operator signComments left right =>
      match shaped, spelled with
        | (leftLevel, rightLevel, leftChain, rightChain, shapedLeft, shapedRight), (leftTokens, sign, rightTokens,
            split, kind, allowed, spelledLeft, spelledRight, signCommented) =>
          let size: tokens.length = leftTokens.length + (rightTokens.length + 1) :=
            rewrite split then List.lengthAppend leftTokens [sign, ..rightTokens]
          let signEnds: endsSuffixes (suffixKind layout [sign, ..rightTokens ++ rest]) = True := rewrite allowed, kind
          let range := levelRange operator
          let leftResult :=
            chainTree self layout bound nested left leftTokens
              [sign, ..rightTokens ++ rest]
              leftChain
              shapedLeft
              spelledLeft
              signEnds
              (arithmetic [small, size])
          let rightResult :=
            chainTree self layout bound nested right rightTokens rest rightChain shapedRight spelledRight ends
              (arithmetic [small, size])
          match leftResult, rightResult with
            | (leftTree, leftReads, leftValue, leftFormed, leftRuns, leftTop, leftBound), (rightTree, rightReads,
                rightValue, rightFormed, rightRuns, rightTop, rightBound) => (
              (Joined sign
                (operator.level - 1)
                LeftAssociative
                (Binary operator (layout.comments sign))
                leftTree
                rightTree),
              (rewrite leftReads, rightReads, split),
              (rewrite leftValue, rightValue, signCommented),
              ((
                (operatorFound layout sign operator kind allowed),
                (arithmetic [range.right, range.left]),
                (leftBound
                  (operator.level - 1)
                  (arithmetic [leftLevel, range.left])
                  (arithmetic [range.right, range.left])),
                (arithmetic [rightLevel, rightTop, range.left]),
                leftFormed,
                rightFormed
              )),
              (((rewrite rightReads then leftRuns), rightRuns)),
              (arithmetic [range.left]),
              (below fits under => arithmetic [fits, range.left])
            )
    | Negate minusComments inner =>
      chainTreeOperand self layout bound nested
        (Negate minusComments inner)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small
    | Var name comments =>
      chainTreeOperand self layout bound nested
        (Var name comments)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small
    | NumberLiteral digits comments =>
      chainTreeOperand self layout bound nested
        (NumberLiteral digits comments)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small
    | StringLiteral written comments =>
      chainTreeOperand self layout bound nested
        (StringLiteral written comments)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small
    | Bracketed opened inner closed =>
      chainTreeOperand self layout bound nested
        (Bracketed opened inner closed)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small
    | Field target dotComments name nameComments =>
      chainTreeOperand self layout bound nested
        (Field target dotComments name nameComments)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small
    | ListLiteral opened listed trailingComma closed =>
      chainTreeOperand self layout bound nested
        (ListLiteral opened listed trailingComma closed)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small
    | Call callee opened arguments trailingComma closed =>
      chainTreeOperand self layout bound nested
        (Call callee opened arguments trailingComma closed)
        tokens
        rest
        byComputing
        byComputing
        shaped
        spelled
        ends
        small

--| A chain starts with no `if`.
theorem chainStart ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (chain: expr.isChain = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens):
    ifAhead layout (tokens ++ rest) = False :=
  match expr with
    | Binary operator signComments left right =>
      match shaped, spelled with
        | (leftLevel, rightLevel, leftChain, rightChain, shapedLeft, shapedRight), (leftTokens, sign, rightTokens,
            split, kind, allowed, spelledLeft, spelledRight, signCommented) =>
          rewrite split, List.appendAssoc leftTokens [sign, ..rightTokens] rest then
            chainStart layout left leftTokens [sign, ..rightTokens ++ rest] leftChain shapedLeft spelledLeft
    | Negate minusComments inner =>
      match spelled with
        | (minus, operandTokens, split, kind, allowed, spelledInner, minusCommented) => rewrite split, kind, allowed
    | Var name comments => (postfixStart layout (Var name comments) tokens rest byComputing shaped spelled).right
    | NumberLiteral digits comments =>
      (postfixStart layout (NumberLiteral digits comments) tokens rest byComputing shaped spelled).right
    | StringLiteral written comments =>
      (postfixStart layout (StringLiteral written comments) tokens rest byComputing shaped spelled).right
    | Bracketed opened inner closed =>
      (postfixStart layout (Bracketed opened inner closed) tokens rest byComputing shaped spelled).right
    | Field target dotComments name nameComments =>
      (postfixStart layout (Field target dotComments name nameComments) tokens rest byComputing shaped spelled).right
    | ListLiteral opened listed trailingComma closed =>
      (postfixStart layout
        (ListLiteral opened listed trailingComma closed)
        tokens
        rest
        byComputing
        shaped
        spelled).right
    | Call callee opened arguments trailingComma closed =>
      (postfixStart layout
        (Call callee opened arguments trailingComma closed)
        tokens
        rest
        byComputing
        shaped
        spelled).right

theorem chainRuleRun ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (state: Parse.State (Parse.Located Token))
    (noIf: ifAhead layout state.at.rest = False):
    Parse.runFrom state (() => (expressionRule self layout, Parse.mark()))
      = Parse.runFrom state (() =>
        (Parse.operators "an operator" (operatorLevels layout) (() => operand self layout), Parse.mark())) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => byComputing
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite noIf

--| One level of the expression parser on anything but an `if`:
--| `expressionRule` reads a chain, given that `self` reads the expressions
--| nested in it.
theorem runsChainRule ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (chain: expr.isChain = True)
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (ends: EndsExpression layout rest)
    (small: tokens.length <= bound):
    Parse.Runs (() => expressionRule self layout) tokens rest expr :=
  match chainTree self layout bound nested expr tokens rest chain shaped spelled ends.left small with
    | (tree, reads, value, formed, runsEach, others) =>
      let runs: Parse.Runs
        (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout))
        tokens
        rest
        expr :=
        rewrite <- reads, <- value then
          Parse.runsOperators "an operator"
            (operatorLevels layout)
            (() => operand self layout)
            tree
            rest
            formed
            runsEach
            ends.right
      state starts honest =>
        match runs state starts honest with
          | (m, ran, after) => (
            m,
            (Eq.trans
              (chainRuleRun self layout state
                (rewrite starts then chainStart layout expr tokens rest chain shaped spelled))
              ran),
            after
          )

--| One level of the expression parser: `expressionRule` reads an `if` or
--| a chain, given that `self` reads the expressions nested in it.
theorem runsExpressionRule ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (declines: DeclinesNested self)
    (expr: Expr) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (after: After layout tokens rest)
    (small: tokens.length <= bound):
    Parse.Runs (() => expressionRule self layout) tokens rest expr :=
  match expr, shaped, spelled with
    | If ifComments condition thenComments whenTrue elseComments whenFalse, shaped, spelled =>
      runsIfSpelled self layout bound nested declines ifComments condition thenComments whenTrue elseComments whenFalse
          tokens rest shaped spelled after small
    | Var name comments, shaped, spelled =>
      runsChainRule self layout bound nested (Var name comments) tokens rest byComputing shaped spelled after.left small
    | NumberLiteral digits comments, shaped, spelled =>
      runsChainRule self layout bound nested
        (NumberLiteral digits comments)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small
    | StringLiteral written comments, shaped, spelled =>
      runsChainRule self layout bound nested
        (StringLiteral written comments)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small
    | Bracketed opened inner closed, shaped, spelled =>
      runsChainRule self layout bound nested
        (Bracketed opened inner closed)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small
    | Field target dotComments name nameComments, shaped, spelled =>
      runsChainRule self layout bound nested
        (Field target dotComments name nameComments)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small
    | Negate minusComments operand, shaped, spelled =>
      runsChainRule self layout bound nested
        (Negate minusComments operand)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small
    | Binary operator signComments left right, shaped, spelled =>
      runsChainRule self layout bound nested
        (Binary operator signComments left right)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small
    | ListLiteral opened listed trailingComma closed, shaped, spelled =>
      runsChainRule self layout bound nested
        (ListLiteral opened listed trailingComma closed)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small
    | Call callee opened arguments trailingComma closed, shaped, spelled =>
      runsChainRule self layout bound nested
        (Call callee opened arguments trailingComma closed)
        tokens
        rest
        byComputing
        shaped
        spelled
        after.left
        small

--| The parser reads back what spells an expression: on tokens that spell
--| `expr` at `layout` (`Spelled`), for an `expr` of the parser's shape
--| (`Shaped`), followed by what may follow it (`After`), `expression
--| layout` reads exactly those tokens and gives `expr`. Each level reads
--| with the level below, which reads every shorter expression and, not
--| being the innermost, declines at a keyword.
theorem runsExpression ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (after: After layout tokens rest):
    Parse.Runs (() => expression layout) tokens rest expr :=
  Parse.runsRecursiveWithFact expressionRule
    (layout tokens rest expr => Shaped expr ∧ Spelled layout expr tokens ∧ After layout tokens rest)
    DeclinesNested
    (Parse.recursiveFacts expressionRule DeclinesNested (self layout token later keyword reserved notIf =>
      expressionRuleDeclines self layout token later keyword reserved notIf))
    (layout tokens rest expr (Both shaped (Both spelled after)) =>
      match spelledStart layout expr tokens shaped spelled with
        | (first, others, split, _) =>
          let size: tokens.length = Succ others.length := rewrite split
          arithmetic [size])
    (self layout tokens rest expr (Both shaped (Both spelled after)) declines nested =>
      runsExpressionRule self layout tokens.length
        (nestedLayout nestedExpr nestedTokens nestedRest nestedShaped nestedSpelled nestedAfter shorter =>
          nested nestedLayout nestedTokens nestedRest nestedExpr
            (Both nestedShaped (Both nestedSpelled nestedAfter))
            shorter)
        declines
        expr
        tokens
        rest
        shaped
        spelled
        after
        (arithmetic []))
    layout
    tokens
    rest
    expr
    (Both shaped (Both spelled after))

--| The kinds of token an expression starts with.
def startsExpression: Kind → Bool
  | Name _ => True
  | Number _ => True
  | Str _ => True
  | Sign OpenParen => True
  | Sign OpenSquare => True
  | Op Minus => True
  | Reserved IfKeyword => True
  | _ => False

--| A spelled expression has a first token, of a kind that starts one.
theorem spelledStart ∀ (layout: Layout) (expr: Expr) (tokens: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens):
    ∃ (first: Parse.Located Token) => ∃ (others: List (Parse.Located Token)) => tokens = [first, ..others]
      ∧ startsExpression first.value.kind = True :=
  match expr with
    | If ifComments condition thenComments whenTrue elseComments whenFalse =>
      match spelled with
        | (ifToken, conditionTokens, thenToken, trueTokens, elseToken, falseTokens, split, isIfToken, others) => (
          ifToken,
          (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]),
          split,
          (rewrite isIfToken)
        )
    | Var name comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => (token, [], split, (rewrite kind))
    | NumberLiteral digits comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => (token, [], split, (rewrite kind))
    | StringLiteral written comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => (token, [], split, (rewrite kind))
    | Bracketed opened inner closed =>
      match spelled with
        | (open, innerTokens, close, split, opens, others) => (open, (innerTokens ++ [close]), split, (rewrite opens))
    | ListLiteral opened listed trailingComma closed =>
      match spelled with
        | (open, itemTokens, close, split, opens, others) => (open, (itemTokens ++ [close]), split, (rewrite opens))
    | Negate minusComments operand =>
      match spelled with
        | (minus, operandTokens, split, kind, others) => (minus, operandTokens, split, (rewrite kind))
    | Field target dotComments name nameComments =>
      match spelled with
        | (targetTokens, dot, named, split, dotted, dotAllowed, isName, nameAllowed, spelledTarget, dotCommented,
            nameCommented) =>
          match spelledStart layout target targetTokens shaped.right spelledTarget with
            | (first, others, targetSplit, startKind) =>
              (first, (others ++ [dot, named]), (rewrite split, targetSplit), startKind)
    | Call callee opened arguments trailingComma closed =>
      match spelled with
        | (calleeTokens, open, argumentTokens, close, split, opens, allowed, closes, spelledCallee, spelledArguments,
            openCommented, closeCommented) =>
          match spelledStart layout callee calleeTokens shaped.right.left spelledCallee with
            | (first, others, calleeSplit, startKind) =>
              (first, (others ++ [open, ..argumentTokens ++ [close]]), (rewrite split, calleeSplit), startKind)
    | Binary operator signComments left right =>
      match shaped, spelled with
        | (leftLevel, rightLevel, leftChain, rightChain, shapedLeft, shapedRight), (leftTokens, sign, rightTokens,
            split, kind, allowed, spelledLeft, spelledRight, signCommented) =>
          match spelledStart layout left leftTokens shapedLeft spelledLeft with
            | (first, others, leftSplit, startKind) =>
              (first, (others ++ [sign, ..rightTokens]), (rewrite split, leftSplit), startKind)

-- Clearing the comments above an expression's first token
-- (`Layout.headed`, which `bareStatement` applies) changes nothing where
-- none are there, and keeps the parser's shape.

--| The own-line comments the first of `tokens` holds at `layout`.
def headAbove (layout: Layout) (tokens: List (Parse.Located Token)): List Comment := match tokens with
  | [first, .._] => (layout.comments first).above
  | [] => []

theorem noAboveCleared ∀ (expr: Expr) (none: expr.firstAbove = []): expr.withoutFirstAbove = expr :=
  match expr, none with
    | Var name { above, after }, none => rewrite none
    | NumberLiteral digits { above, after }, none => rewrite none
    | StringLiteral written { above, after }, none => rewrite none
    | Bracketed ({ above, after }) inner close, none => rewrite none
    | ListLiteral ({ above, after }) items trailingComma close, none => rewrite none
    | Call callee open arguments trailingComma close, none => rewrite noAboveCleared callee none
    | Field target dot name nameComments, none => rewrite noAboveCleared target none
    | Negate ({ above, after }) operand, none => rewrite none
    | Binary operator sign left right, none => rewrite noAboveCleared left none
    | If ({ above, after }) condition thenComments whenTrue elseComments whenFalse, none => rewrite none

--| The comments above a spelled expression are those of its first token.
theorem spelledFirstAbove ∀ (layout: Layout) (expr: Expr) (tokens: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens):
    expr.firstAbove = headAbove layout tokens :=
  match expr with
    | If ifComments condition thenComments whenTrue elseComments whenFalse =>
      match spelled with
        | (ifToken, conditionTokens, thenToken, trueTokens, elseToken, falseTokens, split, isIfToken, ifAllowed, isThen,
            thenAllowed, isElse, elseAllowed, spelledCondition, spelledTrue, spelledFalse, ifCommented, others) =>
          rewrite split, ifCommented
    | Var name comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => rewrite split, commented
    | NumberLiteral digits comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => rewrite split, commented
    | StringLiteral written comments =>
      match spelled with
        | (token, split, kind, allowed, commented) => rewrite split, commented
    | Bracketed opened inner closed =>
      match spelled with
        | (open, innerTokens, close, split, opens, allowed, closes, spelledInner, openCommented, others) =>
          rewrite split, openCommented
    | ListLiteral opened listed trailingComma closed =>
      match spelled with
        | (open, itemTokens, close, split, opens, allowed, closes, spelledItems, openCommented, others) =>
          rewrite split, openCommented
    | Negate minusComments operand =>
      match spelled with
        | (minus, operandTokens, split, kind, allowed, spelledOperand, commented) => rewrite split, commented
    | Field target dotComments name nameComments =>
      match spelled with
        | (targetTokens, dot, named, split, dotted, dotAllowed, isName, nameAllowed, spelledTarget, dotCommented,
            nameCommented) =>
          match spelledStart layout target targetTokens shaped.right spelledTarget with
            | (first, others, targetSplit, startKind) =>
              let inner := spelledFirstAbove layout target targetTokens shaped.right spelledTarget
              rewrite split, targetSplit then (rewrite targetSplit at inner then inner)
    | Call callee opened arguments trailingComma closed =>
      match spelled with
        | (calleeTokens, open, argumentTokens, close, split, opens, allowed, closes, spelledCallee, spelledArguments,
            openCommented, closeCommented) =>
          match spelledStart layout callee calleeTokens shaped.right.left spelledCallee with
            | (first, others, calleeSplit, startKind) =>
              let inner := spelledFirstAbove layout callee calleeTokens shaped.right.left spelledCallee
              rewrite split, calleeSplit then (rewrite calleeSplit at inner then inner)
    | Binary operator signComments left right =>
      match shaped, spelled with
        | (leftLevel, rightLevel, leftChain, rightChain, shapedLeft, shapedRight), (leftTokens, sign, rightTokens,
            split, kind, allowed, spelledLeft, spelledRight, signCommented) =>
          match spelledStart layout left leftTokens shapedLeft spelledLeft with
            | (first, others, leftSplit, startKind) =>
              let inner := spelledFirstAbove layout left leftTokens shapedLeft spelledLeft
              rewrite split, leftSplit then (rewrite leftSplit at inner then inner)

--| An offset is its own. The expression proofs and the spelling proofs
--| both rewrite with it; it is the one copy.
theorem ownOffset ∀ (offset: Nat): (offset == offset) = True := arithmetic

--| A statement's first token holds no comments above it in the tree.
theorem startAbove ∀ (column: Nat) (first: Parse.Located Token):
    ((InStatement column first.offset).comments first).above = [] :=
  rewrite ownOffset first.offset

--| Clearing changes nothing where the first token holds no comments.
theorem spelledHeaded ∀ (layout: Layout) (expr: Expr) (tokens: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (none: headAbove layout tokens = []):
    layout.headed expr = expr :=
  match layout, spelled, none with
    | InBrackets, spelled, none => byComputing
    | InStatement column start, spelled, none =>
      noAboveCleared expr (Eq.trans (spelledFirstAbove (InStatement column start) expr tokens shaped spelled) none)

theorem clearedPostfix ∀ (expr: Expr): expr.withoutFirstAbove.isPostfix = expr.isPostfix := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call _ _ _ _ _ => byComputing
  | Field _ _ _ _ => byComputing
  | Negate _ _ => byComputing
  | Binary _ _ _ _ => byComputing
  | If _ _ _ _ _ _ => byComputing

theorem clearedChain ∀ (expr: Expr): expr.withoutFirstAbove.isChain = expr.isChain := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call _ _ _ _ _ => byComputing
  | Field _ _ _ _ => byComputing
  | Negate _ _ => byComputing
  | Binary _ _ _ _ => byComputing
  | If _ _ _ _ _ _ => byComputing

theorem clearedLevel ∀ (expr: Expr): expr.withoutFirstAbove.chainLevel = expr.chainLevel := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call _ _ _ _ _ => byComputing
  | Field _ _ _ _ => byComputing
  | Negate _ _ => byComputing
  | Binary _ _ _ _ => byComputing
  | If _ _ _ _ _ _ => byComputing

--| Whether the token before a closing bracket has a trailing comment
--| doesn't depend on the comments above the opening one.
theorem clearedOpenEnds ∀ (open: Comments) (items: List Expr):
    itemsEndWithComment { open | above = [] } items = itemsEndWithComment open items :=
  match items with
    | [] => byComputing
    | [last] => byComputing
    | [first, second, ..rest] => clearedOpenEnds open [second, ..rest]

theorem shapedCleared ∀ (expr: Expr) (shaped: Shaped expr): Shaped expr.withoutFirstAbove := match expr, shaped with
  | Var name comments, shaped => shaped
  | NumberLiteral digits comments, shaped => shaped
  | StringLiteral written comments, shaped => shaped
  | Bracketed open inner close, shaped => shaped
  | ListLiteral open items trailingComma close, Both shapedItems settled =>
    (shapedItems, (rewrite clearedOpenEnds open items then settled))
  | Call callee open arguments trailingComma close, Both postfix (Both shapedCallee others) =>
    ((Eq.trans (clearedPostfix callee) postfix), (shapedCleared callee shapedCallee), others)
  | Field target dot name nameComments, Both postfix shapedTarget =>
    ((Eq.trans (clearedPostfix target) postfix), (shapedCleared target shapedTarget))
  | Negate minus operand, shaped => shaped
  | Binary operator sign left right, Both leftLevel
      (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))) => (
    (rewrite clearedLevel left then leftLevel),
    rightLevel,
    (Eq.trans (clearedChain left) leftChain),
    rightChain,
    (shapedCleared left shapedLeft),
    shapedRight
  )
  | If ifComments condition thenComments whenTrue elseComments whenFalse, shaped => shaped

theorem shapedHeaded ∀ (layout: Layout) (expr: Expr) (shaped: Shaped expr): Shaped (layout.headed expr) :=
  match layout with
    | InBrackets => shaped
    | InStatement column start => shapedCleared expr shaped

--| The signs that close a list or a call's arguments.
def bracketSign: Punctuation → Bool
  | CloseParen => True
  | CloseSquare => True
  | _ => False

theorem startNoBracket ∀ (kind: Kind) (wanted: Punctuation)
    (starts: startsExpression kind = True)
    (bracket: bracketSign wanted = True):
    (signIs wanted kind).isSome = False :=
  match kind with
    | Name text => byComputing
    | Number digits => byComputing
    | Str written => byComputing
    | Op operator => byComputing
    | Reserved keyword => byComputing
    | Sign punctuation =>
      match punctuation, wanted with
        | OpenParen, CloseParen => byComputing
        | OpenParen, CloseSquare => byComputing
        | OpenSquare, CloseParen => byComputing
        | OpenSquare, CloseSquare => byComputing

theorem endsAtSign ∀ (token: Parse.Located Token) (punctuation: Punctuation) (rest: List (Parse.Located Token))
    (signed: token.value.kind = Sign punctuation)
    (quiet: endsSuffixes (Sign punctuation) = True):
    EndsExpression InBrackets [token, ..rest] :=
  ((rewrite signed then quiet), (noOperatorAtSign InBrackets 0 token punctuation rest signed))

theorem bracketQuiet ∀ (closer: Punctuation) (bracket: bracketSign closer = True): endsSuffixes (Sign closer) = True :=
  match closer with
    | CloseParen => byComputing
    | CloseSquare => byComputing

theorem noCommaAtBracket ∀ (close: Parse.Located Token) (closer: Punctuation) (after: List (Parse.Located Token))
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True):
    signAhead Comma [close, ..after] = False :=
  rewrite closes then
    match closer with
      | CloseParen => byComputing
      | CloseSquare => byComputing

theorem bracketThere ∀ (close: Parse.Located Token) (closer: Punctuation)
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True):
    (signIs closer close.value.kind).isSome = True :=
  rewrite closes then
    match closer with
      | CloseParen => byComputing
      | CloseSquare => byComputing

--| `closingNext` reads nothing and says whether `closer` comes next.
theorem runsClosingNext ∀ (closer: Punctuation) (rest: List (Parse.Located Token)):
    Parse.Runs (() => closingNext closer) [] rest (signAhead closer rest) :=
  state starts honest =>
    let core := Parse.runsPure (signAhead closer rest) rest state starts honest
    match core with
      | (m, ran, others) => (
        m,
        (rewrite <- starts then
          (Eq.trans
            (Parse.runFromMark state (at => (signAhead closer at.rest, Parse.mark())))
            (rewrite starts then ran))),
        others
      )

--| `itemsFrom` reads the items of a list or call up to its closing
--| bracket: each item with its comma, the last without, given that `self`
--| reads each value; no comma follows the last.
--|
--| Proof idea: by induction on the items. After each comma the next
--| item's first token starts an expression, so it is not `closer`
--| (`itemsStart`) and the loop goes on.
theorem runsItemsFrom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat)
    (nested: ReadsNested self bound)
    (head: Expr) (tail found: List Expr) (fuel: Nat) (tokens after: List (Parse.Located Token))
    (close: Parse.Located Token) (closer: Punctuation)
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True)
    (shaped: ShapedItems [head, ..tail])
    (spelled: SpelledItems [head, ..tail] tokens)
    (small: tokens.length < bound)
    (enough: tail.length < fuel):
    Parse.Runs (() => itemsFrom fuel self closer found) tokens [close, ..after] (
      found.reverse ++ [head, ..tail],
      False
    ) :=
  match tail with
    | [] =>
      match fuel with
        | Succ more =>
          Parse.runsBind
            (() => item self)
            (itemsAfter more self closer found)
            tokens
            []
            tokens
            [close, ..after]
            (head, False)
            (found.reverse ++ [head], False)
            (List.appendNil tokens).flipped
            (runsItemLast self head tokens
              [close, ..after]
              (nested InBrackets head tokens
                [close, ..after]
                shaped.left
                spelled
                (afterBrackets tokens
                  [close, ..after]
                  (endsAtSign close closer after closes (bracketQuiet closer bracket)))
                small)
              (noCommaAtBracket close closer after closes bracket))
            (rewrite <- List.reverseCons head found then Parse.runsPure _ [close, ..after])
    | [next, ..more] =>
      match spelled, shaped, fuel with
        | (valueTokens, commaToken, laterTokens, split, isComma, spelledValue, spelledLater), (shapedValue,
            shapedLater), Succ less =>
          let sizes: tokens.length = valueTokens.length + (laterTokens.length + 1) :=
            rewrite split then List.lengthAppend valueTokens [commaToken, ..laterTokens]
          let notClosed: signAhead closer (laterTokens ++ [close, ..after]) = False :=
            match itemsStart next more laterTokens shapedLater spelledLater with
              | (first, others, laterSplit, startKind, _) =>
                rewrite laterSplit then startNoBracket first.value.kind closer startKind bracket
          let rounds: Parse.Runs (() => itemsFrom less self closer [head, ..found]) laterTokens [close, ..after] (
            found.reverse ++ [head, next, ..more],
            False
          ) :=
            rewrite <- List.appendAssoc found.reverse [head] [next, ..more], <- List.reverseCons head found then
              runsItemsFrom self bound nested next more
                [head, ..found]
                less
                laterTokens
                after
                close
                closer
                closes
                bracket
                shapedLater
                spelledLater
                (arithmetic [small, sizes])
                (arithmetic [enough])
          rewrite split then
            Parse.runsBind
              (() => item self)
              (itemsAfter less self closer found)
              (valueTokens ++ [commaToken])
              laterTokens
              (valueTokens ++ [commaToken, ..laterTokens])
              [close, ..after]
              (head, True)
              (found.reverse ++ [head, next, ..more], False)
              (Eq.flipped (List.appendAssoc valueTokens [commaToken] laterTokens))
              (runsItemComma self head commaToken valueTokens
                (laterTokens ++ [close, ..after])
                (nested InBrackets head valueTokens
                  [commaToken, ..laterTokens ++ [close, ..after]]
                  shapedValue
                  spelledValue
                  (afterBrackets valueTokens
                    [commaToken, ..laterTokens ++ [close, ..after]]
                    (endsAtSign commaToken Comma (laterTokens ++ [close, ..after]) isComma byComputing))
                  (arithmetic [small, sizes]))
                isComma)
              (Parse.runsBind
                (() => closingNext closer)
                (ahead => if ahead then ([head, ..found].reverse, True) else itemsFrom less self closer [head, ..found])
                []
                laterTokens
                laterTokens
                [close, ..after]
                (signAhead closer (laterTokens ++ [close, ..after]))
                (found.reverse ++ [head, next, ..more], False)
                byComputing
                (runsClosingNext closer (laterTokens ++ [close, ..after]))
                (rewrite notClosed then rounds))

--| The tokens of one or more items start with a token that starts an
--| expression, and there are at least as many as items.
theorem itemsStart ∀ (head: Expr) (tail: List Expr) (tokens: List (Parse.Located Token))
    (shaped: ShapedItems [head, ..tail])
    (spelled: SpelledItems [head, ..tail] tokens):
    ∃ (first: Parse.Located Token) => ∃ (others: List (Parse.Located Token)) => tokens = [first, ..others]
      ∧ startsExpression first.value.kind = True
      ∧ tail.length <= others.length :=
  match tail with
    | [] =>
      match spelledStart InBrackets head tokens shaped.left spelled with
        | (first, others, split, startKind) => (first, others, split, startKind, (arithmetic []))
    | [next, ..more] =>
      match spelled, shaped with
        | (valueTokens, commaToken, laterTokens, split, isComma, spelledValue, spelledLater), (shapedValue,
            shapedLater) =>
          let valueStart := spelledStart InBrackets head valueTokens shapedValue spelledValue
          let laterStart := itemsStart next more laterTokens shapedLater spelledLater
          match valueStart, laterStart with
            | (first, others, valueSplit, startKind), (second, rest, laterSplit, laterKind, short) => (
              first,
              (others ++ [commaToken, ..laterTokens]),
              (rewrite split, valueSplit),
              startKind,
              (rewrite laterSplit then arithmetic [short, List.lengthAppend others [commaToken, second, ..rest]])
            )

--| `items` reads the items between brackets and the closing bracket, and
--| gives the bracket's comments.
theorem runsItems ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat)
    (nested: ReadsNested self bound)
    (listed: List Expr) (tokens after: List (Parse.Located Token)) (close: Parse.Located Token) (closer: Punctuation)
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True)
    (shaped: ShapedItems listed)
    (spelled: SpelledItems listed tokens)
    (small: tokens.length < bound):
    Parse.Runs (() => items self closer) (tokens ++ [close]) after (listed, False, Layout.comments InBrackets close) :=
  let closed := Layout.comments InBrackets close
  match listed with
    | [] =>
      rewrite spelled then
        Parse.runsBind
          (() => signInBrackets "'${closer.spelling}'" closer)
          (found =>
            match found with
              | Some close => ([], False, close)
              | None =>
                let (found, trailingComma) := itemsFrom (Parse.mark().left) self closer []
                let close := sign InBrackets "'${closer.spelling}'" closer
                (found, trailingComma, close))
          [close]
          []
          [close]
          after
          (Some closed)
          ([], False, closed)
          byComputing
          (runsSignThere "'${closer.spelling}'" closer close after (bracketThere close closer closes bracket))
          (Parse.runsPure ([], False, closed) after)
    | [head, ..tail] =>
      match itemsStart head tail tokens shaped spelled with
        | (first, others, split, startKind, short) =>
          let absent: signAhead closer ((tokens ++ [close]) ++ after) = False :=
            rewrite split then startNoBracket first.value.kind closer startKind bracket
          let size: tokens.length = Succ others.length := rewrite split
          Parse.runsBind
            (() => signInBrackets "'${closer.spelling}'" closer)
            (found =>
              match found with
                | Some close => ([], False, close)
                | None =>
                  let (found, trailingComma) := itemsFrom (Parse.mark().left) self closer []
                  let close := sign InBrackets "'${closer.spelling}'" closer
                  (found, trailingComma, close))
            []
            (tokens ++ [close])
            (tokens ++ [close])
            after
            None
            ([head, ..tail], False, closed)
            byComputing
            (runsSignAbsent "'${closer.spelling}'" closer ((tokens ++ [close]) ++ after) absent)
            (state starts honest =>
              let lengths: state.at.rest.length = (tokens ++ [close]).length + after.length :=
                rewrite starts then List.lengthAppend (tokens ++ [close]) after
              Parse.runsFromMark state
                (at =>
                  let (found, trailingComma) := itemsFrom at.left self closer []
                  let close := sign InBrackets "'${closer.spelling}'" closer
                  (found, trailingComma, close))
                (tokens ++ [close])
                after
                ([head, ..tail], False, closed)
                (Parse.runsFromBind state
                  (() => itemsFrom state.at.left self closer [])
                  (read =>
                    let (found, trailingComma) := read
                    let close := sign InBrackets "'${closer.spelling}'" closer
                    (found, trailingComma, close))
                  tokens
                  [close]
                  (tokens ++ [close])
                  after
                  ([head, ..tail], False)
                  ([head, ..tail], False, closed)
                  byComputing
                  (runsItemsFrom self bound nested head tail [] state.at.left tokens after close closer closes bracket
                      shaped spelled small
                      (arithmetic [short, size, honest, lengths, List.lengthAppend tokens [close]]))
                  (middle atRest honest1 offset =>
                    Parse.runsMap
                      (() => sign InBrackets "'${closer.spelling}'" closer)
                      (close => ([head, ..tail], False, close))
                      [close]
                      after
                      closed
                      (runsSign InBrackets "'${closer.spelling}'" closer close after closes byComputing)
                      middle))
                starts
                honest)

theorem runsAtomList ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (open: Parse.Located Token)
    (itemTokens rest: List (Parse.Located Token)) (close: Parse.Located Token) (listed: List Expr) (trailingComma: Bool)
    (opens: open.value.kind = Sign OpenSquare)
    (allowed: layout.allows open = True)
    (runsInside: Parse.Runs (() => items self CloseSquare) (itemTokens ++ [close]) rest (
      listed,
      trailingComma,
      Layout.comments InBrackets close
    )):
    Parse.Runs
      (() => atom self layout)
      [open, ..itemTokens ++ [close]]
      rest
      (ListLiteral
        (layout.comments open)
        listed
        trailingComma
        ((Layout.comments InBrackets close).closing (itemsEndWithComment (layout.comments open) listed))) :=
  state starts honest =>
    let opened := layout.comments open
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let (found, trailingComma, close) := items self CloseSquare
          ListLiteral opened found trailingComma (close.closing (itemsEndWithComment opened found)))
        [open]
        (itemTokens ++ [close])
        [open, ..itemTokens ++ [close]]
        rest
        ()
        (ListLiteral opened listed trailingComma
          ((Layout.comments InBrackets close).closing (itemsEndWithComment opened listed)))
        byComputing
        (runsSkip open ((itemTokens ++ [close]) ++ rest))
        (Parse.runsMap
          (() => items self CloseSquare)
          (read =>
            let (found, trailingComma, close) := read
            ListLiteral opened found trailingComma (close.closing (itemsEndWithComment opened found)))
          (itemTokens ++ [close])
          rest
          (listed, trailingComma, Layout.comments InBrackets close)
          runsInside)
    match core state starts honest with | (m, ran, after) => (m, (rewrite starts, allowed, opens then ran), after)

--| A round of `suffixesFrom` that reads a call: `(`, the arguments, `)`,
--| and on from the target with the call.
theorem runsSuffixesCall ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (open: Parse.Located Token) (argumentTokens: List (Parse.Located Token)) (close: Parse.Located Token)
    (after rest: List (Parse.Located Token)) (arguments: List Expr) (trailingComma: Bool) (value: Expr)
    (opens: open.value.kind = Sign OpenParen)
    (allowed: layout.allows open = True)
    (runsInside: Parse.Runs (() => items self CloseParen) (argumentTokens ++ [close]) (after ++ rest) (
      arguments,
      trailingComma,
      Layout.comments InBrackets close
    ))
    (runsMore: Parse.Runs
      (() =>
        suffixesFrom more self layout
          (Call target (layout.comments open) arguments trailingComma (Layout.comments InBrackets close)))
      after
      rest
      value)
    (settled: settledCloser (itemsEndWithComment (layout.comments open) arguments) (Layout.comments InBrackets close)
      = True):
    Parse.Runs
      (() => suffixesFrom (Succ more) self layout target)
      ([open, ..argumentTokens ++ [close]] ++ after)
      rest
      value :=
  state starts honest =>
    let opened := layout.comments open
    let read :=
      Call target opened arguments trailingComma
        ((Layout.comments InBrackets close).closing (itemsEndWithComment opened arguments))
    let core :=
      Parse.runsBind
        (() =>
          Parse.optional (() =>
            skip()
            let (arguments, trailingComma, close) := items self CloseParen
            Call target opened arguments trailingComma (close.closing (itemsEndWithComment opened arguments))))
        (suffixesAfter more self layout target)
        [open, ..argumentTokens ++ [close]]
        after
        ([open, ..argumentTokens ++ [close]] ++ after)
        rest
        (Some read)
        value
        byComputing
        (Parse.runsOptional
          (() =>
            skip()
            let (arguments, trailingComma, close) := items self CloseParen
            Call target opened arguments trailingComma (close.closing (itemsEndWithComment opened arguments)))
          [open, ..argumentTokens ++ [close]]
          (after ++ rest)
          read
          (Parse.runsBind
            (() => skip())
            (skipped =>
              let (arguments, trailingComma, close) := items self CloseParen
              Call target opened arguments trailingComma (close.closing (itemsEndWithComment opened arguments)))
            [open]
            (argumentTokens ++ [close])
            [open, ..argumentTokens ++ [close]]
            (after ++ rest)
            ()
            read
            byComputing
            (runsSkip open ((argumentTokens ++ [close]) ++ (after ++ rest)))
            (Parse.runsMap
              (() => items self CloseParen)
              (found =>
                let (arguments, trailingComma, close) := found
                Call target opened arguments trailingComma (close.closing (itemsEndWithComment opened arguments)))
              (argumentTokens ++ [close])
              (after ++ rest)
              (arguments, trailingComma, Layout.comments InBrackets close)
              runsInside)))
        (rewrite closingSame
              (Layout.comments InBrackets close)
              (itemsEndWithComment (layout.comments open) arguments)
              settled then
          runsMore)
    match core state starts honest with | (m, ran, others) => (m, (rewrite starts, allowed, opens then ran), others)

-- Where no expression starts: at a keyword other than `if`. What ends a
-- block whose next line starts with `then` or `else`.

--| What the expression parser is assumed to do, for the nested
--| expressions of one being read, where a keyword other than `if` comes
--| next: fail, so that what tried it can go on without it.
def DeclinesNested (self: Layout → {Parse (Parse.Located Token)} Expr): Prop :=
  ∀ (layout: Layout) (token: Parse.Located Token) (later: List
    (Parse.Located Token)) (keyword: Keyword) => token.value.kind = Reserved keyword
    → keyword ≠ IfKeyword
    → Parse.Declines (() => self layout) [token, ..later]

theorem notMinusAtReserved ∀ (layout: Layout) (token: Parse.Located Token) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    isMinus layout token = False :=
  match allowed: layout.allows token with
    | True => rewrite reserved
    | False => byComputing

theorem notIfAtReserved ∀ (layout: Layout) (token: Parse.Located Token) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword)
    (notIf: keyword ≠ IfKeyword):
    isIf layout token = False :=
  match allowed: layout.allows token with
    | False => byComputing
    | True =>
      rewrite reserved then
        match keyword, notIf with
          | IfKeyword, notIf => (notIf byComputing).impossible
          | FnKeyword, notIf => byComputing
          | LetKeyword, notIf => byComputing
          | ThenKeyword, notIf => byComputing
          | ElseKeyword, notIf => byComputing
          | TakesKeyword, notIf => byComputing

--| No atom starts with a keyword.
theorem atomDeclines ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (token: Parse.Located Token)
    (later: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    Parse.Declines (() => atom self layout) [token, ..later] :=
  state starts honest =>
    let step: Parse.runFrom state (() => (Parse.optional (() => atom self layout), Parse.mark()))
      = Parse.runFrom state (() => (Parse.optional (() => (Parse.expected "an expression": Expr)), Parse.mark())) :=
      rewrite starts then
        match allowed: layout.allows token with
          | True => rewrite reserved
          | False => byComputing
    Eq.trans step (Parse.declinesExpected "an expression" [token, ..later] state starts honest)

theorem postfixDeclines ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (later: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    Parse.Declines (() => postfix self layout) [token, ..later] :=
  Parse.declinesNote
    (Parse.Problem.Expected "an expression")
    (noted =>
      let first := atom self layout
      suffixesFrom (Parse.mark().left + 1) self layout first)
    [token, ..later]
    (Parse.declinesBind
      (() => atom self layout)
      (first => suffixesFrom (Parse.mark().left + 1) self layout first)
      [token, ..later]
      (atomDeclines self layout token later keyword reserved))

theorem negationsDecline ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (later: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    Parse.Declines (() => negationsFrom fuel self layout) [token, ..later] :=
  state starts honest =>
    let step: Parse.runFrom state (() => (Parse.optional (() => negationsFrom fuel self layout), Parse.mark()))
      = Parse.runFrom state (() => (Parse.optional (() => postfix self layout), Parse.mark())) :=
      match fuel with
        | Zero => byComputing
        | Succ more => rewrite starts, notMinusAtReserved layout token keyword reserved
    Eq.trans step (postfixDeclines self layout token later keyword reserved state starts honest)

theorem chainRuleStops ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (state: Parse.State (Parse.Located Token))
    (noIf: ifAhead layout state.at.rest = False):
    Parse.runFrom state (() => (Parse.optional (() => expressionRule self layout), Parse.mark()))
      = Parse.runFrom state (() =>
        (
          Parse.optional (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout)),
          Parse.mark()
        )) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => byComputing
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite noIf

--| No expression starts with a keyword other than `if`, whatever reads
--| the expressions nested in it.
theorem expressionRuleDeclines ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (later: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword)
    (notIf: keyword ≠ IfKeyword):
    Parse.Declines (() => expressionRule self layout) [token, ..later] :=
  state starts honest =>
    Eq.trans
      (chainRuleStops self layout state (rewrite starts then notIfAtReserved layout token keyword reserved notIf))
      (Parse.declinesOperators "an operator"
        (operatorLevels layout)
        (() => operand self layout)
        [token, ..later]
        (inner begins fair =>
          negationsDecline (inner.at.left + 1) self layout token later keyword reserved inner begins fair)
        state
        starts
        honest)

--| The expression parser, and every level of the recursion in it, declines
--| at a keyword other than `if`, whatever reads the expressions nested in it.
theorem expressionDeclines: DeclinesNested expression := layout token later keyword reserved notIf =>
  Parse.declinesRecursiveWith expressionRule layout [token, ..later] (self =>
    expressionRuleDeclines self layout token later keyword reserved notIf)

-- An instance of `runsExpression`: the six tokens of `f(a) + b`.

def exampleToken (kind: Kind) (offset: Nat): Parse.Located Token :=
  { value = { kind, startsLine = False, column = offset, above = [], trailing = None }, offset, length = 1 }

def exampleTokens: List (Parse.Located Token) := [
  exampleToken (Name "f") 0,
  exampleToken (Sign OpenParen) 1,
  exampleToken (Name "a") 2,
  exampleToken (Sign CloseParen) 3,
  exampleToken (Op Plus) 5,
  exampleToken (Name "b") 7
]

def exampleCall: Expr := Call (Var "f" Comments.none) Comments.none [Var "a" Comments.none] False Comments.none

def exampleExpr: Expr := Binary Plus Comments.none exampleCall (Var "b" Comments.none)

theorem runsExpressionExample: Parse.run exampleTokens (() => expression InBrackets) = Ok exampleExpr :=
  let f := exampleToken (Name "f") 0
  let open := exampleToken (Sign OpenParen) 1
  let a := exampleToken (Name "a") 2
  let close := exampleToken (Sign CloseParen) 3
  let plus := exampleToken (Op Plus) 5
  let b := exampleToken (Name "b") 7
  let spelledCall: Spelled InBrackets exampleCall [f, open, a, close] := (
    [f],
    open,
    [a],
    close,
    byComputing,
    byComputing,
    byComputing,
    byComputing,
    ((f, byComputing, byComputing, byComputing, byComputing)),
    ((a, byComputing, byComputing, byComputing, byComputing)),
    byComputing,
    byComputing,
    byComputing
  )
  Parse.runsRun
    (() => expression InBrackets)
    exampleTokens
    exampleExpr
    (runsExpression InBrackets exampleExpr exampleTokens []
      ((
        (arithmetic []),
        (arithmetic []),
        byComputing,
        byComputing,
        ((byComputing, byComputing, ((byComputing, byComputing)), byComputing)),
        byComputing
      ))
      ((
        [f, open, a, close],
        plus,
        [b],
        byComputing,
        byComputing,
        byComputing,
        spelledCall,
        ((b, byComputing, byComputing, byComputing, byComputing)),
        byComputing
      ))
      ((((byComputing, byComputing)), byComputing)))
