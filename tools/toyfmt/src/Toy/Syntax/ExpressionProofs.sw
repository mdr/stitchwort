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
    (Parse.runsNext (token => True) token rest rfl)

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
    (rewrite allowed, signed in
      match wanted with
        | OpenParen => rfl
        | CloseParen => rfl
        | OpenSquare => rfl
        | CloseSquare => rfl
        | Comma => rfl
        | Dot => rfl
        | Defines => rfl)

theorem runsName ∀ (layout: Layout) (token: Parse.Located Token) (text: Text) (rest: List (Parse.Located Token))
    (named: token.value.kind = Name text)
    (allowed: layout.allows token = True):
    Parse.Runs (() => name layout) [token] rest (text, layout.comments token) :=
  Parse.runsOne "a name"
    (selectWithComments layout nameOf)
    token
    (text, layout.comments token)
    rest
    (rewrite allowed, named in rfl)

theorem runsAtomNumber ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (digits: Text) (rest: List (Parse.Located Token))
    (numbered: token.value.kind = Number digits)
    (allowed: layout.allows token = True):
    Parse.Runs (() => atom self layout) [token] rest (NumberLiteral digits (layout.comments token)) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts in rfl
    Witness
      (state.advance rest 1).at
      (Both (rewrite starts, allowed, numbered, starts in rfl) (Both rfl (Both (omega [honest, lengths]) rfl)))

theorem runsAtomString ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (written: Text) (rest: List (Parse.Located Token))
    (quoted: token.value.kind = Str written)
    (allowed: layout.allows token = True):
    Parse.Runs (() => atom self layout) [token] rest (StringLiteral written (layout.comments token)) :=
  state starts honest =>
    let lengths: state.at.rest.length = rest.length + 1 := rewrite starts in rfl
    Witness
      (state.advance rest 1).at
      (Both (rewrite starts, allowed, quoted, starts in rfl) (Both rfl (Both (omega [honest, lengths]) rfl)))

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
      (Bracketed (layout.comments open) inner (Layout.comments InBrackets close)) :=
  state starts honest =>
    let opened := layout.comments open
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let inner := self InBrackets
          let close := sign InBrackets "')'" CloseParen
          Bracketed opened inner close)
        [open]
        (innerTokens ++ [close])
        [open, ..innerTokens ++ [close]]
        rest
        ()
        (Bracketed opened inner (Layout.comments InBrackets close))
        rfl
        (runsSkip open ((innerTokens ++ [close]) ++ rest))
        (Parse.runsBind
          (() => self InBrackets)
          (inner =>
            let close := sign InBrackets "')'" CloseParen
            Bracketed opened inner close)
          innerTokens
          [close]
          (innerTokens ++ [close])
          rest
          inner
          (Bracketed opened inner (Layout.comments InBrackets close))
          rfl
          runsInner
          (Parse.runsMap
            (() => sign InBrackets "')'" CloseParen)
            (closed => Bracketed opened inner closed)
            [close]
            rest
            (Layout.comments InBrackets close)
            (runsSign InBrackets "')'" CloseParen close rest closes rfl)))
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, allowed, opens in ran) others)

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
        rfl
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
            rfl
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
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, dotAllowed, dotted in ran) others)

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
        rfl
        (runsSkip minus (tokens ++ rest))
        (Parse.runsMap
          (() => negationsFrom more self layout)
          (inner => Negate signed inner)
          tokens
          rest
          operand
          runsOperand)
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, allowed, isMinusSign in ran) others)

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
      rfl
      runsAtom
      (middle atRest honest offset =>
        let lengths: middle.at.rest.length = more.length + rest.length := rewrite atRest in List.lengthAppend more rest
        Parse.runsFromMark middle
          (at => suffixesFrom (at.left + 1) self layout first)
          more
          rest
          value
          (runsSuffixes (middle.at.left + 1) (omega [honest, lengths]) middle))

--| An expression that `atom` and `suffixesFrom` read: an atom with its
--| calls and fields.
def Expr.isPostfix: Expr → Bool
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ _ _ => True
  | ListLiteral _ _ _ => True
  | Call _ _ _ _ => True
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
--| and end in a statement, not a comment line (`ShapedBody`).
def Shaped: Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ inner _ => Shaped inner
  | Field target _ _ _ => target.isPostfix = True ∧ Shaped target
  | Negate _ operand => operand.isOperand = True ∧ Shaped operand
  | Binary operator _ left right =>
    operator.level ≤ left.chainLevel
      ∧ operator.level < right.chainLevel
      ∧ left.isChain = True
      ∧ right.isChain = True
      ∧ Shaped left
      ∧ Shaped right
  | ListLiteral _ items _ => ShapedItems items ∧ BareLastItem items
  | Call callee _ arguments _ =>
    callee.isPostfix = True ∧ Shaped callee ∧ ShapedItems arguments ∧ BareLastItem arguments
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

--| Each item's value is of the parser's shape.
def ShapedItems: List Item → Prop
  | [] => True
  | [{ value, .. }, ..rest] => Shaped value ∧ ShapedItems rest

--| The last item has no comma, so no comma's comments: the printer writes
--| none there.
def BareLastItem: List Item → Prop
  | [] => True
  | [last] => last.comma = Comments.none
  | [_, ..rest] => BareLastItem rest

--| `tokens` spell `expr` at `layout`: its tokens in order, each of the kind
--| the expression has there and standing where the layout allows it
--| (anywhere, inside brackets), and each token's comments in the tree
--| those the parser takes from it (`Layout.comments`). An `if`'s `else` may
--| also start a line at the statement's column, and each of its branches
--| is spelled as a body (`SpelledBody`: one expression or a block)
--| whatever comes after it that may (`After`). For the forms `Shaped`
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
  | ListLiteral opened items closed =>
    ∃ (open: Parse.Located Token) => ∃ (itemTokens: List (Parse.Located Token)) => ∃ (close: Parse.Located Token) =>
      tokens = [open, ..itemTokens ++ [close]]
        ∧ open.value.kind = Sign OpenSquare
        ∧ layout.allows open = True
        ∧ close.value.kind = Sign CloseSquare
        ∧ SpelledItems items itemTokens
        ∧ opened = layout.comments open
        ∧ closed = Layout.comments InBrackets close
  | Call callee opened arguments closed =>
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
  Both ends rfl

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
    | InBrackets, settled => rfl
    | InStatement column from, settled =>
      match rest, settled with
        | [], settled => rfl
        | [next, ..more], Inl closes => Inl closes
        | [next, ..more], Inr (Both low clear) => Inr (Both low (notAtBack next.offset front back clear))

--| `tokens` spell a body that is one expression, at `layout`: the
--| expression, not starting a line deeper than the statement (which would
--| start a block).
def SpelledInline (layout: Layout) (found: Body) (tokens: List (Parse.Located Token)): Prop := match found with
  | { statements = [{ blankBefore, line = Bare value }] } =>
    blankBefore = False ∧ blockAhead layout tokens = False ∧ Spelled layout value tokens ∧ layout.headed value = value
  | _ => False

--| `tokens` spell the items of a list or the arguments of a call, between
--| the brackets: each value, and a comma after each but the last, whose
--| comments the item holds.
def SpelledItems (items: List Item) (tokens: List (Parse.Located Token)): Prop := match items with
  | [] => tokens = []
  | [{ value, comma }] => Spelled InBrackets value tokens ∧ comma = Comments.none
  | [{ value, comma }, next, ..more] =>
    ∃ (valueTokens: List (Parse.Located Token)) => ∃ (commaToken: Parse.Located Token) =>
      ∃ (laterTokens: List (Parse.Located Token)) => tokens = valueTokens ++ [commaToken, ..laterTokens]
        ∧ commaToken.value.kind = Sign Comma
        ∧ Spelled InBrackets value valueTokens
        ∧ comma = Layout.comments InBrackets commaToken
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
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          rewrite split, kind, allowed in Both rfl rfl
    | NumberLiteral digits comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          rewrite split, kind, allowed in Both rfl rfl
    | StringLiteral written comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          rewrite split, kind, allowed in Both rfl rfl
    | Bracketed opened inner closed =>
      match spelled with
        | Witness open (Witness innerTokens (Witness close (Both split (Both opens (Both allowed others))))) =>
          rewrite split, opens, allowed in Both rfl rfl
    | Field target dotComments name nameComments =>
      match spelled with
        | Witness targetTokens
            (Witness dot
              (Witness named
                (Both split
                  (Both dotted
                    (Both dotAllowed
                      (Both isName (Both nameAllowed (Both spelledTarget (Both dotCommented nameCommented))))))))) =>
          rewrite split, List.appendAssoc targetTokens [dot, named] rest in
            postfixStart layout target targetTokens [dot, named, ..rest] shaped.left shaped.right spelledTarget
    | ListLiteral opened listed closed =>
      match spelled with
        | Witness open (Witness itemTokens (Witness close (Both split (Both opens (Both allowed others))))) =>
          rewrite split, opens, allowed in Both rfl rfl
    | Call callee opened arguments closed =>
      match spelled with
        | Witness calleeTokens
            (Witness open
              (Witness argumentTokens
                (Witness close
                  (Both split
                    (Both opens
                      (Both allowed
                        (Both closes
                          (Both spelledCallee (Both spelledArguments (Both openCommented closeCommented)))))))))) =>
          rewrite split, List.appendAssoc calleeTokens [open, ..argumentTokens ++ [close]] rest in
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
    | Zero => rfl
    | Succ more =>
      rewrite starts in
        match input with
          | [] => rfl
          | [token, ..later] => rewrite noMinus in rfl

--| With no `-` next, `negationsFrom` reads a postfix expression.
theorem runsNegationsEnd ∀ (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (tokens rest: List (Parse.Located Token)) (value: Expr)
    (noMinus: minusAhead layout (tokens ++ rest) = False)
    (runsPostfix: Parse.Runs (() => postfix self layout) tokens rest value):
    Parse.Runs (() => negationsFrom fuel self layout) tokens rest value :=
  state starts honest =>
    match runsPostfix state starts honest with
      | Witness m (Both ran others) =>
        Witness m (Both (Eq.trans (negationsEndRun fuel self layout (tokens ++ rest) noMinus state starts) ran) others)

theorem operatorOfSign ∀ (layout: Layout) (level: Nat) (token: Parse.Located Token) (punctuation: Punctuation)
    (signed: token.value.kind = Sign punctuation):
    operatorOf layout level token = None :=
  rewrite signed in rfl

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
      operatorOfSign layout 6 token punctuation signed in
    rfl

theorem endsAtClose ∀ (close: Parse.Located Token) (rest: List (Parse.Located Token))
    (closes: close.value.kind = Sign CloseParen):
    EndsExpression InBrackets [close, ..rest] :=
  Both (rewrite closes in rfl) (noOperatorAtSign InBrackets 0 close CloseParen rest closes)

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
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          rewrite commented at continues in
            rewrite split in
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
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          rewrite commented at continues in
            rewrite split in
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
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          rewrite commented at continues in
            rewrite split in
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
        | Witness open
            (Witness innerTokens
              (Witness close
                (Both split
                  (Both opens
                    (Both allowed (Both closes (Both spelledInner (Both openCommented closeCommented)))))))) =>
          let size: tokens.length = (innerTokens ++ [close]).length + 1 := rewrite split in rfl
          let sizes: (innerTokens ++ [close]).length = innerTokens.length + 1 := List.lengthAppend innerTokens [close]
          rewrite openCommented, closeCommented at continues in
            rewrite split in
              runsAtomThenSuffixes self layout
                [open, ..innerTokens ++ [close]]
                more
                rest
                (Bracketed (layout.comments open) inner (Layout.comments InBrackets close))
                value
                (runsAtomBracketed self layout open close innerTokens
                  (more ++ rest)
                  inner
                  opens
                  allowed
                  closes
                  (nested InBrackets inner innerTokens
                    [close, ..more ++ rest]
                    shaped
                    spelledInner
                    (afterBrackets innerTokens [close, ..more ++ rest] (endsAtClose close (more ++ rest) closes))
                    (omega [small, size, sizes])))
                continues
    | Field target dotComments name nameComments =>
      match spelled with
        | Witness targetTokens
            (Witness dot
              (Witness named
                (Both split
                  (Both dotted
                    (Both dotAllowed
                      (Both isName (Both nameAllowed (Both spelledTarget (Both dotCommented nameCommented))))))))) =>
          let size: tokens.length = targetTokens.length + 2 :=
            rewrite split in List.lengthAppend targetTokens [dot, named]
          rewrite dotCommented, nameCommented at continues in
            rewrite split, List.appendAssoc targetTokens [dot, named] more in
              runsPostfixPrefix self layout bound nested target targetTokens
                [dot, named, ..more]
                rest
                value
                shaped.left
                shaped.right
                spelledTarget
                (omega [small, size])
                (fuel enough =>
                  match fuel with
                    | Succ less =>
                      runsSuffixesField less self layout target dot named name more rest value dotted dotAllowed isName
                          nameAllowed
                          (continues less (omega [enough])))
    | ListLiteral opened listed closed =>
      match spelled with
        | Witness open
            (Witness itemTokens
              (Witness close
                (Both split
                  (Both opens
                    (Both allowed (Both closes (Both spelledItems (Both openCommented closeCommented)))))))) =>
          let size: tokens.length = (itemTokens ++ [close]).length + 1 := rewrite split in rfl
          let sizes: (itemTokens ++ [close]).length = itemTokens.length + 1 := List.lengthAppend itemTokens [close]
          rewrite openCommented, closeCommented at continues in
            rewrite split in
              runsAtomThenSuffixes self layout
                [open, ..itemTokens ++ [close]]
                more
                rest
                (ListLiteral (layout.comments open) listed (Layout.comments InBrackets close))
                value
                (runsAtomList self layout open itemTokens
                  (more ++ rest)
                  close
                  listed
                  opens
                  allowed
                  (runsItems self bound nested listed itemTokens
                    (more ++ rest)
                    close
                    CloseSquare
                    closes
                    rfl
                    shaped.left
                    spelledItems
                    (omega [small, size, sizes])))
                continues
    | Call callee opened arguments closed =>
      match spelled with
        | Witness calleeTokens
            (Witness open
              (Witness argumentTokens
                (Witness close
                  (Both split
                    (Both opens
                      (Both allowed
                        (Both closes
                          (Both spelledCallee (Both spelledArguments (Both openCommented closeCommented)))))))))) =>
          let size: tokens.length = calleeTokens.length + ((argumentTokens ++ [close]).length + 1) :=
            rewrite split in List.lengthAppend calleeTokens [open, ..argumentTokens ++ [close]]
          let sizes: (argumentTokens ++ [close]).length = argumentTokens.length + 1 :=
            List.lengthAppend argumentTokens [close]
          rewrite openCommented, closeCommented at continues in
            rewrite split, List.appendAssoc calleeTokens [open, ..argumentTokens ++ [close]] more in
              runsPostfixPrefix self layout bound nested callee calleeTokens
                ([open, ..argumentTokens ++ [close]] ++ more)
                rest
                value
                shaped.left
                shaped.right.left
                spelledCallee
                (omega [small, size])
                (fuel enough =>
                  match fuel with
                    | Succ less =>
                      runsSuffixesCall less self layout callee open argumentTokens close more rest arguments value opens
                          allowed
                          (runsItems self bound nested arguments argumentTokens
                            (more ++ rest)
                            close
                            CloseParen
                            closes
                            rfl
                            shaped.right.right.left
                            spelledArguments
                            (omega [small, size, sizes]))
                          (continues less (omega [enough, List.lengthAppend (argumentTokens ++ [close]) more])))

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
      rfl
      (Parse.runsNote (Parse.Problem.Expected "an expression") (tokens ++ rest))
      (rewrite <- List.appendNil tokens in
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
        | Witness minus
            (Witness operandTokens (Both split (Both kind (Both allowed (Both spelledInner minusCommented))))), Succ
              more =>
          let size: tokens.length = operandTokens.length + 1 := rewrite split in rfl
          rewrite split, minusCommented in
            runsNegation more self layout minus operandTokens rest inner kind allowed
              (runsNegations self layout bound nested inner more operandTokens rest shaped.left shaped.right
                  spelledInner ends
                  (omega [small, size])
                  (omega [enough, size]))
    | Var name comments =>
      runsNegationsPostfix self layout bound nested (Var name comments) fuel tokens rest rfl shaped spelled ends small
    | NumberLiteral digits comments =>
      runsNegationsPostfix self layout bound nested
        (NumberLiteral digits comments)
        fuel
        tokens
        rest
        rfl
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
        rfl
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
        rfl
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
        rfl
        shaped
        spelled
        ends
        small
    | ListLiteral opened listed closed =>
      runsNegationsPostfix self layout bound nested
        (ListLiteral opened listed closed)
        fuel
        tokens
        rest
        rfl
        shaped
        spelled
        ends
        small
    | Call callee opened arguments closed =>
      runsNegationsPostfix self layout bound nested
        (Call callee opened arguments closed)
        fuel
        tokens
        rest
        rfl
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
    let lengths: state.at.rest.length = tokens.length + rest.length := rewrite starts in List.lengthAppend tokens rest
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
        (omega [honest, lengths])
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
  rewrite kind, allowed in
    match same: operator.level == level with
      | True => rfl
      | False => rfl

theorem levelRange ∀ (operator: Operator): 1 <= operator.level ∧ operator.level <= 6 := match operator with
  | Or => Both (omega []) (omega [])
  | And => Both (omega []) (omega [])
  | EqualTo => Both (omega []) (omega [])
  | NotEqual => Both (omega []) (omega [])
  | LessThan => Both (omega []) (omega [])
  | LessEqual => Both (omega []) (omega [])
  | Append => Both (omega []) (omega [])
  | Plus => Both (omega []) (omega [])
  | Minus => Both (omega []) (omega [])
  | Times => Both (omega []) (omega [])
  | Divide => Both (omega []) (omega [])
  | Remainder => Both (omega []) (omega [])

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
    | Or => rewrite at1 in rfl
    | And => rewrite at1, at2 in rfl
    | EqualTo => rewrite at1, at2, at3 in rfl
    | NotEqual => rewrite at1, at2, at3 in rfl
    | LessThan => rewrite at1, at2, at3 in rfl
    | LessEqual => rewrite at1, at2, at3 in rfl
    | Append => rewrite at1, at2, at3, at4 in rfl
    | Plus => rewrite at1, at2, at3, at4, at5 in rfl
    | Minus => rewrite at1, at2, at3, at4, at5 in rfl
    | Times => rewrite at1, at2, at3, at4, at5, at6 in rfl
    | Divide => rewrite at1, at2, at3, at4, at5, at6 in rfl
    | Remainder => rewrite at1, at2, at3, at4, at5, at6 in rfl

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
  Witness
    (Operand tokens expr)
    (Both rfl
      (Both rfl
        (Both rfl
          (Both
            (runsOperand self layout bound nested expr tokens rest isOperand shaped spelled ends small)
            (Both (Eq.sym level) (below fits under => under))))))

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
        | Both leftLevel
            (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))), Witness leftTokens
            (Witness sign
              (Witness rightTokens
                (Both split (Both kind (Both allowed (Both spelledLeft (Both spelledRight signCommented))))))) =>
          let size: tokens.length = leftTokens.length + (rightTokens.length + 1) :=
            rewrite split in List.lengthAppend leftTokens [sign, ..rightTokens]
          let signEnds: endsSuffixes (suffixKind layout [sign, ..rightTokens ++ rest]) = True :=
            rewrite allowed, kind in rfl
          let range := levelRange operator
          let leftResult :=
            chainTree self layout bound nested left leftTokens
              [sign, ..rightTokens ++ rest]
              leftChain
              shapedLeft
              spelledLeft
              signEnds
              (omega [small, size])
          let rightResult :=
            chainTree self layout bound nested right rightTokens rest rightChain shapedRight spelledRight ends
              (omega [small, size])
          match leftResult, rightResult with
            | Witness leftTree
                (Both leftReads
                  (Both leftValue (Both leftFormed (Both leftRuns (Both leftTop leftBound))))), Witness rightTree
                (Both rightReads (Both rightValue (Both rightFormed (Both rightRuns (Both rightTop rightBound))))) =>
              Witness
                (Joined sign
                  (operator.level - 1)
                  LeftAssociative
                  (Binary operator (layout.comments sign))
                  leftTree
                  rightTree)
                (Both
                  (rewrite leftReads, rightReads, split in rfl)
                  (Both
                    (rewrite leftValue, rightValue, signCommented in rfl)
                    (Both
                      (Both
                        (operatorFound layout sign operator kind allowed)
                        (Both
                          (omega [range.right, range.left])
                          (Both
                            (leftBound
                              (operator.level - 1)
                              (omega [leftLevel, range.left])
                              (omega [range.right, range.left]))
                            (Both (omega [rightLevel, rightTop, range.left]) (Both leftFormed rightFormed)))))
                      (Both
                        (Both (rewrite rightReads in leftRuns) rightRuns)
                        (Both (omega [range.left]) (below fits under => omega [fits, range.left]))))))
    | Negate minusComments inner =>
      chainTreeOperand self layout bound nested
        (Negate minusComments inner)
        tokens
        rest
        rfl
        rfl
        shaped
        spelled
        ends
        small
    | Var name comments =>
      chainTreeOperand self layout bound nested (Var name comments) tokens rest rfl rfl shaped spelled ends small
    | NumberLiteral digits comments =>
      chainTreeOperand self layout bound nested
        (NumberLiteral digits comments)
        tokens
        rest
        rfl
        rfl
        shaped
        spelled
        ends
        small
    | StringLiteral written comments =>
      chainTreeOperand self layout bound nested
        (StringLiteral written comments)
        tokens
        rest
        rfl
        rfl
        shaped
        spelled
        ends
        small
    | Bracketed opened inner closed =>
      chainTreeOperand self layout bound nested
        (Bracketed opened inner closed)
        tokens
        rest
        rfl
        rfl
        shaped
        spelled
        ends
        small
    | Field target dotComments name nameComments =>
      chainTreeOperand self layout bound nested
        (Field target dotComments name nameComments)
        tokens
        rest
        rfl
        rfl
        shaped
        spelled
        ends
        small
    | ListLiteral opened listed closed =>
      chainTreeOperand self layout bound nested
        (ListLiteral opened listed closed)
        tokens
        rest
        rfl
        rfl
        shaped
        spelled
        ends
        small
    | Call callee opened arguments closed =>
      chainTreeOperand self layout bound nested
        (Call callee opened arguments closed)
        tokens
        rest
        rfl
        rfl
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
        | Both leftLevel
            (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))), Witness leftTokens
            (Witness sign
              (Witness rightTokens
                (Both split (Both kind (Both allowed (Both spelledLeft (Both spelledRight signCommented))))))) =>
          rewrite split, List.appendAssoc leftTokens [sign, ..rightTokens] rest in
            chainStart layout left leftTokens [sign, ..rightTokens ++ rest] leftChain shapedLeft spelledLeft
    | Negate minusComments inner =>
      match spelled with
        | Witness minus
            (Witness operandTokens (Both split (Both kind (Both allowed (Both spelledInner minusCommented))))) =>
          rewrite split, kind, allowed in rfl
    | Var name comments => (postfixStart layout (Var name comments) tokens rest rfl shaped spelled).right
    | NumberLiteral digits comments =>
      (postfixStart layout (NumberLiteral digits comments) tokens rest rfl shaped spelled).right
    | StringLiteral written comments =>
      (postfixStart layout (StringLiteral written comments) tokens rest rfl shaped spelled).right
    | Bracketed opened inner closed =>
      (postfixStart layout (Bracketed opened inner closed) tokens rest rfl shaped spelled).right
    | Field target dotComments name nameComments =>
      (postfixStart layout (Field target dotComments name nameComments) tokens rest rfl shaped spelled).right
    | ListLiteral opened listed closed =>
      (postfixStart layout (ListLiteral opened listed closed) tokens rest rfl shaped spelled).right
    | Call callee opened arguments closed =>
      (postfixStart layout (Call callee opened arguments closed) tokens rest rfl shaped spelled).right

theorem chainRuleRun ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (layout: Layout) (state: Parse.State (Parse.Located Token))
    (noIf: ifAhead layout state.at.rest = False):
    Parse.runFrom state (() => (expressionRule self layout, Parse.mark()))
      = Parse.runFrom state (() =>
        (Parse.operators "an operator" (operatorLevels layout) (() => operand self layout), Parse.mark())) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite noIf in rfl

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
    | Witness tree (Both reads (Both value (Both formed (Both runsEach others)))) =>
      let runs: Parse.Runs
        (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout))
        tokens
        rest
        expr :=
        rewrite <- reads, <- value in
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
          | Witness m (Both ran after) =>
            Witness m
              (Both
                (Eq.trans
                  (chainRuleRun self layout state
                    (rewrite starts in chainStart layout expr tokens rest chain shaped spelled))
                  ran)
                after)

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
      runsChainRule self layout bound nested (Var name comments) tokens rest rfl shaped spelled after.left small
    | NumberLiteral digits comments, shaped, spelled =>
      runsChainRule self layout bound nested
        (NumberLiteral digits comments)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small
    | StringLiteral written comments, shaped, spelled =>
      runsChainRule self layout bound nested
        (StringLiteral written comments)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small
    | Bracketed opened inner closed, shaped, spelled =>
      runsChainRule self layout bound nested
        (Bracketed opened inner closed)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small
    | Field target dotComments name nameComments, shaped, spelled =>
      runsChainRule self layout bound nested
        (Field target dotComments name nameComments)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small
    | Negate minusComments operand, shaped, spelled =>
      runsChainRule self layout bound nested
        (Negate minusComments operand)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small
    | Binary operator signComments left right, shaped, spelled =>
      runsChainRule self layout bound nested
        (Binary operator signComments left right)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small
    | ListLiteral opened listed closed, shaped, spelled =>
      runsChainRule self layout bound nested
        (ListLiteral opened listed closed)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small
    | Call callee opened arguments closed, shaped, spelled =>
      runsChainRule self layout bound nested
        (Call callee opened arguments closed)
        tokens
        rest
        rfl
        shaped
        spelled
        after.left
        small

--| `expression` with its fuel: each level reads with the level below,
--| which reads every shorter expression and, not being the innermost,
--| declines at a keyword.
theorem runsExpressionFuel ∀ (fuel: Nat) (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (after: After layout tokens rest)
    (small: tokens.length < fuel):
    Parse.Runs (() => Parse.recursiveWithFuel fuel expressionRule layout) tokens rest expr :=
  match fuel, small with
    | Succ Zero, small =>
      match spelledStart layout expr tokens shaped spelled with
        | Witness first (Witness others (Both split _)) =>
          let size: tokens.length = Succ others.length := rewrite split in rfl
          Void.exfalso (omega [size, small])
    | Succ (Succ more), small => state starts honest =>
      runsExpressionRule
        (inner => Parse.recursiveWithFuel (Succ more) expressionRule inner)
        layout
        (Succ more)
        (nestedLayout nestedExpr nestedTokens nestedRest nestedShaped nestedSpelled nestedAfter shorter =>
          runsExpressionFuel
            (Succ more)
            nestedLayout
            nestedExpr
            nestedTokens
            nestedRest
            nestedShaped
            nestedSpelled
            nestedAfter
            shorter)
        (fuelDeclines more)
        expr
        tokens
        rest
        shaped
        spelled
        after
        (omega [small])
        state
        starts
        honest

--| The parser reads back what spells an expression: on tokens that spell
--| `expr` at `layout` (`Spelled`), for an `expr` of the parser's shape
--| (`Shaped`), followed by what may follow it (`After`), `expression
--| layout` reads exactly those tokens and gives `expr`.
theorem runsExpression ∀ (layout: Layout) (expr: Expr) (tokens rest: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (after: After layout tokens rest):
    Parse.Runs (() => expression layout) tokens rest expr :=
  state starts honest =>
    let lengths: state.at.rest.length = tokens.length + rest.length := rewrite starts in List.lengthAppend tokens rest
    Parse.runsFromMark state
      (at => Parse.recursiveWithFuel (at.left + 1) expressionRule layout)
      tokens
      rest
      expr
      (runsExpressionFuel
        (state.at.left + 1)
        layout
        expr
        tokens
        rest
        shaped
        spelled
        after
        (omega [lengths, honest])
        state)
      starts
      honest

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
        | Witness ifToken
            (Witness conditionTokens
              (Witness thenToken
                (Witness trueTokens (Witness elseToken (Witness falseTokens (Both split (Both isIfToken others))))))) =>
          Witness ifToken
            (Witness
              (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
              (Both split (rewrite isIfToken in rfl)))
    | Var name comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          Witness token (Witness [] (Both split (rewrite kind in rfl)))
    | NumberLiteral digits comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          Witness token (Witness [] (Both split (rewrite kind in rfl)))
    | StringLiteral written comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) =>
          Witness token (Witness [] (Both split (rewrite kind in rfl)))
    | Bracketed opened inner closed =>
      match spelled with
        | Witness open (Witness innerTokens (Witness close (Both split (Both opens others)))) =>
          Witness open (Witness (innerTokens ++ [close]) (Both split (rewrite opens in rfl)))
    | ListLiteral opened listed closed =>
      match spelled with
        | Witness open (Witness itemTokens (Witness close (Both split (Both opens others)))) =>
          Witness open (Witness (itemTokens ++ [close]) (Both split (rewrite opens in rfl)))
    | Negate minusComments operand =>
      match spelled with
        | Witness minus (Witness operandTokens (Both split (Both kind others))) =>
          Witness minus (Witness operandTokens (Both split (rewrite kind in rfl)))
    | Field target dotComments name nameComments =>
      match spelled with
        | Witness targetTokens
            (Witness dot
              (Witness named
                (Both split
                  (Both dotted
                    (Both dotAllowed
                      (Both isName (Both nameAllowed (Both spelledTarget (Both dotCommented nameCommented))))))))) =>
          match spelledStart layout target targetTokens shaped.right spelledTarget with
            | Witness first (Witness others (Both targetSplit startKind)) =>
              Witness first (Witness (others ++ [dot, named]) (Both (rewrite split, targetSplit in rfl) startKind))
    | Call callee opened arguments closed =>
      match spelled with
        | Witness calleeTokens
            (Witness open
              (Witness argumentTokens
                (Witness close
                  (Both split
                    (Both opens
                      (Both allowed
                        (Both closes
                          (Both spelledCallee (Both spelledArguments (Both openCommented closeCommented)))))))))) =>
          match spelledStart layout callee calleeTokens shaped.right.left spelledCallee with
            | Witness first (Witness others (Both calleeSplit startKind)) =>
              Witness first
                (Witness
                  (others ++ [open, ..argumentTokens ++ [close]])
                  (Both (rewrite split, calleeSplit in rfl) startKind))
    | Binary operator signComments left right =>
      match shaped, spelled with
        | Both leftLevel
            (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))), Witness leftTokens
            (Witness sign
              (Witness rightTokens
                (Both split (Both kind (Both allowed (Both spelledLeft (Both spelledRight signCommented))))))) =>
          match spelledStart layout left leftTokens shapedLeft spelledLeft with
            | Witness first (Witness others (Both leftSplit startKind)) =>
              Witness first
                (Witness (others ++ [sign, ..rightTokens]) (Both (rewrite split, leftSplit in rfl) startKind))

-- Clearing the comments above an expression's first token
-- (`Layout.headed`, which `bareStatement` applies) changes nothing where
-- none are there, and keeps the parser's shape.

--| The own-line comments the first of `tokens` holds at `layout`.
def headAbove (layout: Layout) (tokens: List (Parse.Located Token)): List Comment := match tokens with
  | [first, .._] => (layout.comments first).above
  | [] => []

theorem noAboveCleared ∀ (expr: Expr) (none: expr.firstAbove = []): expr.withoutFirstAbove = expr :=
  match expr, none with
    | Var name { above, after }, none => rewrite none in rfl
    | NumberLiteral digits { above, after }, none => rewrite none in rfl
    | StringLiteral written { above, after }, none => rewrite none in rfl
    | Bracketed ({ above, after }) inner close, none => rewrite none in rfl
    | ListLiteral ({ above, after }) items close, none => rewrite none in rfl
    | Call callee open arguments close, none => rewrite noAboveCleared callee none in rfl
    | Field target dot name nameComments, none => rewrite noAboveCleared target none in rfl
    | Negate ({ above, after }) operand, none => rewrite none in rfl
    | Binary operator sign left right, none => rewrite noAboveCleared left none in rfl
    | If ({ above, after }) condition thenComments whenTrue elseComments whenFalse, none => rewrite none in rfl

--| The comments above a spelled expression are those of its first token.
theorem spelledFirstAbove ∀ (layout: Layout) (expr: Expr) (tokens: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens):
    expr.firstAbove = headAbove layout tokens :=
  match expr with
    | If ifComments condition thenComments whenTrue elseComments whenFalse =>
      match spelled with
        | Witness ifToken
            (Witness conditionTokens
              (Witness thenToken
                (Witness trueTokens
                  (Witness elseToken
                    (Witness falseTokens
                      (Both split
                        (Both isIfToken
                          (Both ifAllowed
                            (Both isThen
                              (Both thenAllowed
                                (Both isElse
                                  (Both elseAllowed
                                    (Both spelledCondition
                                      (Both spelledTrue (Both spelledFalse (Both ifCommented others)))))))))))))))) =>
          rewrite split, ifCommented in rfl
    | Var name comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) => rewrite split, commented in rfl
    | NumberLiteral digits comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) => rewrite split, commented in rfl
    | StringLiteral written comments =>
      match spelled with
        | Witness token (Both split (Both kind (Both allowed commented))) => rewrite split, commented in rfl
    | Bracketed opened inner closed =>
      match spelled with
        | Witness open
            (Witness innerTokens
              (Witness close
                (Both split
                  (Both opens (Both allowed (Both closes (Both spelledInner (Both openCommented others)))))))) =>
          rewrite split, openCommented in rfl
    | ListLiteral opened listed closed =>
      match spelled with
        | Witness open
            (Witness itemTokens
              (Witness close
                (Both split
                  (Both opens (Both allowed (Both closes (Both spelledItems (Both openCommented others)))))))) =>
          rewrite split, openCommented in rfl
    | Negate minusComments operand =>
      match spelled with
        | Witness minus
            (Witness operandTokens (Both split (Both kind (Both allowed (Both spelledOperand commented))))) =>
          rewrite split, commented in rfl
    | Field target dotComments name nameComments =>
      match spelled with
        | Witness targetTokens
            (Witness dot
              (Witness named
                (Both split
                  (Both dotted
                    (Both dotAllowed
                      (Both isName (Both nameAllowed (Both spelledTarget (Both dotCommented nameCommented))))))))) =>
          match spelledStart layout target targetTokens shaped.right spelledTarget with
            | Witness first (Witness others (Both targetSplit startKind)) =>
              let inner := spelledFirstAbove layout target targetTokens shaped.right spelledTarget
              rewrite split, targetSplit in (rewrite targetSplit at inner in inner)
    | Call callee opened arguments closed =>
      match spelled with
        | Witness calleeTokens
            (Witness open
              (Witness argumentTokens
                (Witness close
                  (Both split
                    (Both opens
                      (Both allowed
                        (Both closes
                          (Both spelledCallee (Both spelledArguments (Both openCommented closeCommented)))))))))) =>
          match spelledStart layout callee calleeTokens shaped.right.left spelledCallee with
            | Witness first (Witness others (Both calleeSplit startKind)) =>
              let inner := spelledFirstAbove layout callee calleeTokens shaped.right.left spelledCallee
              rewrite split, calleeSplit in (rewrite calleeSplit at inner in inner)
    | Binary operator signComments left right =>
      match shaped, spelled with
        | Both leftLevel
            (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))), Witness leftTokens
            (Witness sign
              (Witness rightTokens
                (Both split (Both kind (Both allowed (Both spelledLeft (Both spelledRight signCommented))))))) =>
          match spelledStart layout left leftTokens shapedLeft spelledLeft with
            | Witness first (Witness others (Both leftSplit startKind)) =>
              let inner := spelledFirstAbove layout left leftTokens shapedLeft spelledLeft
              rewrite split, leftSplit in (rewrite leftSplit at inner in inner)

--| An offset is its own. The expression proofs and the spelling proofs
--| both rewrite with it; it is the one copy.
theorem ownOffset ∀ (offset: Nat): (offset == offset) = True := omega

--| A statement's first token holds no comments above it in the tree.
theorem startAbove ∀ (column: Nat) (first: Parse.Located Token):
    ((InStatement column first.offset).comments first).above = [] :=
  rewrite ownOffset first.offset in rfl

--| Clearing changes nothing where the first token holds no comments.
theorem spelledHeaded ∀ (layout: Layout) (expr: Expr) (tokens: List (Parse.Located Token))
    (shaped: Shaped expr)
    (spelled: Spelled layout expr tokens)
    (none: headAbove layout tokens = []):
    layout.headed expr = expr :=
  match layout, spelled, none with
    | InBrackets, spelled, none => rfl
    | InStatement column start, spelled, none =>
      noAboveCleared expr (Eq.trans (spelledFirstAbove (InStatement column start) expr tokens shaped spelled) none)

theorem clearedPostfix ∀ (expr: Expr): expr.withoutFirstAbove.isPostfix = expr.isPostfix := match expr with
  | Var _ _ => rfl
  | NumberLiteral _ _ => rfl
  | StringLiteral _ _ => rfl
  | Bracketed _ _ _ => rfl
  | ListLiteral _ _ _ => rfl
  | Call _ _ _ _ => rfl
  | Field _ _ _ _ => rfl
  | Negate _ _ => rfl
  | Binary _ _ _ _ => rfl
  | If _ _ _ _ _ _ => rfl

theorem clearedChain ∀ (expr: Expr): expr.withoutFirstAbove.isChain = expr.isChain := match expr with
  | Var _ _ => rfl
  | NumberLiteral _ _ => rfl
  | StringLiteral _ _ => rfl
  | Bracketed _ _ _ => rfl
  | ListLiteral _ _ _ => rfl
  | Call _ _ _ _ => rfl
  | Field _ _ _ _ => rfl
  | Negate _ _ => rfl
  | Binary _ _ _ _ => rfl
  | If _ _ _ _ _ _ => rfl

theorem clearedLevel ∀ (expr: Expr): expr.withoutFirstAbove.chainLevel = expr.chainLevel := match expr with
  | Var _ _ => rfl
  | NumberLiteral _ _ => rfl
  | StringLiteral _ _ => rfl
  | Bracketed _ _ _ => rfl
  | ListLiteral _ _ _ => rfl
  | Call _ _ _ _ => rfl
  | Field _ _ _ _ => rfl
  | Negate _ _ => rfl
  | Binary _ _ _ _ => rfl
  | If _ _ _ _ _ _ => rfl

theorem shapedCleared ∀ (expr: Expr) (shaped: Shaped expr): Shaped expr.withoutFirstAbove := match expr, shaped with
  | Var name comments, shaped => shaped
  | NumberLiteral digits comments, shaped => shaped
  | StringLiteral written comments, shaped => shaped
  | Bracketed open inner close, shaped => shaped
  | ListLiteral open items close, shaped => shaped
  | Call callee open arguments close, Both postfix (Both shapedCallee others) =>
    Both (Eq.trans (clearedPostfix callee) postfix) (Both (shapedCleared callee shapedCallee) others)
  | Field target dot name nameComments, Both postfix shapedTarget =>
    Both (Eq.trans (clearedPostfix target) postfix) (shapedCleared target shapedTarget)
  | Negate minus operand, shaped => shaped
  | Binary operator sign left right, Both leftLevel
      (Both rightLevel (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))) =>
    Both
      (rewrite clearedLevel left in leftLevel)
      (Both rightLevel
        (Both
          (Eq.trans (clearedChain left) leftChain)
          (Both rightChain (Both (shapedCleared left shapedLeft) shapedRight))))
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
    | Name text => rfl
    | Number digits => rfl
    | Str written => rfl
    | Op operator => rfl
    | Reserved keyword => rfl
    | Sign punctuation =>
      match punctuation, wanted with
        | OpenParen, CloseParen => rfl
        | OpenParen, CloseSquare => rfl
        | OpenSquare, CloseParen => rfl
        | OpenSquare, CloseSquare => rfl

theorem endsAtSign ∀ (token: Parse.Located Token) (punctuation: Punctuation) (rest: List (Parse.Located Token))
    (signed: token.value.kind = Sign punctuation)
    (quiet: endsSuffixes (Sign punctuation) = True):
    EndsExpression InBrackets [token, ..rest] :=
  Both (rewrite signed in quiet) (noOperatorAtSign InBrackets 0 token punctuation rest signed)

theorem bracketQuiet ∀ (closer: Punctuation) (bracket: bracketSign closer = True): endsSuffixes (Sign closer) = True :=
  match closer with
    | CloseParen => rfl
    | CloseSquare => rfl

theorem noCommaAtBracket ∀ (close: Parse.Located Token) (closer: Punctuation) (after: List (Parse.Located Token))
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True):
    signAhead Comma [close, ..after] = False :=
  rewrite closes in
    match closer with
      | CloseParen => rfl
      | CloseSquare => rfl

theorem bracketThere ∀ (close: Parse.Located Token) (closer: Punctuation)
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True):
    (signIs closer close.value.kind).isSome = True :=
  rewrite closes in
    match closer with
      | CloseParen => rfl
      | CloseSquare => rfl

--| `itemsFrom` reads the items of a list or call up to its closing
--| bracket: each item with its comma, the last without, given that `self`
--| reads each value.
theorem runsItemsFrom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat)
    (nested: ReadsNested self bound)
    (head: Item) (tail found: List Item) (fuel: Nat) (tokens after: List (Parse.Located Token))
    (close: Parse.Located Token) (closer: Punctuation)
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True)
    (shaped: ShapedItems [head, ..tail])
    (spelled: SpelledItems [head, ..tail] tokens)
    (small: tokens.length < bound)
    (enough: tail.length < fuel):
    Parse.Runs (() => itemsFrom fuel self found) tokens [close, ..after] (found.reverse ++ [head, ..tail]) :=
  match head, tail with
    | { value, comma }, [] =>
      match spelled, fuel with
        | Both spelledValue noComma, Succ more =>
          let read: Item := { value, comma = Comments.none }
          rewrite noComma in
            Parse.runsBind
              (() => item self)
              (itemsAfter more self found)
              tokens
              []
              tokens
              [close, ..after]
              (read, False)
              (found.reverse ++ [read])
              (Eq.sym (List.appendNil tokens))
              (runsItemLast self value tokens
                [close, ..after]
                (nested InBrackets value tokens
                  [close, ..after]
                  shaped.left
                  spelledValue
                  (afterBrackets tokens
                    [close, ..after]
                    (endsAtSign close closer after closes (bracketQuiet closer bracket)))
                  small)
                (noCommaAtBracket close closer after closes bracket))
              (rewrite <- List.reverseCons read found in Parse.runsPure _ [close, ..after])
    | { value, comma }, [next, ..more] =>
      match spelled, shaped, fuel with
        | Witness valueTokens
            (Witness commaToken
              (Witness laterTokens
                (Both split (Both isComma (Both spelledValue (Both commaCommented spelledLater)))))), Both shapedValue
              shapedLater, Succ less =>
          let read: Item := { value, comma = Layout.comments InBrackets commaToken }
          let sizes: tokens.length = valueTokens.length + (laterTokens.length + 1) :=
            rewrite split in List.lengthAppend valueTokens [commaToken, ..laterTokens]
          rewrite commaCommented, split in
            Parse.runsBind
              (() => item self)
              (itemsAfter less self found)
              (valueTokens ++ [commaToken])
              laterTokens
              (valueTokens ++ [commaToken, ..laterTokens])
              [close, ..after]
              (read, True)
              (found.reverse ++ [read, next, ..more])
              (Eq.sym (List.appendAssoc valueTokens [commaToken] laterTokens))
              (runsItemComma self value commaToken valueTokens
                (laterTokens ++ [close, ..after])
                (nested InBrackets value valueTokens
                  [commaToken, ..laterTokens ++ [close, ..after]]
                  shapedValue
                  spelledValue
                  (afterBrackets valueTokens
                    [commaToken, ..laterTokens ++ [close, ..after]]
                    (endsAtSign commaToken Comma (laterTokens ++ [close, ..after]) isComma rfl))
                  (omega [small, sizes]))
                isComma)
              (rewrite <- List.appendAssoc found.reverse [read] [next, ..more], <- List.reverseCons read found in
                runsItemsFrom self bound nested next more
                  [read, ..found]
                  less
                  laterTokens
                  after
                  close
                  closer
                  closes
                  bracket
                  shapedLater
                  spelledLater
                  (omega [small, sizes])
                  (omega [enough]))

--| The tokens of one or more items start with a token that starts an
--| expression, and there are at least as many as items.
theorem itemsStart ∀ (head: Item) (tail: List Item) (tokens: List (Parse.Located Token))
    (shaped: ShapedItems [head, ..tail])
    (spelled: SpelledItems [head, ..tail] tokens):
    ∃ (first: Parse.Located Token) => ∃ (others: List (Parse.Located Token)) => tokens = [first, ..others]
      ∧ startsExpression first.value.kind = True
      ∧ tail.length <= others.length :=
  match head, tail with
    | { value, comma }, [] =>
      match spelledStart InBrackets value tokens shaped.left spelled.left with
        | Witness first (Witness others (Both split startKind)) =>
          Witness first (Witness others (Both split (Both startKind (omega []))))
    | { value, comma }, [next, ..more] =>
      match spelled, shaped with
        | Witness valueTokens
            (Witness commaToken
              (Witness laterTokens
                (Both split (Both isComma (Both spelledValue (Both commaCommented spelledLater)))))), Both shapedValue
              shapedLater =>
          let valueStart := spelledStart InBrackets value valueTokens shapedValue spelledValue
          let laterStart := itemsStart next more laterTokens shapedLater spelledLater
          match valueStart, laterStart with
            | Witness first (Witness others (Both valueSplit startKind)), Witness second
                (Witness rest (Both laterSplit (Both laterKind short))) =>
              Witness first
                (Witness
                  (others ++ [commaToken, ..laterTokens])
                  (Both
                    (rewrite split, valueSplit in rfl)
                    (Both startKind
                      (rewrite laterSplit in omega [short, List.lengthAppend others [commaToken, second, ..rest]]))))

--| `items` reads the items between brackets and the closing bracket, and
--| gives the bracket's comments.
theorem runsItems ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bound: Nat)
    (nested: ReadsNested self bound)
    (listed: List Item) (tokens after: List (Parse.Located Token)) (close: Parse.Located Token) (closer: Punctuation)
    (closes: close.value.kind = Sign closer)
    (bracket: bracketSign closer = True)
    (shaped: ShapedItems listed)
    (spelled: SpelledItems listed tokens)
    (small: tokens.length < bound):
    Parse.Runs (() => items self closer) (tokens ++ [close]) after (listed, Layout.comments InBrackets close) :=
  let closed := Layout.comments InBrackets close
  match listed with
    | [] =>
      rewrite spelled in
        Parse.runsBind
          (() => signInBrackets "'${closer.spelling}'" closer)
          (found =>
            match found with
              | Some close => ([], close)
              | None =>
                let found := itemsFrom (Parse.mark().left) self []
                let close := sign InBrackets "'${closer.spelling}'" closer
                (found, close))
          [close]
          []
          [close]
          after
          (Some closed)
          ([], closed)
          rfl
          (runsSignThere "'${closer.spelling}'" closer close after (bracketThere close closer closes bracket))
          (Parse.runsPure ([], closed) after)
    | [head, ..tail] =>
      match itemsStart head tail tokens shaped spelled with
        | Witness first (Witness others (Both split (Both startKind short))) =>
          let absent: signAhead closer ((tokens ++ [close]) ++ after) = False :=
            rewrite split in startNoBracket first.value.kind closer startKind bracket
          let size: tokens.length = Succ others.length := rewrite split in rfl
          Parse.runsBind
            (() => signInBrackets "'${closer.spelling}'" closer)
            (found =>
              match found with
                | Some close => ([], close)
                | None =>
                  let found := itemsFrom (Parse.mark().left) self []
                  let close := sign InBrackets "'${closer.spelling}'" closer
                  (found, close))
            []
            (tokens ++ [close])
            (tokens ++ [close])
            after
            None
            ([head, ..tail], closed)
            rfl
            (runsSignAbsent "'${closer.spelling}'" closer ((tokens ++ [close]) ++ after) absent)
            (state starts honest =>
              let lengths: state.at.rest.length = (tokens ++ [close]).length + after.length :=
                rewrite starts in List.lengthAppend (tokens ++ [close]) after
              Parse.runsFromMark state
                (at =>
                  let found := itemsFrom at.left self []
                  let close := sign InBrackets "'${closer.spelling}'" closer
                  (found, close))
                (tokens ++ [close])
                after
                ([head, ..tail], closed)
                (Parse.runsFromBind state
                  (() => itemsFrom state.at.left self [])
                  (found =>
                    let close := sign InBrackets "'${closer.spelling}'" closer
                    (found, close))
                  tokens
                  [close]
                  (tokens ++ [close])
                  after
                  [head, ..tail]
                  ([head, ..tail], closed)
                  rfl
                  (runsItemsFrom self bound nested head tail [] state.at.left tokens after close closer closes bracket
                      shaped spelled small
                      (omega [short, size, honest, lengths, List.lengthAppend tokens [close]]))
                  (middle atRest honest1 offset =>
                    Parse.runsMap
                      (() => sign InBrackets "'${closer.spelling}'" closer)
                      (close => ([head, ..tail], close))
                      [close]
                      after
                      closed
                      (runsSign InBrackets "'${closer.spelling}'" closer close after closes rfl)
                      middle))
                starts
                honest)

theorem runsAtomList ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (open: Parse.Located Token)
    (itemTokens rest: List (Parse.Located Token)) (close: Parse.Located Token) (listed: List Item)
    (opens: open.value.kind = Sign OpenSquare)
    (allowed: layout.allows open = True)
    (runsInside: Parse.Runs (() => items self CloseSquare) (itemTokens ++ [close]) rest (
      listed,
      Layout.comments InBrackets close
    )):
    Parse.Runs
      (() => atom self layout)
      [open, ..itemTokens ++ [close]]
      rest
      (ListLiteral (layout.comments open) listed (Layout.comments InBrackets close)) :=
  state starts honest =>
    let opened := layout.comments open
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let (found, close) := items self CloseSquare
          ListLiteral opened found close)
        [open]
        (itemTokens ++ [close])
        [open, ..itemTokens ++ [close]]
        rest
        ()
        (ListLiteral opened listed (Layout.comments InBrackets close))
        rfl
        (runsSkip open ((itemTokens ++ [close]) ++ rest))
        (Parse.runsMap
          (() => items self CloseSquare)
          (read =>
            let (found, close) := read
            ListLiteral opened found close)
          (itemTokens ++ [close])
          rest
          (listed, Layout.comments InBrackets close)
          runsInside)
    match core state starts honest with
      | Witness m (Both ran after) => Witness m (Both (rewrite starts, allowed, opens in ran) after)

--| A round of `suffixesFrom` that reads a call: `(`, the arguments, `)`,
--| and on from the target with the call.
theorem runsSuffixesCall ∀ (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (open: Parse.Located Token) (argumentTokens: List (Parse.Located Token)) (close: Parse.Located Token)
    (after rest: List (Parse.Located Token)) (arguments: List Item) (value: Expr)
    (opens: open.value.kind = Sign OpenParen)
    (allowed: layout.allows open = True)
    (runsInside: Parse.Runs (() => items self CloseParen) (argumentTokens ++ [close]) (after ++ rest) (
      arguments,
      Layout.comments InBrackets close
    ))
    (runsMore: Parse.Runs
      (() =>
        suffixesFrom more self layout (Call target (layout.comments open) arguments (Layout.comments InBrackets close)))
      after
      rest
      value):
    Parse.Runs
      (() => suffixesFrom (Succ more) self layout target)
      ([open, ..argumentTokens ++ [close]] ++ after)
      rest
      value :=
  state starts honest =>
    let opened := layout.comments open
    let read := Call target opened arguments (Layout.comments InBrackets close)
    let core :=
      Parse.runsBind
        (() =>
          Parse.optional (() =>
            skip()
            let (arguments, close) := items self CloseParen
            Call target opened arguments close))
        (suffixesAfter more self layout target)
        [open, ..argumentTokens ++ [close]]
        after
        ([open, ..argumentTokens ++ [close]] ++ after)
        rest
        (Some read)
        value
        rfl
        (Parse.runsOptional
          (() =>
            skip()
            let (arguments, close) := items self CloseParen
            Call target opened arguments close)
          [open, ..argumentTokens ++ [close]]
          (after ++ rest)
          read
          (Parse.runsBind
            (() => skip())
            (skipped =>
              let (arguments, close) := items self CloseParen
              Call target opened arguments close)
            [open]
            (argumentTokens ++ [close])
            [open, ..argumentTokens ++ [close]]
            (after ++ rest)
            ()
            read
            rfl
            (runsSkip open ((argumentTokens ++ [close]) ++ (after ++ rest)))
            (Parse.runsMap
              (() => items self CloseParen)
              (found =>
                let (arguments, close) := found
                Call target opened arguments close)
              (argumentTokens ++ [close])
              (after ++ rest)
              (arguments, Layout.comments InBrackets close)
              runsInside)))
        runsMore
    match core state starts honest with
      | Witness m (Both ran others) => Witness m (Both (rewrite starts, allowed, opens in ran) others)

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
    | True => rewrite reserved in rfl
    | False => rfl

theorem notIfAtReserved ∀ (layout: Layout) (token: Parse.Located Token) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword)
    (notIf: keyword ≠ IfKeyword):
    isIf layout token = False :=
  match allowed: layout.allows token with
    | False => rfl
    | True =>
      rewrite reserved in
        match keyword, notIf with
          | IfKeyword, notIf => Void.exfalso (notIf rfl)
          | FnKeyword, notIf => rfl
          | LetKeyword, notIf => rfl
          | ThenKeyword, notIf => rfl
          | ElseKeyword, notIf => rfl

--| No atom starts with a keyword.
theorem atomDeclines ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (token: Parse.Located Token)
    (later: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    Parse.Declines (() => atom self layout) [token, ..later] :=
  state starts honest =>
    let step: Parse.runFrom state (() => (Parse.optional (() => atom self layout), Parse.mark()))
      = Parse.runFrom state (() => (Parse.optional (() => (Parse.expected "an expression": Expr)), Parse.mark())) :=
      rewrite starts in
        match allowed: layout.allows token with
          | True => rewrite reserved in rfl
          | False => rfl
    Eq.trans step (Parse.declinesExpected "an expression" [token, ..later] state starts honest)

theorem postfixDeclines ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (later: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword):
    Parse.Declines (() => postfix self layout) [token, ..later] :=
  Parse.declinesAfter
    (() => Parse.note (Parse.Problem.Expected "an expression"))
    (noted =>
      let first := atom self layout
      suffixesFrom (Parse.mark().left + 1) self layout first)
    []
    [token, ..later]
    ()
    (Parse.runsNote (Parse.Problem.Expected "an expression") [token, ..later])
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
        | Zero => rfl
        | Succ more => rewrite starts, notMinusAtReserved layout token keyword reserved in rfl
    Eq.trans step (postfixDeclines self layout token later keyword reserved state starts honest)

--| `operators` declines where its first operand does.
theorem operatorsDecline ∀ (levels: List (Parse.Level (Parse.Located Token) Expr))
    (operand: () → {Parse (Parse.Located Token)} Expr) (input: List (Parse.Located Token))
    (declines: Parse.Declines operand input):
    Parse.Declines (() => Parse.operators "an operator" levels operand) input :=
  state starts honest =>
    Parse.declinesBind operand
      (first => Parse.operandsAfter (state.at.left + 1) "an operator" levels levels.length operand 0 first)
      input
      declines
      state
      starts
      honest

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
    | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite noIf in rfl

--| No expression starts with a keyword other than `if`, whatever reads
--| the expressions nested in it.
theorem expressionRuleDeclines ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (token: Parse.Located Token) (later: List (Parse.Located Token)) (keyword: Keyword)
    (reserved: token.value.kind = Reserved keyword)
    (notIf: keyword ≠ IfKeyword):
    Parse.Declines (() => expressionRule self layout) [token, ..later] :=
  state starts honest =>
    Eq.trans
      (chainRuleStops self layout state (rewrite starts in notIfAtReserved layout token keyword reserved notIf))
      (operatorsDecline
        (operatorLevels layout)
        (() => operand self layout)
        [token, ..later]
        (inner begins fair =>
          negationsDecline (inner.at.left + 1) self layout token later keyword reserved inner begins fair)
        state
        starts
        honest)

--| The expression parser of each level of the recursion but the
--| innermost, which reads nothing, declines at a keyword.
theorem fuelDeclines ∀ (more: Nat):
    DeclinesNested (inner => Parse.recursiveWithFuel (Succ more) expressionRule inner) :=
  layout token later keyword reserved notIf =>
    expressionRuleDeclines
      (inner => Parse.recursiveWithFuel more expressionRule inner)
      layout
      token
      later
      keyword
      reserved
      notIf

theorem expressionDeclines: DeclinesNested expression := layout token later keyword reserved notIf =>
  state starts honest => fuelDeclines state.at.left layout token later keyword reserved notIf state starts honest

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

def exampleCall: Expr :=
  Call (Var "f" Comments.none) Comments.none [{ value = Var "a" Comments.none, comma = Comments.none }] Comments.none

def exampleExpr: Expr := Binary Plus Comments.none exampleCall (Var "b" Comments.none)

theorem runsExpressionExample: Parse.run exampleTokens (() => expression InBrackets) = Ok exampleExpr :=
  let f := exampleToken (Name "f") 0
  let open := exampleToken (Sign OpenParen) 1
  let a := exampleToken (Name "a") 2
  let close := exampleToken (Sign CloseParen) 3
  let plus := exampleToken (Op Plus) 5
  let b := exampleToken (Name "b") 7
  let spelledCall: Spelled InBrackets exampleCall [f, open, a, close] :=
    Witness
      [f]
      (Witness open
        (Witness
          [a]
          (Witness close
            (Both rfl
              (Both rfl
                (Both rfl
                  (Both rfl
                    (Both
                      (Witness f (Both rfl (Both rfl (Both rfl rfl))))
                      (Both (Both (Witness a (Both rfl (Both rfl (Both rfl rfl)))) rfl) (Both rfl rfl))))))))))
  Parse.runsRun
    (() => expression InBrackets)
    exampleTokens
    exampleExpr
    (runsExpression InBrackets exampleExpr exampleTokens []
      (Both
        (omega [])
        (Both (omega []) (Both rfl (Both rfl (Both (Both rfl (Both rfl (Both (Both rfl rfl) rfl))) rfl)))))
      (Witness
        [f, open, a, close]
        (Witness plus
          (Witness
            [b]
            (Both rfl
              (Both rfl (Both rfl (Both spelledCall (Both (Witness b (Both rfl (Both rfl (Both rfl rfl)))) rfl))))))))
      (Both (Both rfl rfl) rfl))
