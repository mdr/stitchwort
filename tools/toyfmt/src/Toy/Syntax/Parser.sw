--| Sprig's parser: the lexer's tokens read into a `SourceFile` with `Parse`
--| over tokens, as `Tree.sw`'s comment describes.
--|
--| Blocks go by indentation. A block's statements each start a line at the
--| block's column; any other line of a statement starts deeper. Every
--| token is read through a `Layout`, passed down from the statement being
--| read, which turns away a token that starts a line too far left, so a
--| statement ends where the next line isn't deeper. Inside brackets line
--| starts don't matter.
--|
--| Comments are placed as they are read: own-line comments at the start of
--| a declaration, statement, list item or argument, from its first token;
--| a trailing comment at the end of a list item, argument or bare
--| statement, from its last. A declaration in which some comment wasn't
--| placed that way is kept as written.

namespace Toy.Syntax
import Std.Parse.Associativity (LeftAssociative)
import Std (Empty, List, NonEmptyList, Option, Parse, Result, Text)

--| How a token may stand: anywhere inside brackets; in a statement that
--| starts at `start` (an offset in the source) at `column`, on that line
--| or on a deeper one.
type Layout = | InBrackets | InStatement (column: Nat) (start: Nat)

def Layout.allows (layout: Layout) (token: Parse.Located Token): Bool := match layout with
  | InBrackets => True
  | InStatement column start => not token.value.startsLine || token.value.column > column || token.offset == start

--| `else` may also start a line at the statement's own column, under its
--| `if`.
def Layout.allowsElse (layout: Layout) (token: Parse.Located Token): Bool := match layout with
  | InBrackets => True
  | InStatement column _ => not token.value.startsLine || token.value.column >= column

def selectAllowed (layout: Layout) (select: Kind → Option a) (token: Parse.Located Token): Option a :=
  if layout.allows token then select token.value.kind else None

--| The next token's value from `select`, if the layout allows it there,
--| else "expected `what`".
def take (layout: Layout) (what: Text) (select: Kind → Option a): {Parse (Parse.Located Token)} a :=
  Parse.one what (selectAllowed layout select)

def peek(): {Parse (Parse.Located Token)} Option (Parse.Located Token) := Parse.mark().rest.head

def skip(): {Parse (Parse.Located Token)} () :=
  let skipped := Parse.next (token => True)
  ()

def nameOf: Kind → Option Text
  | Name text => Some text
  | _ => None

def name (layout: Layout): {Parse (Parse.Located Token)} Text := take layout "a name" nameOf

def signIs (wanted: Punctuation): Kind → Option ()
  | Sign found => if found == wanted then Some () else None
  | _ => None

def sign (layout: Layout) (what: Text) (wanted: Punctuation): {Parse (Parse.Located Token)} () :=
  take layout what (signIs wanted)

def keywordIs (wanted: Keyword): Kind → Option ()
  | Reserved found => if found == wanted then Some () else None
  | _ => None

def keyword (layout: Layout) (wanted: Keyword): {Parse (Parse.Located Token)} () :=
  take layout "'${wanted.spelling}'" (keywordIs wanted)

--| The last token read since `start`, which was before at least one.
def lastSince (start: Parse.Mark (Parse.Located Token)): {Parse (Parse.Located Token)} Option Token :=
  Parse.lastRead start Parse.mark() |> .map (token => token.value)

--| The comment after the last token read since `start`.
def lastTrailing (start: Parse.Mark (Parse.Located Token)): {Parse (Parse.Located Token)} Option Comment :=
  lastSince start |> .flatMap (token => token.trailing) |> .map (comment => comment.value)

--| The trailing comment of the item or bare statement `value`, read since
--| `start`. One ending in an `if` ends in the `if`'s last branch, whose own
--| bare statement has already taken it.
def trailingSince (start: Parse.Mark (Parse.Located Token)) (value: Expr):
    {Parse (Parse.Located Token)} Option Comment :=
  match value with
    | If _ _ _ => None
    | _ => lastTrailing start

--| The own-line comments in `trivia` as lines of a list, each knowing if a
--| blank line was above it, and whether one is above what follows them.
def spacedNotes (note: Comment → a) (trivia: List Trivia): (List (Spaced a), Bool) :=
  trivia.foldLeft
    (([], False): (List (Spaced a), Bool))
    (((lines, blank) piece =>
      match piece with
        | BlankLine => (lines, True)
        | OwnLine comment => (lines ++ [{ blankBefore = blank, line = note comment }], False)))

def ownLineComments (trivia: List Trivia): List Comment := trivia.filterMap (match some | OwnLine comment => comment)

--| The first line of a list has no blank line above it.
def withoutFirstBlank (lines: List (Spaced a)): List (Spaced a) := match lines with
  | [first, ..rest] => [{ first | blankBefore = False }, ..rest]
  | [] => []

-- Expressions. They nest, so they are read by `Parse.recursiveWith` with `self`, the
-- expression parser at a layout; the rest of the grammar gets `self` as an
-- argument and doesn't call itself.

def expression (layout: Layout): {Parse (Parse.Located Token)} Expr := Parse.recursiveWith expressionRule layout

def isIf (layout: Layout) (token: Parse.Located Token): Bool :=
  layout.allows token && token.value.kind |> matches | Reserved IfKeyword

def expressionRule (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout):
    {Parse (Parse.Located Token)} Expr :=
  match peek() with
    | Some token if isIf layout token =>
      skip()
      let condition := self layout
      keyword layout ThenKeyword
      let whenTrue := body self layout
      elseKeyword layout
      let whenFalse := body self layout
      If condition whenTrue whenFalse
    | _ => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout)

def elseKeyword (layout: Layout): {Parse (Parse.Located Token)} () := match peek() with
  | Some token if (keywordIs ElseKeyword token.value.kind).isSome =>
    if layout.allowsElse token then skip()
    else Parse.fail "'else' must not start a line to the left of its 'if' statement"
  | _ => keyword layout ElseKeyword

--| The operators of each level (1 for `||` to 6 for `* / %`, see
--| `Operator.level`) that a token may be at `layout`, each level chaining
--| from the left: `a - b + c` is `(a - b) + c`.
def operatorLevels (layout: Layout): List (Parse.Level (Parse.Located Token) Expr) :=
  [1, 2, 3, 4, 5, 6].map (level => { associativity = LeftAssociative, operator = operatorOf layout level })

def operatorOf (layout: Layout) (level: Nat) (token: Parse.Located Token): Option (Expr → Expr → Expr) :=
  match token.value.kind with
    | Op operator if operator.level == level && layout.allows token => Some (Binary operator)
    | _ => None

def isMinus (layout: Layout) (token: Parse.Located Token): Bool :=
  layout.allows token && token.value.kind |> matches | Op Minus

--| `-` any number of times, then an atom and its calls and fields.
def operand (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout): {Parse (Parse.Located Token)} Expr :=
  negationsFrom (Parse.mark().left + 1) self layout

--| The `-`s before an atom, at most `fuel` of them, each a `Negate`
--| around the rest.
def negationsFrom (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout):
    {Parse (Parse.Located Token)} Expr :=
  match fuel, peek() with
    | Succ more, Some token if isMinus layout token =>
      skip()
      Negate (negationsFrom more self layout)
    | _, _ => postfix self layout

--| An atom and its calls and fields.
def postfix (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout): {Parse (Parse.Located Token)} Expr :=
  Parse.note (Parse.Problem.Expected "an expression")
  let first := atom self layout
  suffixesFrom (Parse.mark().left + 1) self layout first

--| `target`'s calls and fields, at most `fuel` of them. A call or field
--| that doesn't parse is left unread.
def suffixesFrom (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (target: Expr):
    {Parse (Parse.Located Token)} Expr :=
  let next := match peek() with
    | Some token if layout.allows token => token.value.kind
    | _ => Stray ""
  match fuel, next with
    | Succ more, Sign OpenParen =>
      let call := Parse.optional (() =>
        skip()
        Call target (items self CloseParen))
      suffixesAfter more self layout target call
    | Succ more, Sign Dot =>
      let field := Parse.optional (() =>
        skip()
        Field target (name layout))
      suffixesAfter more self layout target field
    | _, _ =>
      Parse.note (Parse.Problem.Expected "'('")
      Parse.note (Parse.Problem.Expected "'.'")
      target

--| What `suffixesFrom` does with the call or field it tried after `target`:
--| on from `longer`, the target with it, or `target` alone if it didn't
--| parse.
-- A function of its own so that proofs (ExpressionProofs.sw) can name it.
def suffixesAfter (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (longer: Option Expr):
    {Parse (Parse.Located Token)} Expr :=
  match longer with
    | Some longer => suffixesFrom more self layout longer
    | None => target

def atom (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout): {Parse (Parse.Located Token)} Expr :=
  match peek() with
    | Some token if layout.allows token =>
      match token.value.kind with
        | Name text =>
          skip()
          Var text
        | Number digits =>
          skip()
          NumberLiteral digits
        | Str written =>
          skip()
          StringLiteral written
        | Sign OpenParen =>
          skip()
          let inner := self InBrackets
          sign InBrackets "')'" CloseParen
          Bracketed inner
        | Sign OpenSquare =>
          skip()
          ListLiteral (items self CloseSquare)
        | _ => Parse.expected "an expression"
    | _ => Parse.expected "an expression"

--| A list's items or a call's arguments, then `closer`; the opening bracket
--| has been read.
def items (self: Layout → {Parse (Parse.Located Token)} Expr) (closer: Punctuation):
    {Parse (Parse.Located Token)} List Item :=
  let closing := "'${closer.spelling}'"
  if signInBrackets closing closer then []
  else
    let found := itemsFrom (Parse.mark().left) self []
    sign InBrackets closing closer
    found

--| Whether the sign `wanted` comes next, read if it does, else noted as
--| expected: `Parse.optional (() => sign InBrackets what wanted)` without
--| the handler, since reading one token can't fail halfway.
def signInBrackets (what: Text) (wanted: Punctuation): {Parse (Parse.Located Token)} Bool := match peek() with
  | Some token if (signIs wanted token.value.kind).isSome =>
    skip()
    True
  | _ =>
    Parse.note (Parse.Problem.Expected what)
    False

--| Items while each is followed by a comma, at most `fuel` more. `found`
--| is newest first.
def itemsFrom (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (found: List Item):
    {Parse (Parse.Located Token)} List Item :=
  match fuel with
    | Zero => found.reverse
    | Succ more => itemsAfter more self found (item self)

--| What `itemsFrom` does with the item it read and whether a comma followed
--| it: on to the next item after a comma, else the items found.
-- A function of its own so that proofs (ExpressionProofs.sw) can name it.
def itemsAfter (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (found: List Item) (read: (Item, Bool)):
    {Parse (Parse.Located Token)} List Item :=
  if read.snd then itemsFrom more self [read.fst, ..found] else [read.fst, ..found].reverse

--| An item, its comma if one follows, and whether one did. The comma is
--| the item's last token, so a comment after it is the item's.
def item (self: Layout → {Parse (Parse.Located Token)} Expr): {Parse (Parse.Located Token)} (Item, Bool) :=
  let start := Parse.mark()
  let comments := commentsAbove start.rest
  let value := self InBrackets
  let comma := signInBrackets "','" Comma
  let trailing := if comma then lastTrailing start else trailingSince start value
  ({ comments, value, trailing }, comma)

--| The own-line comments above the first of the tokens.
def commentsAbove (tokens: List (Parse.Located Token)): List Comment :=
  tokens.head |> .map (token => ownLineComments token.value.above) |> .getOrElse []

def Punctuation.spelling: Punctuation → Text
  | OpenParen => "("
  | CloseParen => ")"
  | OpenSquare => "["
  | CloseSquare => "]"
  | Comma => ","
  | Dot => "."
  | Defines => "="

-- Bodies and blocks.

--| What follows `=`, `then` or `else`: a block if the next token starts a
--| line deeper than the statement, else one expression.
def body (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout): {Parse (Parse.Located Token)} Body :=
  bodyFuel (Parse.mark().left + 1) self layout

--| `body`, through blocks nested at most `fuel` deep. Each level reads a
--| token before it nests, so the tokens left are enough.
def bodyFuel (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout):
    {Parse (Parse.Located Token)} Body :=
  match fuel, layout, peek() with
    | Zero, _, _ => Empty.absurd (Parse.fatal "nested too deeply")
    | Succ more, InStatement column _, Some token if token.value.startsLine && token.value.column > column =>
      block more self token.value.column
    | _, _, _ => inlineBody self layout

--| A body that is one expression, on the line of what it follows.
-- A function of its own so that proofs (BlockProofs.sw) can name it; so
-- are `bareStatement`, `statementLine` and `notedStatement`.
def inlineBody (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout): {Parse (Parse.Located Token)} Body :=
  let start := Parse.mark()
  let line := bareStatement self layout start
  { statements = [{ blankBefore = False, line }] }

--| An expression as a statement, with the trailing comment it ends in;
--| `start` is where it starts.
def bareStatement (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (start: Parse.Mark (Parse.Located Token)):
    {Parse (Parse.Located Token)} Statement :=
  let value := self layout
  Bare value (trailingSince start value)

--| Statements starting lines at `column`, with the comments above them.
def block (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat):
    {Parse (Parse.Located Token)} Body :=
  let lines := Parse.many1 (() => statement fuel self column)
  { statements = lines.toList.concat |> withoutFirstBlank }

--| A statement starting a line at `column`, after the own-line comments
--| above it; fails without a message if the next token doesn't start a line
--| there, which ends the block.
def statement (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (column: Nat):
    {Parse (Parse.Located Token)} List (Spaced Statement) :=
  let start := Parse.mark()
  match start.rest with
    | [first, .._] if first.value.startsLine && first.value.column == column =>
      let line := statementLine fuel self (InStatement column first.offset) start first.value.kind
      notedStatement first.value.above line
    | _ => Empty.absurd Parse.stop()

--| The statement whose first token, at `start`, is of `kind`: a `let`, or
--| else an expression.
def statementLine (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (start: Parse.Mark (Parse.Located Token)) (kind: Kind):
    {Parse (Parse.Located Token)} Statement :=
  match kind with
    | Reserved LetKeyword =>
      skip()
      let bound := name layout
      sign layout "'='" Defines
      Let bound (bodyFuel fuel self layout)
    | _ => bareStatement self layout start

--| A statement's lines: the own-line comments in `above`, the trivia on
--| its first token, then the statement.
def notedStatement (above: List Trivia) (line: Statement): List (Spaced Statement) :=
  let (notes, blankBefore) := spacedNotes StatementNote above
  notes ++ [{ blankBefore, line }]

-- Declarations and the file.

--| A declaration starting a line at column 0, after the own-line comments
--| above it; kept as written if a comment in it wasn't placed.
def declaration (source: Text): {Parse (Parse.Located Token)} List (Spaced Declaration) :=
  let start := Parse.mark()
  match start.rest with
    | [first, .._] if first.value.startsLine && first.value.column == 0 =>
      let parsed := declarationLine (InStatement 0 first.offset) first.value.kind
      let finish := Parse.mark()
      notedDeclaration source first.value.above (start.rest.take (finish.offset - start.offset)) parsed
    | _ => Empty.absurd Parse.stop()

--| The declaration whose first token is of `kind`: `fn` or `let`.
-- A function of its own so that proofs (BlockProofs.sw) can name it; so
-- are `notedDeclaration` and `fileEnd`.
def declarationLine (layout: Layout) (kind: Kind): {Parse (Parse.Located Token)} Declaration := match kind with
  | Reserved FnKeyword =>
    skip()
    let declared := name layout
    sign layout "'('" OpenParen
    let parameters := Parse.sepBy (() => name InBrackets) (() => sign InBrackets "','" Comma)
    sign InBrackets "')'" CloseParen
    sign layout "'='" Defines
    Function declared parameters (body expression layout)
  | Reserved LetKeyword =>
    skip()
    let declared := name layout
    sign layout "'='" Defines
    Value declared (body expression layout)
  | _ =>
    Parse.note (Parse.Problem.Literal "fn")
    Parse.note (Parse.Problem.Literal "let")
    Empty.absurd Parse.stop()

--| A declaration's lines: the own-line comments in `above`, the trivia on
--| its first token, then `parsed`, or its `tokens` as written if one of
--| their comments has no place in it.
def notedDeclaration (source: Text) (above: List Trivia) (tokens: List (Parse.Located Token)) (parsed: Declaration):
    List (Spaced Declaration) :=
  let (notes, blankBefore) := spacedNotes DeclarationNote above
  let line := if parsed.comments < commentsAmong tokens then AsWritten (asWritten source tokens) else parsed
  notes ++ [{ blankBefore, line }]

--| The comments among a declaration's tokens, not counting those above
--| its first token, which are the file's.
def commentsAmong (tokens: List (Parse.Located Token)): Nat := tokens.withIndex.foldLeft 0 (count (index, token) =>
  let above := if index == 0 then 0 else (ownLineComments token.value.above).length
  count + above + (if token.value.trailing.isSome then 1 else 0))

--| A declaration's text as written: from its first token to the end of its
--| last, or of the comment after it.
def asWritten (source: Text) (tokens: List (Parse.Located Token)): Text := match tokens.head, tokens.last with
  | Some first, Some last =>
    let finish := match last.value.trailing with
      | Some comment => comment.offset + comment.length
      | None => last.offset + last.length
    source.slice first.offset finish
  | _, _ => ""

--| The file, given the comments after its last token (or all of them, with
--| no tokens).
def sourceFile (source: Text) (endTrivia: List Trivia): {Parse (Parse.Located Token)} SourceFile :=
  let found := Parse.many (() => declaration source)
  fileEnd found.concat endTrivia

--| The file of `declarations`, read to where no more starts, and the
--| comments after them; an indented line there belongs to nothing.
def fileEnd (declarations: List (Spaced Declaration)) (endTrivia: List Trivia):
    {Parse (Parse.Located Token)} SourceFile :=
  match peek() with
    | Some token if token.value.startsLine && token.value.column > 0 =>
      Parse.fail "this line's indentation matches no block it could belong to"
    | _ => fileOf declarations endTrivia

def fileOf (declarations: List (Spaced Declaration)) (endTrivia: List Trivia): SourceFile :=
  let (endNotes, _) := spacedNotes DeclarationNote endTrivia
  { declarations = declarations ++ endNotes |> withoutFirstBlank }

--| The tree of a Sprig source, or the first error as "line 3, column 9:
--| expected ',' or ')', got 'b'". The source is lexed and checked first
--| (`lex`), so every tree comes from tokens that cover the source.
def parse (source: Text): Result SourceFile Text := match lex source with
  | Err message => Err message
  | Ok lexed =>
    match Parse.whole lexed.tokens (() => sourceFile source lexed.endTrivia) with
      | Ok file => Ok file
      | Err failure => Err (Parse.tokensMessage source.toList lexed.tokens failure)
