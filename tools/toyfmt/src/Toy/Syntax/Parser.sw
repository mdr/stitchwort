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
import Std (Empty, Fail, List, NonEmptyList, Option, Parse, Result, Text)

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
  let finish := Parse.mark()
  start.rest.drop (finish.offset - start.offset - 1) |> .head |> .map (token => token.value)

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

-- Expressions. They nest, so they are read by `nested` with `self`, the
-- expression parser at a layout; the rest of the grammar gets `self` as an
-- argument and doesn't call itself.

--| `body` with `self` for its nested parser, at most `fuel` levels deep.
def nestedFuel (fuel: Nat) (body: (b → {Parse t} a) → b → {Parse t} a) (argument: b): {Parse t} a := match fuel with
  | Zero => Empty.absurd (Parse.fatal "nested too deeply")
  | Succ more => body (inner => nestedFuel more body inner) argument

--| `Parse.recursive` for a parser that takes an argument. Each level reads
--| a token before it nests, so the tokens left are enough fuel.
def nested (body: (b → {Parse t} a) → b → {Parse t} a) (argument: b): {Parse t} a :=
  nestedFuel (Parse.mark().left + 1) body argument

def expression (layout: Layout): {Parse (Parse.Located Token)} Expr := nested expressionRule layout

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
    | _ => chain (() => operand self layout) layout levels

def elseKeyword (layout: Layout): {Parse (Parse.Located Token)} () := match peek() with
  | Some token if (keywordIs ElseKeyword token.value.kind).isSome =>
    if layout.allowsElse token then skip()
    else Parse.fail "'else' must not start a line to the left of its 'if' statement"
  | _ => keyword layout ElseKeyword

--| `Operator.level`'s values, loosest first.
def levels: List Nat := List.range 1 7

--| Operator chains, loosest level first: each level's operands are chains
--| of the tighter levels.
def chain (operand: () → {Parse (Parse.Located Token)} Expr) (layout: Layout):
    (levels: List Nat) → {Parse (Parse.Located Token)} Expr
  | [] => operand()
  | [level, ..tighter] =>
    Parse.chainLeft (() => chain operand layout tighter) (() => take layout "an operator" (binaryAt level))

def binaryAt (level: Nat): Kind → Option (Expr → Expr → Expr)
  | Op operator if operator.level == level => Some (left right => Binary operator left right)
  | _ => None

def isMinus: Kind → Option ()
  | Op Minus => Some ()
  | _ => None

--| `-` any number of times, then an atom and its calls and fields.
def operand (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout): {Parse (Parse.Located Token)} Expr :=
  let negations := Parse.many (() => take layout "an expression" isMinus)
  let first := atom self layout
  let suffixes := Parse.many (() => suffix self layout)
  let value := suffixes.foldLeft first (target apply => apply target)
  negations.foldLeft value (inner _ => Negate inner)

def suffix (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout):
    {Parse (Parse.Located Token)} (Expr → Expr) :=
  Parse.oneOf [
    () =>
      sign layout "'('" OpenParen
      let arguments := items self CloseParen
      (callee => Call callee arguments),
    () =>
      sign layout "'.'" Dot
      let field := name layout
      (target => Field target field)
  ]

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
  match Parse.optional (() => sign InBrackets closing closer) with
    | Some () => []
    | None =>
      let found := itemsFrom (Parse.mark().left) self []
      sign InBrackets closing closer
      found

--| Items while each is followed by a comma, at most `fuel` more. `found`
--| is newest first.
def itemsFrom (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (found: List Item):
    {Parse (Parse.Located Token)} List Item :=
  match fuel with
    | Zero => found.reverse
    | Succ more =>
      let (next, comma) := item self
      if comma then itemsFrom more self [next, ..found] else [next, ..found].reverse

--| An item, its comma if one follows, and whether one did. The comma is
--| the item's last token, so a comment after it is the item's.
def item (self: Layout → {Parse (Parse.Located Token)} Expr): {Parse (Parse.Located Token)} (Item, Bool) :=
  let start := Parse.mark()
  let comments := start.rest.head |> .map (token => ownLineComments token.value.above) |> .getOrElse []
  let value := self InBrackets
  let comma := Parse.optional (() => sign InBrackets "','" Comma) |> .isSome
  let trailing := if comma then lastTrailing start else trailingSince start value
  ({ comments, value, trailing }, comma)

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
    | _, _, _ =>
      let start := Parse.mark()
      let value := self layout
      { statements = [{ blankBefore = False, line = Bare value (trailingSince start value) }] }

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
      let layout := InStatement column first.offset
      let (notes, blankBefore) := spacedNotes StatementNote first.value.above
      let line := match first.value.kind with
        | Reserved LetKeyword =>
          skip()
          let bound := name layout
          sign layout "'='" Defines
          Let bound (bodyFuel fuel self layout)
        | _ =>
          let value := self layout
          Bare value (trailingSince start value)
      notes ++ [{ blankBefore, line }]
    | _ => Empty.absurd Parse.stop()

-- Declarations and the file.

--| A declaration starting a line at column 0, after the own-line comments
--| above it; kept as written if a comment in it wasn't placed.
def declaration (source: Text): {Parse (Parse.Located Token)} List (Spaced Declaration) :=
  let start := Parse.mark()
  match start.rest with
    | [first, .._] if first.value.startsLine && first.value.column == 0 =>
      let layout := InStatement 0 first.offset
      let (notes, blankBefore) := spacedNotes DeclarationNote first.value.above
      let parsed := match first.value.kind with
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
      let finish := Parse.mark()
      let tokens := start.rest.take (finish.offset - start.offset)
      let line := if parsed.comments < commentsAmong tokens then AsWritten (asWritten source tokens) else parsed
      notes ++ [{ blankBefore, line }]
    | _ => Empty.absurd Parse.stop()

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

def sourceFile (source: Text): {Parse (Parse.Located Token)} SourceFile :=
  let all := Parse.mark().rest
  let declarations := Parse.many (() => declaration source) |> .concat
  match peek() with
    | Some token if token.value.startsLine && token.value.column > 0 =>
      Parse.fail "this line's indentation matches no block it could belong to"
    | _ =>
      let (endNotes, _) :=
        all.last |> .map (token => spacedNotes DeclarationNote token.value.below) |> .getOrElse ([], False)
      { declarations = declarations ++ endNotes |> withoutFirstBlank }

--| A file with no tokens: its comments, as notes.
def commentsOnly (source: Text): SourceFile :=
  let trivia := source.lines.foldLeft ([]: List Trivia) (found line =>
    let trimmed := line.trim
    if trimmed.isEmpty then addBlank found else [OwnLine { text = trimmed }, ..found])
  let (notes, _) := spacedNotes DeclarationNote trivia.reverse
  { declarations = withoutFirstBlank notes }

--| The tree of a Sprig source, or the first error as "line 3, column 9:
--| expected ',' or ')', got 'b'".
def parse (source: Text): Result SourceFile Text :=
  Fail.toResult (() => Parse.tokens source (() => lex source) (() => sourceFile source))
    |> .map (file => if file.declarations.isEmpty then commentsOnly source else file)
