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
--| Comments are carried, not placed: each token's comments go into the
--| tree beside it (`Layout.comments`) as the token is read, so no source
--| that parses is left without a tree.

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

--| The comments `token` holds, as the tree keeps them. The own-line
--| comments above a statement's first token (at the layout's `start`) are
--| the block's note lines instead, and its blank lines count only there.
def Layout.comments (layout: Layout) (token: Parse.Located Token): Comments :=
  let above := match layout with
    | InStatement _ start if token.offset == start => []
    | _ => ownLineComments token.value.above
  { above, after = token.value.trailing.map (comment => comment.value) }

def selectAllowed (layout: Layout) (select: Kind → Option a) (token: Parse.Located Token): Option a :=
  if layout.allows token then select token.value.kind else None

--| `select`'s value for `token`, and its comments, if the layout allows it.
def selectWithComments (layout: Layout) (select: Kind → Option a) (token: Parse.Located Token): Option (a, Comments) :=
  selectAllowed layout select token |> .map (value => (value, layout.comments token))

--| The comments of `token`, if the layout allows it and `select` takes it.
def selectComments (layout: Layout) (select: Kind → Option a) (token: Parse.Located Token): Option Comments :=
  selectAllowed layout select token |> .map (found => layout.comments token)

--| The next token's value from `select` and its comments, if the layout
--| allows it there, else "expected `what`".
def take (layout: Layout) (what: Text) (select: Kind → Option a): {Parse (Parse.Located Token)} (a, Comments) :=
  Parse.one what (selectWithComments layout select)

def peek(): {Parse (Parse.Located Token)} Option (Parse.Located Token) := Parse.mark().rest.head

def skip(): {Parse (Parse.Located Token)} () :=
  let skipped := Parse.next (token => True)
  ()

def nameOf: Kind → Option Text
  | Name text => Some text
  | _ => None

def name (layout: Layout): {Parse (Parse.Located Token)} (Text, Comments) := take layout "a name" nameOf

def signIs (wanted: Punctuation): Kind → Option ()
  | Sign found => if found == wanted then Some () else None
  | _ => None

--| The sign `wanted`'s comments, if it comes next and the layout allows it
--| there, else "expected `what`".
def sign (layout: Layout) (what: Text) (wanted: Punctuation): {Parse (Parse.Located Token)} Comments :=
  Parse.one what (selectComments layout (signIs wanted))

def keywordIs (wanted: Keyword): Kind → Option ()
  | Reserved found => if found == wanted then Some () else None
  | _ => None

def keyword (layout: Layout) (wanted: Keyword): {Parse (Parse.Located Token)} Comments :=
  Parse.one "'${wanted.spelling}'" (selectComments layout (keywordIs wanted))

--| The own-line comments in `trivia` as lines of a list, each knowing if a
--| blank line was above it, and whether one is above what follows them.
def spacedNotes (note: Comment → a) (trivia: List Trivia): (List (Spaced a), Bool) :=
  trivia.foldLeft (([], False): (List (Spaced a), Bool)) (noteStep note)

--| `spacedNotes` after one more piece: a comment is a line, with the blank
--| line seen before it; a blank line is remembered for the next line.
-- A function of its own so that proofs (ShapeProofs.sw) can name it.
def noteStep (note: Comment → a) (found: (List (Spaced a), Bool)) (piece: Trivia): (List (Spaced a), Bool) :=
  match piece with
    | BlankLine => (found.fst, True)
    | OwnLine comment => (found.fst ++ [{ blankBefore = found.snd, line = note comment }], False)

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
      let thenComments := keyword layout ThenKeyword
      let whenTrue := body self layout
      let elseComments := elseKeyword layout
      let whenFalse := body self layout
      If (layout.comments token) condition thenComments whenTrue elseComments whenFalse
    | _ => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout)

def elseKeyword (layout: Layout): {Parse (Parse.Located Token)} Comments := match peek() with
  | Some token if (keywordIs ElseKeyword token.value.kind).isSome =>
    if layout.allowsElse token then
      skip()
      layout.comments token
    else Parse.fail "'else' must not start a line to the left of its 'if' statement"
  | _ => keyword layout ElseKeyword

--| The operators of each level (1 for `||` to 6 for `* / %`, see
--| `Operator.level`) that a token may be at `layout`, each level chaining
--| from the left: `a - b + c` is `(a - b) + c`.
def operatorLevels (layout: Layout): List (Parse.Level (Parse.Located Token) Expr) :=
  [1, 2, 3, 4, 5, 6].map (level => { associativity = LeftAssociative, operator = operatorOf layout level })

def operatorOf (layout: Layout) (level: Nat) (token: Parse.Located Token): Option (Expr → Expr → Expr) :=
  match token.value.kind with
    | Op operator if operator.level == level && layout.allows token => Some (Binary operator (layout.comments token))
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
      Negate (layout.comments token) (negationsFrom more self layout)
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
    | Some token if layout.allows token => (token.value.kind, layout.comments token)
    | _ => (Stray "", Comments.none)
  match fuel, next with
    | Succ more, (Sign OpenParen, open) =>
      let call := Parse.optional (() => callAfter self target open)
      suffixesAfter more self layout target call
    | Succ more, (Sign Dot, dot) =>
      let field := Parse.optional (() => fieldAfter layout target dot)
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
    | Some token if layout.allows token => atomOf self (layout.comments token) token.value.kind
    | _ => Parse.expected "an expression"

--| The atom whose first token is of `kind` and holds `comments`.
-- A function of its own so that proofs (Fmt/WalkProofs.sw) can name it; so
-- are `callAfter` and `fieldAfter`.
def atomOf (self: Layout → {Parse (Parse.Located Token)} Expr) (comments: Comments) (kind: Kind):
    {Parse (Parse.Located Token)} Expr :=
  match kind with
    | Name text =>
      skip()
      Var text comments
    | Number digits =>
      skip()
      NumberLiteral digits comments
    | Str written =>
      skip()
      StringLiteral written comments
    | Sign OpenParen =>
      skip()
      let inner := self InBrackets
      let close := sign InBrackets "')'" CloseParen
      Bracketed comments inner close
    | Sign OpenSquare =>
      skip()
      let (found, close) := items self CloseSquare
      ListLiteral comments found close
    | _ => Parse.expected "an expression"

--| A call of `target`, from its `(`, whose comments are `open`.
def callAfter (self: Layout → {Parse (Parse.Located Token)} Expr) (target: Expr) (open: Comments):
    {Parse (Parse.Located Token)} Expr :=
  skip()
  let (arguments, close) := items self CloseParen
  Call target open arguments close

--| A field of `target`, from its `.`, whose comments are `dot`.
def fieldAfter (layout: Layout) (target: Expr) (dot: Comments): {Parse (Parse.Located Token)} Expr :=
  skip()
  let (named, nameComments) := name layout
  Field target dot named nameComments

--| A list's items or a call's arguments, then `closer` and its comments;
--| the opening bracket has been read.
def items (self: Layout → {Parse (Parse.Located Token)} Expr) (closer: Punctuation):
    {Parse (Parse.Located Token)} (List Item, Comments) :=
  let closing := "'${closer.spelling}'"
  match signInBrackets closing closer with
    | Some close => ([], close)
    | None =>
      let found := itemsFrom (Parse.mark().left) self []
      let close := sign InBrackets closing closer
      (found, close)

--| The comments of the sign `wanted` if it comes next, read if it does,
--| else noted as expected: `Parse.optional (() => sign InBrackets what
--| wanted)` without the handler, since reading one token can't fail
--| halfway.
def signInBrackets (what: Text) (wanted: Punctuation): {Parse (Parse.Located Token)} Option Comments :=
  match peek() with
    | Some token if (signIs wanted token.value.kind).isSome =>
      skip()
      Some (Layout.comments InBrackets token)
    | _ =>
      Parse.note (Parse.Problem.Expected what)
      None

--| Items while each is followed by a comma, at most `fuel` more. `found`
--| is newest first.
def itemsFrom (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (found: List Item):
    {Parse (Parse.Located Token)} List Item :=
  match fuel with
    -- Reached only with no tokens left, so with nothing found: every round
    -- reads a token, and `fuel` starts as the tokens left.
    | Zero => []
    | Succ more => itemsAfter more self found (item self)

--| What `itemsFrom` does with the item it read and whether a comma followed
--| it: on to the next item after a comma, else the items found.
-- A function of its own so that proofs (ExpressionProofs.sw) can name it.
def itemsAfter (more: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (found: List Item) (read: (Item, Bool)):
    {Parse (Parse.Located Token)} List Item :=
  if read.snd then itemsFrom more self [read.fst, ..found] else [read.fst, ..found].reverse

--| An item, its comma if one follows, and whether one did.
def item (self: Layout → {Parse (Parse.Located Token)} Expr): {Parse (Parse.Located Token)} (Item, Bool) :=
  let value := self InBrackets
  let comma := signInBrackets "','" Comma
  ({ value, comma = comma.getOrElse Comments.none }, comma.isSome)

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
def inlineBody (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout):
    {Parse (Parse.Located Token)} Body :=
  let line := bareStatement self layout
  { statements = [{ blankBefore = False, line }] }

--| An expression as a statement.
def bareStatement (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout):
    {Parse (Parse.Located Token)} Statement :=
  let value := self layout
  Bare (layout.headed value)

--| The own-line comments above the expression's leftmost token.
def Expr.firstAbove: Expr → List Comment
  | Var _ comments => comments.above
  | NumberLiteral _ comments => comments.above
  | StringLiteral _ comments => comments.above
  | Bracketed open _ _ => open.above
  | ListLiteral open _ _ => open.above
  | Call callee _ _ _ => callee.firstAbove
  | Field target _ _ _ => target.firstAbove
  | Negate minus _ => minus.above
  | Binary _ _ left _ => left.firstAbove
  | If ifComments _ _ _ _ _ => ifComments.above

--| The expression with no own-line comments above its leftmost token.
def Expr.withoutFirstAbove: Expr → Expr
  | Var name comments => Var name { comments | above = [] }
  | NumberLiteral digits comments => NumberLiteral digits { comments | above = [] }
  | StringLiteral written comments => StringLiteral written { comments | above = [] }
  | Bracketed open inner close => Bracketed { open | above = [] } inner close
  | ListLiteral open items close => ListLiteral { open | above = [] } items close
  | Call callee open arguments close => Call callee.withoutFirstAbove open arguments close
  | Field target dot name nameComments => Field target.withoutFirstAbove dot name nameComments
  | Negate minus operand => Negate { minus | above = [] } operand
  | Binary operator sign left right => Binary operator sign left.withoutFirstAbove right
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    If { ifComments | above = [] } condition thenComments whenTrue elseComments whenFalse

--| An expression read as a statement or as a body's one expression, as
--| the tree keeps it. Outside brackets its first token holds no own-line
--| comments: above a statement they are the block's note lines, and a
--| body on its keyword's line has none above it. So there this changes
--| nothing the parser reads; it makes that a fact about the tree which
--| needs no account of which token was read first.
def Layout.headed (layout: Layout) (value: Expr): Expr := match layout with
  | InBrackets => value
  | InStatement _ _ => value.withoutFirstAbove

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
      let line := statementLine fuel self (InStatement column first.offset) first first.value.kind
      notedStatement first.value.above line
    | _ => Empty.absurd Parse.stop()

--| The statement whose first token, `first`, is of `kind`: a `let`, or
--| else an expression.
def statementLine (fuel: Nat) (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (first: Parse.Located Token) (kind: Kind):
    {Parse (Parse.Located Token)} Statement :=
  match kind with
    | Reserved LetKeyword =>
      skip()
      let (bound, nameComments) := name layout
      let equals := sign layout "'='" Defines
      Let (layout.comments first) bound nameComments equals (bodyFuel fuel self layout)
    | _ => bareStatement self layout

--| A statement's lines: the own-line comments in `above`, the trivia on
--| its first token, then the statement.
def notedStatement (above: List Trivia) (line: Statement): List (Spaced Statement) :=
  let (notes, blankBefore) := spacedNotes StatementNote above
  notes ++ [{ blankBefore, line }]

-- Declarations and the file.

--| A declaration starting a line at column 0, after the own-line comments
--| above it.
def declaration(): {Parse (Parse.Located Token)} List (Spaced Declaration) := match Parse.mark().rest with
  | [first, .._] if first.value.startsLine && first.value.column == 0 =>
    let parsed := declarationLine (InStatement 0 first.offset) first
    notedDeclaration first.value.above parsed
  | _ => Empty.absurd Parse.stop()

--| The declaration whose first token is `first`: `fn` or `let`.
-- A function of its own so that proofs (BlockProofs.sw) can name it; so
-- are `notedDeclaration` and `fileEnd`.
def declarationLine (layout: Layout) (first: Parse.Located Token): {Parse (Parse.Located Token)} Declaration :=
  match first.value.kind with
    | Reserved FnKeyword => functionLine layout first
    | Reserved LetKeyword => valueLine layout first
    | _ =>
      Parse.note (Parse.Problem.Literal "fn")
      Parse.note (Parse.Problem.Literal "let")
      Empty.absurd Parse.stop()

--| A function declaration, from its `fn`, the token `first`.
-- A function of its own so that proofs (Fmt/WalkProofs.sw) can name it; so
-- is `valueLine`.
def functionLine (layout: Layout) (first: Parse.Located Token): {Parse (Parse.Located Token)} Declaration :=
  skip()
  let (declared, nameComments) := name layout
  let open := sign layout "'('" OpenParen
  let parameters := parametersOf (Parse.optional parameterList)
  let close := sign InBrackets "')'" CloseParen
  let equals := sign layout "'='" Defines
  Function (layout.comments first) declared nameComments open parameters close equals (body expression layout)

--| A value declaration, from its `let`, the token `first`.
def valueLine (layout: Layout) (first: Parse.Located Token): {Parse (Parse.Located Token)} Declaration :=
  skip()
  let (declared, nameComments) := name layout
  let equals := sign layout "'='" Defines
  Value (layout.comments first) declared nameComments equals (body expression layout)

--| A header's parameters: a name, then a comma and a name as long as both
--| come, as `Parse.sepBy1` reads them but keeping each comma's comments.
def parameterList(): {Parse (Parse.Located Token)} ((Text, Comments), List (Comments, (Text, Comments))) :=
  let first := name InBrackets
  let others := Parse.many parameterStep
  (first, others)

--| A comma and the parameter after it.
def parameterStep(): {Parse (Parse.Located Token)} (Comments, (Text, Comments)) :=
  let comma := sign InBrackets "','" Comma
  let named := name InBrackets
  (comma, named)

def parametersOf (found: Option ((Text, Comments), List (Comments, (Text, Comments)))): List Parameter :=
  match found with
    | None => []
    | Some (first, others) => withCommas first others

--| Each parameter with the comments of the comma after it.
def withCommas (first: (Text, Comments)) (others: List (Comments, (Text, Comments))): List Parameter :=
  match others with
    | [] => [{ name = first.fst, comments = first.snd, comma = Comments.none }]
    | [(comma, next), ..rest] => [{ name = first.fst, comments = first.snd, comma }, ..withCommas next rest]

--| A declaration's lines: the own-line comments in `above`, the trivia on
--| its first token, then `parsed`.
def notedDeclaration (above: List Trivia) (parsed: Declaration): List (Spaced Declaration) :=
  let (notes, blankBefore) := spacedNotes DeclarationNote above
  notes ++ [{ blankBefore, line = parsed }]

--| The file, given the comments after its last token (or all of them, with
--| no tokens).
def sourceFile (endTrivia: List Trivia): {Parse (Parse.Located Token)} SourceFile :=
  let found := Parse.many declaration
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
    match Parse.whole lexed.tokens (() => sourceFile lexed.endTrivia) with
      | Ok file => Ok file
      | Err failure => Err (Parse.tokensMessage source.toList lexed.tokens failure)
