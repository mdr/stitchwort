--| The parser copies the lexer's texts. Given tokens whose texts are the
--| lexer's (`Good`: each name a word that spells no keyword, each number
--| digits, each string closed, each comment a comment), every tree the
--| parser gives is `Lexical`: its names, numbers, strings and comments
--| are those tokens', and its bodies end in statements. This file has the
--| property's own facts about tokens and trees; the walk over the parser
--| that proves `LexicalFile` of every parsed file (`parseLexical`) is
--| WalkProofs.sw, under `Parse.Invariant.every Good`.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std.Parse.Associativity (LeftAssociative)
import Std (And, Bool, Eq, List, NonEmptyList, Option, Pair, Parse, Result, Text, Void)

--| A kind whose text is what the printer's rules need of it.
def GoodKind: Kind → Prop
  | Name text => IsName text
  | Number digits => IsDigits digits
  | Str written => IsString written
  | _ => True

--| A token with the lexer's texts: its kind's, and its comments'.
def Good (token: Parse.Located Token): Prop :=
  GoodKind token.value.kind ∧ FineTrivia token.value.above ∧ FineTrailing token.value.trailing

-- A token's comments, as the tree keeps them.

theorem fineAbove ∀ (trivia: List Trivia) (fine: FineTrivia trivia): FineAbove (ownLineComments trivia) :=
  match trivia, fine with
    | [], _ => byComputing
    | [OwnLine comment, ..rest], Both isComment others => (isComment, (fineAbove rest others))
    | [BlankLine, ..rest], others => fineAbove rest others

theorem fineAfter ∀ (trailing: Option (Parse.Located Comment))
    (fine: FineTrailing trailing):
    FineAfter (trailing.map (comment => comment.value)) :=
  match trailing, fine with
    | None, _ => byComputing
    | Some comment, isComment => isComment

--| The comments the tree keeps of a good token are comments.
theorem fineComments ∀ (layout: Layout) (token: Parse.Located Token) (good: Good token): Fine (layout.comments token) :=
  match layout with
    | InBrackets => ((fineAbove token.value.above good.right.left), (fineAfter token.value.trailing good.right.right))
    | InStatement column start =>
      match same: token.offset == start with
        | True => (byComputing, (fineAfter token.value.trailing good.right.right))
        | False => ((fineAbove token.value.above good.right.left), (fineAfter token.value.trailing good.right.right))

theorem selectedComments ∀ (layout: Layout) (select: Kind → Option a) (token: Parse.Located Token) (comments: Comments)
    (selected: selectComments layout select token = Some comments):
    comments = layout.comments token :=
  match allowed: layout.allows token with
    | True =>
      match found: select token.value.kind with
        | Some value => (Option.someInjective selected).flipped

--| A name and its comments, as the tree keeps them.
def FineNamed (named: (Text, Comments)): Prop := IsName named.fst ∧ Fine named.snd

theorem selectedName ∀ (layout: Layout) (token: Parse.Located Token) (named: (Text, Comments))
    (goodKind: GoodKind token.value.kind)
    (fine: Fine (layout.comments token))
    (selected: selectWithComments layout nameOf token = Some named):
    FineNamed named :=
  match allowed: layout.allows token with
    | True =>
      match kind: token.value.kind with
        | Name text => rewrite <- Option.someInjective selected then (goodKind, fine)

-- Items.

theorem lexicalItemsAppend ∀ (front: List Expr) (last: Expr)
    (lexical: LexicalItems front)
    (lastLexical: Lexical last):
    LexicalItems (front ++ [last]) :=
  match front, lexical with
    | [], lexical => (lastLexical, byComputing)
    | [value, ..rest], Both valueLexical restLexical =>
      (valueLexical, (lexicalItemsAppend rest last restLexical lastLexical))

theorem lexicalItemsReverse ∀ (found: List Expr) (lexical: LexicalItems found): LexicalItems found.reverse :=
  match found, lexical with
    | [], lexical => byComputing
    | [value, ..rest], Both valueLexical restLexical =>
      rewrite List.reverseCons value rest then
        lexicalItemsAppend rest.reverse value (lexicalItemsReverse rest restLexical) valueLexical

--| Items and the closing bracket's comments, all the lexer's.
def LexicalList (found: (List Expr, Comments)): Prop := LexicalItems found.fst ∧ Fine found.snd

-- Atoms and their calls and fields.

-- Operator chains.

--| What `operatorLevels` finds for a token, if anything: a `Binary` that
--| holds the token's comments.
def OperatorCarries (layout: Layout) (token: Parse.Located Token):
    Option (Nat, Parse.Associativity, Expr → Expr → Expr) → Prop
  | None => True
  | Some (level, associativity, combine) => ∃ (operator: Operator) => combine = Binary operator (layout.comments token)

theorem operatorCarries ∀ (layout: Layout) (token: Parse.Located Token):
    OperatorCarries layout token (Parse.operatorFrom token 0 (operatorLevels layout)) :=
  match operatorOfKinds layout token with
    | Inl none => rewrite none 1, none 2, none 3, none 4, none 5, none 6
    | Inr (Witness operator (Both kind allowed)) =>
      rewrite operatorFound layout token operator kind allowed then (operator, byComputing)

--| An operator read between two expressions with the lexer's texts makes
--| one: its comments are its token's.
theorem lexicalStep ∀ (layout: Layout) (lowest highest level: Nat) (associativity: Parse.Associativity)
    (combine: Expr → Expr → Expr) (item: Parse.Located Token) (left right: Expr)
    (good: Good item)
    (found: Parse.operatorFrom item 0 (operatorLevels layout) = Some (level, associativity, combine))
    (above: lowest ≤ level)
    (below: level ≤ highest)
    (leftLexical: Lexical left)
    (rightLexical: Lexical right):
    Lexical (combine left right) :=
  let carried := operatorCarries layout item
  let known := rewrite found at carried then carried
  match known with
    | Witness operator isBinary => rewrite isBinary then ((fineComments layout item good), leftLexical, rightLexical)

theorem fineCleared ∀ (comments: Comments) (fine: Fine comments): Fine { comments | above = [] } :=
  Both byComputing fine.right

--| Clearing the comments above the first token keeps the lexer's texts.
theorem lexicalCleared ∀ (expr: Expr) (lexical: Lexical expr): Lexical expr.withoutFirstAbove :=
  match expr, lexical with
    | Var name comments, Both isName fine => (isName, (fineCleared comments fine))
    | NumberLiteral digits comments, Both isDigits fine => (isDigits, (fineCleared comments fine))
    | StringLiteral written comments, Both isString fine => (isString, (fineCleared comments fine))
    | Bracketed open inner close, Both fine others => ((fineCleared open fine), others)
    | ListLiteral open items trailingComma close, Both fine others => ((fineCleared open fine), others)
    | Call callee open arguments trailingComma close, Both lexicalCallee others =>
      ((lexicalCleared callee lexicalCallee), others)
    | Field target dot name nameComments, Both lexicalTarget others => ((lexicalCleared target lexicalTarget), others)
    | Negate minus operand, Both fine others => ((fineCleared minus fine), others)
    | Binary operator sign left right, Both fine (Both lexicalLeft lexicalRight) =>
      (fine, (lexicalCleared left lexicalLeft), lexicalRight)
    | If ifComments condition thenComments whenTrue elseComments whenFalse, Both fine others =>
      ((fineCleared ifComments fine), others)

theorem lexicalHeaded ∀ (layout: Layout) (expr: Expr) (lexical: Lexical expr): Lexical (layout.headed expr) :=
  match layout with
    | InBrackets => lexical
    | InStatement column start => lexicalCleared expr lexical

-- Bodies and blocks.

--| A statement with the lexer's texts that isn't a comment line.
def CodedLexical (line: Statement): Prop := LexicalStatement line ∧ Coded line

theorem lexicalLinesAppend ∀ (front back: List (Spaced Statement))
    (frontLexical: LexicalLines front)
    (backLexical: LexicalLines back):
    LexicalLines (front ++ back) :=
  match front, frontLexical with
    | [], frontLexical => backLexical
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical =>
      (lineLexical, (lexicalLinesAppend rest back restLexical backLexical))

theorem lexicalNotes ∀ (trivia: List Trivia) (found: (List (Spaced Statement), Bool))
    (fine: FineTrivia trivia)
    (lexical: LexicalLines found.fst):
    LexicalLines (trivia.foldLeft found (noteStep StatementNote)).fst :=
  match trivia, fine with
    | [], _ => lexical
    | [BlankLine, ..rest], others => lexicalNotes rest (noteStep StatementNote found BlankLine) others lexical
    | [OwnLine comment, ..rest], Both isComment others =>
      lexicalNotes rest
        (noteStep StatementNote found (OwnLine comment))
        others
        (lexicalLinesAppend found.fst
          [{ blankBefore = found.snd, line = StatementNote comment }]
          lexical
          ((isComment, byComputing)))

--| A statement's lines, the notes above it and itself, have the lexer's
--| texts when it has and the trivia above it are the lexer's.
theorem lexicalNoted ∀ (above: List Trivia) (line: Statement)
    (fine: FineTrivia above)
    (lexical: LexicalStatement line):
    LexicalLines (notedStatement above line) :=
  let notesLexical: LexicalLines (spacedNotes StatementNote above).fst :=
    lexicalNotes above ([], False) fine byComputing
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => lexicalLinesAppend notes [{ blankBefore, line }] notesLexical ((lexical, byComputing))

theorem lexicalWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (lexical: LexicalLines lines):
    LexicalLines (withoutFirstBlank lines) :=
  match lines, lexical with
    | [], lexical => byComputing
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical => (lineLexical, restLexical)

--| Lines with the lexer's texts that end in a statement.
def ClosedLexical (lines: List (Spaced Statement)): Prop := LexicalLines lines ∧ ClosedLines lines

theorem lexicalConcat ∀ (groups: List (List (Spaced Statement)))
    (all: List.All ClosedLexical groups):
    LexicalLines groups.concat :=
  match groups, all with
    | [], all => byComputing
    | [first, ..rest], Both (Both firstLexical _) restLexical =>
      lexicalLinesAppend first rest.concat firstLexical (lexicalConcat rest restLexical)

-- `if`, and the expression parser.

-- Declarations and the file.

--| A closing bracket's comments, as the parser builds them from the
--| lexer's, are comments.
theorem closingFine ∀ (close: Comments) (before: Bool) (fine: Fine close): Fine (close.closing before) :=
  match close, before, fine with
    | { above, after = None }, _, fine => fine
    | { above = [], after = Some comment }, False, (_, fineAfter) => (((fineAfter, byComputing)), byComputing)
    | { above = [], after = Some comment }, True, fine => fine
    | { above = [first, ..rest], after = Some comment }, _, fine => fine

--| A type of the parser's shape, with the lexer's texts.
def ParsedType (annotation: TypeExpr): Prop := ShapedType annotation ∧ LexicalType annotation

--| A parameter group of the parser's shape, with the lexer's texts.
def ParsedGroup (group: ParameterGroup): Prop := ShapedGroup group ∧ LexicalGroup group

--| A first group and the groups after it.
--| The trailing comma's flag says nothing about the groups.
def FineList (found: (ParameterGroup, List ParameterGroup, Bool)): Prop :=
  ParsedGroup found.fst ∧ List.All ParsedGroup found.snd.fst

theorem parsedGroups ∀ (groups: List ParameterGroup)
    (all: List.All ParsedGroup groups):
    ShapedGroups groups ∧ LexicalParameters groups :=
  match groups, all with
    | [], _ => (byComputing, byComputing)
    | [group, ..rest], Both (Both shaped lexical) more =>
      let (shapedRest, lexicalRest) := parsedGroups rest more
      (((shaped, shapedRest)), ((lexical, lexicalRest)))

theorem lexicalNamesOf ∀ (others: List (Text, Comments))
    (named: List.All FineNamed others):
    LexicalNames (others.map namedOf) :=
  match others, named with
    | [], _ => byComputing
    | [found, ..rest], Both fine more => (fine, (lexicalNamesOf rest more))

theorem lexicalDeclarationsAppend ∀ (front back: List (Spaced Declaration))
    (frontLexical: LexicalDeclarations front)
    (backLexical: LexicalDeclarations back):
    LexicalDeclarations (front ++ back) :=
  match front, frontLexical with
    | [], frontLexical => backLexical
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical =>
      (lineLexical, (lexicalDeclarationsAppend rest back restLexical backLexical))

theorem lexicalDeclarationNotes ∀ (trivia: List Trivia) (found: (List (Spaced Declaration), Bool))
    (fine: FineTrivia trivia)
    (lexical: LexicalDeclarations found.fst):
    LexicalDeclarations (trivia.foldLeft found (noteStep DeclarationNote)).fst :=
  match trivia, fine with
    | [], _ => lexical
    | [BlankLine, ..rest], others =>
      lexicalDeclarationNotes rest (noteStep DeclarationNote found BlankLine) others lexical
    | [OwnLine comment, ..rest], Both isComment others =>
      lexicalDeclarationNotes rest
        (noteStep DeclarationNote found (OwnLine comment))
        others
        (lexicalDeclarationsAppend found.fst
          [{ blankBefore = found.snd, line = DeclarationNote comment }]
          lexical
          ((isComment, byComputing)))

theorem lexicalNotedDeclaration ∀ (above: List Trivia) (line: Declaration)
    (fine: FineTrivia above)
    (lexical: LexicalDeclaration line):
    LexicalDeclarations (notedDeclaration above line) :=
  let notesLexical: LexicalDeclarations (spacedNotes DeclarationNote above).fst :=
    lexicalDeclarationNotes above ([], False) fine byComputing
  match found: spacedNotes DeclarationNote above with
    | (notes, blankBefore) =>
      lexicalDeclarationsAppend notes [{ blankBefore, line }] notesLexical ((lexical, byComputing))

theorem lexicalDeclarationsWithoutFirstBlank ∀ (lines: List (Spaced Declaration))
    (lexical: LexicalDeclarations lines):
    LexicalDeclarations (withoutFirstBlank lines) :=
  match lines, lexical with
    | [], lexical => byComputing
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical => (lineLexical, restLexical)

theorem lexicalDeclarationsConcat ∀ (groups: List (List (Spaced Declaration)))
    (all: List.All LexicalDeclarations groups):
    LexicalDeclarations groups.concat :=
  match groups, all with
    | [], all => byComputing
    | [first, ..rest], Both firstLexical restLexical =>
      lexicalDeclarationsAppend first rest.concat firstLexical (lexicalDeclarationsConcat rest restLexical)

theorem lexicalFileOf ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (fine: FineTrivia endTrivia)
    (lexical: LexicalDeclarations declarations):
    LexicalFile (fileOf declarations endTrivia) :=
  let notesLexical: LexicalDeclarations (spacedNotes DeclarationNote endTrivia).fst :=
    lexicalDeclarationNotes endTrivia ([], False) fine byComputing
  match found: spacedNotes DeclarationNote endTrivia with
    | (endNotes, blank) =>
      lexicalDeclarationsWithoutFirstBlank
        (declarations ++ endNotes)
        (lexicalDeclarationsAppend declarations endNotes lexical notesLexical)

-- From the source.

theorem goodKind ∀ (kind: Kind) (fine: FineKind kind): GoodKind kind := match kind, fine with
  | Name text, isName => isName
  | Number digits, isDigits => isDigits
  | Str written, read => stringReadClosed written read
  | _, _ => cases

--| The lexer's tokens are good ones.
theorem goodTokens ∀ (tokens: List (Parse.Located Token)) (fine: FineTokens tokens): List.All Good tokens :=
  match tokens, fine with
    | [], _ => ()
    | [token, ..rest], Both (Both kind (Both above trailing)) others =>
      ((((goodKind token.value.kind kind), above, trailing)), (goodTokens rest others))
