--| What the parser guarantees of where comments and blocks are
--| (`HeadedFile`, SpellProofs.sw): outside brackets no statement's,
--| declaration's or one-expression body's first token holds comments
--| above it in the tree; inside brackets every body is one expression;
--| and no body or file keeps a blank line above its first line. So the
--| spelling theorems' `Headed` hypotheses hold of every parsed tree and
--| needn't be checked. This file has the property's own facts; the walk
--| over the parser (`parseHeaded`) is WalkProofs.sw.
--|
--| The first-token facts need no account of the tokens read:
--| `bareStatement` clears the comments on the tree it built
--| (`Layout.headed`), and a `let` or `fn` takes its keyword's comments at
--| the statement's own start, where `Layout.comments` gives none above.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, NonEmptyList, Option, Parse, Result, Text, Void)

--| `HeadedExpr` of an expression read at `layout`.
def HeadedAt (layout: Layout) (expr: Expr): Prop := HeadedExpr (bracketedOf layout) expr

--| `HeadedBody` of a body read at `layout`.
def HeadedBodyAt (layout: Layout) (found: Body): Prop := HeadedBody (bracketedOf layout) found

-- Clearing.

theorem clearedFirstAbove ∀ (expr: Expr): expr.withoutFirstAbove.firstAbove = [] := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ => byComputing
  | Call callee _ _ _ => clearedFirstAbove callee
  | Field target _ _ _ => clearedFirstAbove target
  | Negate _ _ => byComputing
  | Binary _ _ left _ => clearedFirstAbove left
  | If _ _ _ _ _ _ => byComputing

theorem headedCleared ∀ (bracketed: Bool) (expr: Expr)
    (headed: HeadedExpr bracketed expr):
    HeadedExpr bracketed expr.withoutFirstAbove :=
  match expr, headed with
    | Var name comments, headed => headed
    | NumberLiteral digits comments, headed => headed
    | StringLiteral written comments, headed => headed
    | Bracketed open inner close, headed => headed
    | ListLiteral open items close, headed => headed
    | Call callee open arguments close, Both calleeHeaded others =>
      ((headedCleared bracketed callee calleeHeaded), others)
    | Field target dot name nameComments, headed => headedCleared bracketed target headed
    | Negate minus operand, headed => headed
    | Binary operator sign left right, Both leftHeaded rightHeaded =>
      ((headedCleared bracketed left leftHeaded), rightHeaded)
    | If ifComments condition thenComments whenTrue elseComments whenFalse, headed => headed

--| A statement that is an expression.
def IsBare: Statement → Prop
  | Bare _ => True
  | _ => False

--| What `bareStatement` gives at a layout inside brackets or not.
def BareHeaded (bracketed: Bool) (line: Statement): Prop := HeadedStatement bracketed line ∧ IsBare line

theorem headedBare ∀ (layout: Layout) (value: Expr)
    (headed: HeadedAt layout value):
    BareHeaded (bracketedOf layout) (Bare (layout.headed value)) :=
  match layout, headed with
    | InBrackets, headed => ((((never => (Bool.trueNotFalse never).impossible), headed)), byComputing)
    | InStatement column start, headed =>
      ((((outside => clearedFirstAbove value), (headedCleared False value headed))), byComputing)

-- Items.

theorem headedItemsAppend ∀ (front: List Item) (last: Item)
    (headed: HeadedItems front)
    (lastHeaded: HeadedExpr True last.value):
    HeadedItems (front ++ [last]) :=
  match front, headed, last, lastHeaded with
    | [], headed, { value, comma }, lastHeaded => (lastHeaded, byComputing)
    | [{ value, comma }, ..rest], Both valueHeaded restHeaded, last, lastHeaded =>
      (valueHeaded, (headedItemsAppend rest last restHeaded lastHeaded))

theorem headedItemsReverse ∀ (found: List Item) (headed: HeadedItems found): HeadedItems found.reverse :=
  match found, headed with
    | [], headed => byComputing
    | [{ value, comma }, ..rest], Both valueHeaded restHeaded =>
      rewrite List.reverseCons ({ value, comma }: Item) rest then
        headedItemsAppend rest.reverse { value, comma } (headedItemsReverse rest restHeaded) valueHeaded

def HeadedItem (read: (Item, Bool)): Prop := HeadedExpr True read.fst.value

-- Atoms and their calls and fields.

-- Operator chains.

theorem headedStep ∀ (layout: Layout) (lowest highest level: Nat) (associativity: Parse.Associativity)
    (combine: Expr → Expr → Expr) (item: Parse.Located Token) (left right: Expr)
    (found: Parse.operatorFrom item 0 (operatorLevels layout) = Some (level, associativity, combine))
    (above: lowest ≤ level)
    (below: level ≤ highest)
    (leftHeaded: HeadedAt layout left)
    (rightHeaded: HeadedAt layout right):
    HeadedAt layout (combine left right) :=
  let shape := operatorShape layout item
  let known := rewrite found at shape then shape
  match known with
    | Witness operator (Witness comments (Both isBinary others)) => rewrite isBinary then (leftHeaded, rightHeaded)

-- Bodies and blocks.

theorem headedLinesAppend ∀ (bracketed: Bool) (front back: List (Spaced Statement))
    (frontHeaded: HeadedLines bracketed front)
    (backHeaded: HeadedLines bracketed back):
    HeadedLines bracketed (front ++ back) :=
  match front, frontHeaded with
    | [], frontHeaded => backHeaded
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded =>
      (lineHeaded, (headedLinesAppend bracketed rest back restHeaded backHeaded))

theorem headedNotes ∀ (trivia: List Trivia) (found: (List (Spaced Statement), Bool))
    (headed: HeadedLines False found.fst):
    HeadedLines False (trivia.foldLeft found (noteStep StatementNote)).fst :=
  match trivia with
    | [] => headed
    | [BlankLine, ..rest] => headedNotes rest (noteStep StatementNote found BlankLine) headed
    | [OwnLine comment, ..rest] =>
      headedNotes rest
        (noteStep StatementNote found (OwnLine comment))
        (headedLinesAppend False found.fst
          [{ blankBefore = found.snd, line = StatementNote comment }]
          headed
          ((byComputing, byComputing)))

--| A statement's lines, the notes above it and itself.
theorem headedNoted ∀ (above: List Trivia) (line: Statement)
    (headed: HeadedStatement False line):
    HeadedLines False (notedStatement above line) :=
  let notesHeaded: HeadedLines False (spacedNotes StatementNote above).fst := headedNotes above ([], False) byComputing
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => headedLinesAppend False notes [{ blankBefore, line }] notesHeaded ((headed, byComputing))

theorem headedWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (headed: HeadedLines False lines):
    HeadedLines False (withoutFirstBlank lines) :=
  match lines, headed with
    | [], headed => byComputing
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded => (lineHeaded, restHeaded)

--| `withoutFirstBlank` leaves no blank line above the first line.
theorem unspacedWithout ∀ (lines: List (Spaced a)): Unspaced (withoutFirstBlank lines) := match lines with
  | [] => byComputing
  | [{ blankBefore, line }, ..rest] => byComputing

theorem headedConcat ∀ (groups: List (List (Spaced Statement)))
    (all: List.All (HeadedLines False) groups):
    HeadedLines False groups.concat :=
  match groups, all with
    | [], all => byComputing
    | [first, ..rest], Both firstHeaded restHeaded =>
      headedLinesAppend False first rest.concat firstHeaded (headedConcat rest restHeaded)

-- `if`, and the expression parser.

-- Declarations and the file.

theorem headedDeclarationsAppend ∀ (front back: List (Spaced Declaration))
    (frontHeaded: HeadedDeclarations front)
    (backHeaded: HeadedDeclarations back):
    HeadedDeclarations (front ++ back) :=
  match front, frontHeaded with
    | [], frontHeaded => backHeaded
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded =>
      (lineHeaded, (headedDeclarationsAppend rest back restHeaded backHeaded))

theorem headedDeclarationNotes ∀ (trivia: List Trivia) (found: (List (Spaced Declaration), Bool))
    (headed: HeadedDeclarations found.fst):
    HeadedDeclarations (trivia.foldLeft found (noteStep DeclarationNote)).fst :=
  match trivia with
    | [] => headed
    | [BlankLine, ..rest] => headedDeclarationNotes rest (noteStep DeclarationNote found BlankLine) headed
    | [OwnLine comment, ..rest] =>
      headedDeclarationNotes rest
        (noteStep DeclarationNote found (OwnLine comment))
        (headedDeclarationsAppend found.fst
          [{ blankBefore = found.snd, line = DeclarationNote comment }]
          headed
          ((byComputing, byComputing)))

theorem headedNotedDeclaration ∀ (above: List Trivia) (line: Declaration)
    (headed: HeadedDeclaration line):
    HeadedDeclarations (notedDeclaration above line) :=
  let notesHeaded: HeadedDeclarations (spacedNotes DeclarationNote above).fst :=
    headedDeclarationNotes above ([], False) byComputing
  match found: spacedNotes DeclarationNote above with
    | (notes, blankBefore) => headedDeclarationsAppend notes [{ blankBefore, line }] notesHeaded ((headed, byComputing))

theorem headedDeclarationsWithoutFirstBlank ∀ (lines: List (Spaced Declaration))
    (headed: HeadedDeclarations lines):
    HeadedDeclarations (withoutFirstBlank lines) :=
  match lines, headed with
    | [], headed => byComputing
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded => (lineHeaded, restHeaded)

theorem headedDeclarationsConcat ∀ (groups: List (List (Spaced Declaration)))
    (all: List.All HeadedDeclarations groups):
    HeadedDeclarations groups.concat :=
  match groups, all with
    | [], all => byComputing
    | [first, ..rest], Both firstHeaded restHeaded =>
      headedDeclarationsAppend first rest.concat firstHeaded (headedDeclarationsConcat rest restHeaded)

theorem headedFileOf ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (headed: HeadedDeclarations declarations):
    HeadedFile (fileOf declarations endTrivia) :=
  let notesHeaded: HeadedDeclarations (spacedNotes DeclarationNote endTrivia).fst :=
    headedDeclarationNotes endTrivia ([], False) byComputing
  match found: spacedNotes DeclarationNote endTrivia with
    | (endNotes, blank) => (
      (headedDeclarationsWithoutFirstBlank
        (declarations ++ endNotes)
        (headedDeclarationsAppend declarations endNotes headed notesHeaded)),
      (unspacedWithout (declarations ++ endNotes))
    )
