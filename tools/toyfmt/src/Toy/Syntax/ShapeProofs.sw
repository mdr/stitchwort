--| The parser's shape, as a property of trees: every expression of the
--| shape `Shaped` describes (operators grouped by precedence, a call's
--| callee and a field's target postfix, `-` before an operand), every body
--| ending in a statement, every closing bracket holding only a trailing
--| comment rule N leaves there (`ShapedFile`). These are the property's own facts, about the
--| values the parser builds; the walk over the parser that proves every
--| parsed file `ShapedFile` (`parseShaped`) is Fmt/WalkProofs.sw, with
--| the other two properties of parsed trees.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std.Parse.Associativity (LeftAssociative)
import Std (Bool, Eq, List, NonEmptyList, Option, Parse, Result, Text, Void)

-- Items.

theorem shapedItemsAppend ∀ (front: List Expr) (last: Expr)
    (shaped: ShapedItems front)
    (lastShaped: Shaped last):
    ShapedItems (front ++ [last]) :=
  match front, shaped with
    | [], shaped => (lastShaped, byComputing)
    | [value, ..rest], Both valueShaped restShaped => (valueShaped, (shapedItemsAppend rest last restShaped lastShaped))

theorem shapedItemsReverse ∀ (found: List Expr) (shaped: ShapedItems found): ShapedItems found.reverse :=
  match found, shaped with
    | [], shaped => byComputing
    | [value, ..rest], Both valueShaped restShaped =>
      rewrite List.reverseCons value rest then
        shapedItemsAppend rest.reverse value (shapedItemsReverse rest restShaped) valueShaped

--| An item of the parser's shape, and whether a comma followed it.
def ShapedItem (read: (Expr, Bool)): Prop := Shaped read.fst

-- Atoms and their calls and fields.

--| A postfix expression of the parser's shape: what `atom` and
--| `suffixesFrom` give.
def PostfixShaped (expr: Expr): Prop := expr.isPostfix = True ∧ Shaped expr

--| An operand of the parser's shape: what `operand` gives.
def OperandShaped (expr: Expr): Prop := expr.isOperand = True ∧ Shaped expr

theorem postfixIsOperand ∀ (expr: Expr) (postfix: expr.isPostfix = True): expr.isOperand = True := cases

theorem operandIsChain ∀ (expr: Expr) (operand: expr.isOperand = True): expr.isChain = True := cases

theorem operandLevel ∀ (expr: Expr) (isOperand: expr.isOperand = True): expr.chainLevel = 7 :=
  match expr, isOperand with | _, _ => cases

-- Operator chains.

--| What `Parse.operators` gives for operators of level `lowest` (counted
--| from 0) or tighter: a chain of the parser's shape whose outermost
--| operator, if it has one, is of such a level.
def Grouped (lowest: Nat) (expr: Expr): Prop :=
  Shaped expr ∧ expr.isChain = True ∧ (expr.isOperand = True ∨ lowest < expr.chainLevel)

--| What `Parse.operators` holds on its left while it reads operators of
--| levels `lowest` to `highest`: a chain whose outermost operator, if it
--| has one, is no looser than either.
def Chained (lowest highest: Nat) (expr: Expr): Prop :=
  Shaped expr ∧ expr.isChain = True ∧ (expr.isOperand = True ∨ (lowest < expr.chainLevel ∧ highest < expr.chainLevel))

--| What `operatorLevels` finds for a token, if anything: an operator's
--| `Binary`, at the place of its level, chaining from the left.
def OperatorShape: Option (Nat, Parse.Associativity, Expr → Expr → Expr) → Prop
  | None => True
  | Some (level, associativity, combine) =>
    ∃ (operator: Operator) => ∃ (comments: Comments) => combine = Binary operator comments
      ∧ operator.level = level + 1
      ∧ associativity = LeftAssociative

--| A token is an operator the layout allows, or no level takes it.
theorem operatorOfKinds ∀ (layout: Layout) (token: Parse.Located Token):
    (∀ (level: Nat) => operatorOf layout level token = None)
      ∨ (∃ (operator: Operator) => token.value.kind = Op operator ∧ layout.allows token = True) :=
  match kind: token.value.kind with
    | Op operator =>
      match allowed: layout.allows token with
        | True => Inr ((operator, byComputing, byComputing))
        | False => Inl (level =>
          match same: operator.level == level with
            | True => byComputing
            | False => byComputing)
    | Name text => Inl (level => byComputing)
    | Number digits => Inl (level => byComputing)
    | Str written => Inl (level => byComputing)
    | Reserved keyword => Inl (level => byComputing)
    | Sign punctuation => Inl (level => byComputing)
    | Stray text => Inl (level => byComputing)

theorem operatorShape ∀ (layout: Layout) (token: Parse.Located Token):
    OperatorShape (Parse.operatorFrom token 0 (operatorLevels layout)) :=
  match operatorOfKinds layout token with
    | Inl none => rewrite none 1, none 2, none 3, none 4, none 5, none 6
    | Inr (Witness operator (Both kind allowed)) =>
      rewrite operatorFound layout token operator kind allowed then
        (operator, (layout.comments token), byComputing, (arithmetic [(levelRange operator).left]), byComputing)

--| An operator read after a chain, with its right side grouped tighter,
--| makes a chain of the parser's shape.
theorem chainStep ∀ (layout: Layout) (lowest highest level: Nat) (associativity: Parse.Associativity)
    (combine: Expr → Expr → Expr) (item: Parse.Located Token) (left right: Expr)
    (found: Parse.operatorFrom item 0 (operatorLevels layout) = Some (level, associativity, combine))
    (above: lowest ≤ level)
    (below: level ≤ highest)
    (chained: Chained lowest highest left)
    (grouped: Grouped (Parse.nextLowest associativity level) right):
    Chained lowest level (combine left right) :=
  let shape := operatorShape layout item
  let known := rewrite found at shape then shape
  match known with
    | Witness operator (Witness comments (Both isBinary (Both level1 isLeft))) =>
      let groupedLeft: Grouped (level + 1) right := rewrite isLeft at grouped then grouped
      let leftBound: operator.level ≤ left.chainLevel := match chained.right.right with
        | Inl isOperand => arithmetic [operandLevel left isOperand, (levelRange operator).right]
        | Inr both => arithmetic [both.right, below, level1]
      let rightBound: operator.level < right.chainLevel := match groupedLeft.right.right with
        | Inl isOperand => arithmetic [operandLevel right isOperand, (levelRange operator).right]
        | Inr low => arithmetic [low, level1]
      rewrite isBinary then
        (
          ((leftBound, rightBound, chained.right.left, groupedLeft.right.left, chained.left, groupedLeft.left)),
          byComputing,
          (Inr (((arithmetic [above, level1]), (arithmetic [level1]))))
        )

-- Bodies and blocks.

--| A statement of the parser's shape that isn't a comment line.
def CodedShaped (line: Statement): Prop := ShapedStatement line ∧ Coded line

theorem shapedLinesAppend ∀ (front back: List (Spaced Statement))
    (frontShaped: ShapedLines front)
    (backShaped: ShapedLines back):
    ShapedLines (front ++ back) :=
  match front, frontShaped with
    | [], frontShaped => backShaped
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped =>
      (lineShaped, (shapedLinesAppend rest back restShaped backShaped))

theorem shapedNotes ∀ (trivia: List Trivia) (found: (List (Spaced Statement), Bool))
    (shaped: ShapedLines found.fst):
    ShapedLines (trivia.foldLeft found (noteStep StatementNote)).fst :=
  match trivia with
    | [] => shaped
    | [BlankLine, ..rest] => shapedNotes rest (noteStep StatementNote found BlankLine) shaped
    | [OwnLine comment, ..rest] =>
      shapedNotes rest
        (noteStep StatementNote found (OwnLine comment))
        (shapedLinesAppend found.fst
          [{ blankBefore = found.snd, line = StatementNote comment }]
          shaped
          ((byComputing, byComputing)))

--| A statement's lines, the notes above it and itself, are of the
--| parser's shape when it is.
theorem shapedNoted ∀ (above: List Trivia) (line: Statement)
    (shaped: ShapedStatement line):
    ShapedLines (notedStatement above line) :=
  let notesShaped: ShapedLines (spacedNotes StatementNote above).fst := shapedNotes above ([], False) byComputing
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => shapedLinesAppend notes [{ blankBefore, line }] notesShaped ((shaped, byComputing))

theorem closedCons ∀ (first: Spaced Statement) (lines: List (Spaced Statement))
    (closed: ClosedLines lines):
    ClosedLines [first, ..lines] :=
  match lines, closed with
    | [], never => (Bool.falseNotTrue never).impossible
    | [next, ..more], closed => closed

--| Lines before lines that end in a statement end in it too.
theorem closedAppend ∀ (front back: List (Spaced Statement)) (closed: ClosedLines back): ClosedLines (front ++ back) :=
  match front with
    | [] => closed
    | [first, ..rest] => closedCons first (rest ++ back) (closedAppend rest back closed)

--| A statement's lines end in the statement, whatever notes are above
--| it.
theorem closedNoted ∀ (above: List Trivia) (line: Statement)
    (coded: Coded line):
    ClosedLines (notedStatement above line) :=
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => closedAppend notes [{ blankBefore, line }] coded

theorem closedWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (closed: ClosedLines lines):
    ClosedLines (withoutFirstBlank lines) :=
  match lines, closed with
    | [], never => (Bool.falseNotTrue never).impossible
    | [{ blankBefore, line }], coded => coded
    | [{ blankBefore, line }, next, ..rest], closed => closed

theorem shapedWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (shaped: ShapedLines lines):
    ShapedLines (withoutFirstBlank lines) :=
  match lines, shaped with
    | [], shaped => byComputing
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped => (lineShaped, restShaped)

--| Lines of the parser's shape that end in a statement.
def ClosedShaped (lines: List (Spaced Statement)): Prop := ShapedLines lines ∧ ClosedLines lines

theorem shapedConcat ∀ (groups: List (List (Spaced Statement)))
    (all: List.All ClosedShaped groups):
    ShapedLines groups.concat :=
  match groups, all with
    | [], all => byComputing
    | [first, ..rest], Both (Both firstShaped _) restShaped =>
      shapedLinesAppend first rest.concat firstShaped (shapedConcat rest restShaped)

--| Groups of lines that each end in a statement, one after another, end
--| in a statement.
theorem closedConcat ∀ (first: List (Spaced Statement)) (rest: List (List (Spaced Statement)))
    (all: List.All ClosedShaped [first, ..rest]):
    ClosedLines [first, ..rest].concat :=
  match rest, all with
    | [], (((_, closed)), _) => rewrite List.appendNil first then closed
    | [second, ..more], (_, others) => closedAppend first [second, ..more].concat (closedConcat second more others)

-- `if`, and the expression parser.

-- Declarations and the file.

--| A type whose closing brackets hold what rule N leaves on one.
def ShapedType: TypeExpr → Prop
  | TypeName _ _ => True
  | TypeBracketed _ inner close => ShapedType inner ∧ settledCloser inner.endsWithComment close = True

def ShapedGroup: ParameterGroup → Prop
  | Untyped _ => True
  | Typed _ _ annotation => ShapedType annotation

def ShapedGroups: List ParameterGroup → Prop
  | [] => True
  | [group, ..rest] => ShapedGroup group ∧ ShapedGroups rest

--| A function's parameters between `open` and `close`: each type's
--| closing brackets, and the list's own, hold what rule N leaves on one.
def ShapedParameters (open: Comments) (parameters: List ParameterGroup) (close: Comments): Prop :=
  ShapedGroups parameters ∧ settledCloser (groupsEndWithComment open parameters) close = True

--| Each expression in the declaration is of the parser's shape, and a
--| function's parameters are (`ShapedParameters`).
def ShapedDeclaration: Declaration → Prop
  | Function _ _ _ _ open parameters trailingComma close _ found =>
    ShapedParameters open parameters close ∧ ShapedBody found
  | Value _ _ _ _ found => ShapedBody found
  | DeclarationNote _ => True

def ShapedDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => ShapedDeclaration line ∧ ShapedDeclarations rest

--| Each expression in the file is of the parser's shape, each body ends
--| in a statement, and each closing bracket holds what rule N leaves on
--| one (`settledCloser`).
def ShapedFile: SourceFile → Prop
  | { declarations } => ShapedDeclarations declarations

theorem declarationsAppend ∀ (front back: List (Spaced Declaration))
    (frontShaped: ShapedDeclarations front)
    (backShaped: ShapedDeclarations back):
    ShapedDeclarations (front ++ back) :=
  match front, frontShaped with
    | [], frontShaped => backShaped
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped =>
      (lineShaped, (declarationsAppend rest back restShaped backShaped))

theorem declarationNotes ∀ (trivia: List Trivia) (found: (List (Spaced Declaration), Bool))
    (shaped: ShapedDeclarations found.fst):
    ShapedDeclarations (trivia.foldLeft found (noteStep DeclarationNote)).fst :=
  match trivia with
    | [] => shaped
    | [BlankLine, ..rest] => declarationNotes rest (noteStep DeclarationNote found BlankLine) shaped
    | [OwnLine comment, ..rest] =>
      declarationNotes rest
        (noteStep DeclarationNote found (OwnLine comment))
        (declarationsAppend found.fst
          [{ blankBefore = found.snd, line = DeclarationNote comment }]
          shaped
          ((byComputing, byComputing)))

theorem shapedNotedDeclaration ∀ (above: List Trivia) (line: Declaration)
    (shaped: ShapedDeclaration line):
    ShapedDeclarations (notedDeclaration above line) :=
  let notesShaped: ShapedDeclarations (spacedNotes DeclarationNote above).fst :=
    declarationNotes above ([], False) byComputing
  match found: spacedNotes DeclarationNote above with
    | (notes, blankBefore) => declarationsAppend notes [{ blankBefore, line }] notesShaped ((shaped, byComputing))

theorem declarationsWithoutFirstBlank ∀ (lines: List (Spaced Declaration))
    (shaped: ShapedDeclarations lines):
    ShapedDeclarations (withoutFirstBlank lines) :=
  match lines, shaped with
    | [], shaped => byComputing
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped => (lineShaped, restShaped)

theorem declarationsConcat ∀ (groups: List (List (Spaced Declaration)))
    (all: List.All ShapedDeclarations groups):
    ShapedDeclarations groups.concat :=
  match groups, all with
    | [], all => byComputing
    | [first, ..rest], Both firstShaped restShaped =>
      declarationsAppend first rest.concat firstShaped (declarationsConcat rest restShaped)

theorem shapedFileOf ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (shaped: ShapedDeclarations declarations):
    ShapedFile (fileOf declarations endTrivia) :=
  let notesShaped: ShapedDeclarations (spacedNotes DeclarationNote endTrivia).fst :=
    declarationNotes endTrivia ([], False) byComputing
  match found: spacedNotes DeclarationNote endTrivia with
    | (endNotes, blank) =>
      declarationsWithoutFirstBlank
        (declarations ++ endNotes)
        (declarationsAppend declarations endNotes shaped notesShaped)
