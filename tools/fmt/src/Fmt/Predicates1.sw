--| The predicates slice 1's proofs speak of (docs/proposals/
--| self-hosted-fmt-s1-sketch.md §1.2, §1.3, §1.5), written out as tests on
--| the real tree: what rule N leaves (`settled1`), the blank-line flags the
--| rules read (`calm`), the shapes the parser gives (`shaped1`), the
--| tokens' spellings (`lexical1`) and where printed lines start (`hangs`).
--|
--| `shaped1` and `lexical1` are the sketch's `Shaped1` and `Lexical1`,
--| which it only names. They are written here from its description, for
--| the passes' proofs: the parser lane (ticket 16) owns them and may
--| tighten them; the passes keep any test that doesn't read a trailing
--| comma.

namespace Fmt
import Std (Bool, List, Nat, Option, Result, Text)
import Syntax (Comments, Decl, DefBody, Expr, Header, InfixKind, Leaf, Note, SourceFile, Tok, Word, lex)

-- Settled (K1, rule 3, rule 5).

--| A declaration's tokens in order, commas left out (the tree has none).
def Decl.words: Decl → List Word
  | Definition _ header (Assigned colonEq value) =>
    [fixedWord "def" header.keyword, header.name, fixedWord ":" header.colon]
      ++ header.result.words
      ++ [fixedWord ":=" colonEq]
      ++ value.words
  | _ => []

--| Closers, newest word first: a closer holds a trailing comment only if
--| it has own-line comments or the code before it, closers aside, ends
--| with a comment (K1's `homed`; commas aren't in the list, which is rule
--| 1 walking past them).
def homedBack: List Word → Bool
  | [] => True
  | [word, ..earlier] =>
    (!(isCloserText word.text && word.trails) || earlier.isEmpty || word.noted || trailsBack earlier)
      && homedBack earlier

--| `->`: no trailing comment on it and no own-line comment after it
--| (rule 3).
def arrowsBare: List Word → Bool
  | [word, next, ..rest] =>
    (operatorTok word.text != Some Arrow || (!word.trails && !next.noted)) && arrowsBare [next, ..rest]
  | _ => True

--| A comment as rule N leaves it and the lexer reads it: `--`, no line
--| break, no space at its end (rule 5).
def commentText (text: Text): Bool := text.startsWith "--" && !text.contains "\n" && !text.endsWith " "

def Comments.texts (comments: Comments): List Text := comments.above.map (note => note.text) ++ comments.after.toList

def Decl.settled1 (decl: Decl): Bool :=
  homedBack decl.words.reverse && arrowsBare decl.words && decl.words.all (word => word.comments.texts.all commentText)

def SourceFile.settled1 (file: SourceFile): Bool :=
  file.decls.all Decl.settled1 && file.end.texts.all commentText && file.end.after.isNone

-- Blank lines: `calm`.

--| A token's comments with the blank-line flags the rules never read
--| cleared: the flag below the comments is read above an item with no
--| comments and below any comments that aren't a closer's; the first
--| comment's flag only above an item.
def Comments.kept (comments: Comments) (item closer: Bool): Comments :=
  let above := match comments.above with
    | [] => []
    | [first, ..rest] => [{ first | blankBefore = first.blankBefore && item && !closer }, ..rest]
  let below := if comments.above.isEmpty then item else !closer
  { comments | above, blankBefore = comments.blankBefore && below }

def Word.kept (word: Word) (item closer: Bool): Word := { word | comments = word.comments.kept item closer }

--| The expression with only the blank-line flags the rules read. `item`:
--| it is an item of a tuple or list.
def Expr.calm (expr: Expr) (item: Bool): Expr := match expr with
  | Atom kind word => Atom kind (word.kept item False)
  | Paren open inner close => Paren (open.kept item False) (inner.calm False) (close.kept False True)
  | Tuple open items comma close => Tuple (open.kept item False) (calmAll True items) comma (close.kept False True)
  | ListOf open items comma close => ListOf (open.kept item False) (calmItems items) comma (close.kept False True)
  | App head arguments => App (head.calm item) (calmAll False arguments)
  | Infix kind left operator right => Infix kind (left.calm item) (operator.kept False False) (right.calm False)
  | Prefix operator operand => Prefix (operator.kept item False) (operand.calm False)
  | other => other

--| The items of a list of only plain values: the first is no item for
--| blank lines (`firstAround`).
def calmLead: List Expr → List Expr
  | [] => []
  | [first, ..rest] => [first.calm False, ..calmAll True rest]

--| A bracket's items.
def calmItems (items: List Expr): List Expr := pickItems (items.all Expr.plainItem) items

--| `calmItems`, given whether the items are all plain values.
def pickItems (plain: Bool) (items: List Expr): List Expr := if plain then calmLead items else calmAll True items

def calmAll (item: Bool): List Expr → List Expr
  | [] => []
  | [expr, ..rest] => [expr.calm item, ..calmAll item rest]

--| A header with the first token's flags kept (the file loop reads them
--| all) and the rest of its tokens calmed.
def Header.calm (header: Header): Header := { header |
  name = header.name.kept False False,
  colon = header.colon.kept False False,
  result = header.result.calm False
}

def Decl.calm: Decl → Decl
  | Definition attributes header (Assigned colonEq value) =>
    Definition attributes header.calm (Assigned (colonEq.kept False False) (value.calm False))
  | other => other

--| Calm declarations; the end's own flag is the file loop's, not read.
def SourceFile.calm (file: SourceFile): SourceFile :=
  { decls = file.decls.map Decl.calm, end = { file.end | blankBefore = False } }

-- Shaped and lexical.

--| An atom or a bracket: what a call's argument may be, and what a sign on an argument may sit on.
def Expr.atomic1: Expr → Bool
  | Atom _ _ => True
  | Paren _ _ _ => True
  | Tuple _ _ _ _ => True
  | ListOf _ _ _ _ => True
  | _ => False

--| A numeral, which a `-` glued to it reads as one atom with.
def Expr.numberAtom1: Expr → Bool
  | Atom Num _ => True
  | Atom Float _ => True
  | _ => False

--| The leftmost token of an expression of the slice.
def Expr.lead: Expr → Word
  | Atom _ word => word
  | Paren open _ _ => open
  | Tuple open _ _ _ => open
  | ListOf open _ _ _ => open
  | App head _ => head.lead
  | Infix _ left _ _ => left.lead
  | Prefix operator _ => operator
  | _ => Word.none

--| No comment between a sign and its operand: none trailing the sign and none above the operand's first token. A
--| comment there breaks the line, so nothing is glued: `(- -- c` then `1)` on the next line.
def signQuiet (operator: Word) (operand: Expr): Bool := quietBefore operator operand.lead

--| No comment after `operator` and none above `next`.
def quietBefore (operator next: Word): Bool := match operator.comments.after, next.comments.above with
  | None, [] => True
  | _, _ => False

--| A call's head: an atom or a bracket, or `-` on a numeral (`-1 n` reads `-1` as one atom, `App (Prefix - 1) [n]`),
--| with no comment between them (`signQuiet`: the parser reads `-1` as one atom only when the two are glued). Any
--| other sign takes the whole call: `-x y` and `!x y` read as `-(x y)` and `!(x y)`.
def Expr.head1: Expr → Bool
  | Prefix operator operand => operator.text == "-" && operand.numberAtom1 && signQuiet operator operand
  | other => other.atomic1

--| A call's argument: an atom or a bracket, or a sign on one (`f -x !b`) with no comment between them
--| (`signQuiet`: the parser reads an argument's sign only when its operand is glued to it). A sign on a sign is no
--| argument: `f - -x` reads as `f - (-x)`, since only an atom or a bracket may follow an argument's sign.
def Expr.argument1: Expr → Bool
  | Prefix operator operand => operand.atomic1 && signQuiet operator operand
  | other => other.atomic1

--| The least level an expression needs to stand bare as the right operand of an infix operator: the operator's own
--| level where it nests to the right (`++`, `&&`, `||`, `->`), the next level up where it nests to the left (`+`, `*`:
--| `a - (b - c)` needs its brackets, as `a - b - c` reads as `(a - b) - c`), and for a comparison, which doesn't chain
--| (`a == b == c` doesn't parse), level 8, the level `leftNeeds` asks of its left operand. An operator nests to the
--| left exactly where `leftNeeds` is its own level.
def rightNeeds (kind: InfixKind) (operator: Text): Nat := match kind with
  | InfixBinary =>
    if leftNeeds kind operator == 8 then 8
    else if leftNeeds kind operator == infixLevel kind operator then infixLevel kind operator + 2
    else infixLevel kind operator
  | other => infixLevel kind operator

--| The tree is one the parser can give: a call's head is an atom, a bracket or a negative numeral, and its arguments
--| atoms, brackets or signs on them (so a head is no application); operands of an infix sit at their ladder levels
--| (`ParseProofs` proves the levels), the right operand of a chain that nests to the left one level up; a tuple has
--| two items or more.
def Expr.shaped1: Expr → Bool
  | Atom kind _ => kind.wordWithin1
  | Paren _ inner _ => inner.shaped1
  | Tuple _ items _ _ => items.length >= 2 && allShaped1 items
  | ListOf _ items _ _ => allShaped1 items
  | App head arguments =>
    head.head1 && head.shaped1 && !arguments.isEmpty && arguments.all Expr.argument1 && allShaped1 arguments
  | Infix kind left operator right =>
    left.shaped1
      && right.shaped1
      && leftNeeds kind operator.text <= left.level
      && rightNeeds kind operator.text <= right.level
  | Prefix _ operand => operand.shaped1 && 18 <= operand.level
  | _ => False

def allShaped1: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.shaped1 && allShaped1 rest

--| A text lexes as exactly one token, of the given kind.
def textLexesAs (text: Text) (kind: Tok): Bool := match lex text with
  | Ok lexed =>
    match lexed.leaves with
      | [leaf] => leaf.token.text == text && leaf.token.kind == kind
      | _ => False
  | Err _ => False

--| A word's text lexes as exactly one token, of the given kind.
def Word.lexesAs (word: Word) (kind: Tok): Bool := textLexesAs word.text kind

--| Words with one text lex alike: the comments are no part of the lexing.
theorem Word.lexesAsText ∀ (word other: Word)
    (same: word.text = other.text) (kind: Tok):
    word.lexesAs kind = other.lexesAs kind :=
  rewrite same

theorem Word.keptNameWithin1 ∀ (word: Word) (item closer: Bool):
    (word.kept item closer).nameWithin1 = word.nameWithin1 :=
  byComputing

theorem Word.keptLexesAs ∀ (word: Word) (item closer: Bool) (kind: Tok):
    (word.kept item closer).lexesAs kind = word.lexesAs kind :=
  byComputing

--| Each word's text lexes as one token of its kind, a bracket's word is
--| its bracket and an operator's text is in `operatorTok`'s table.
def Expr.lexical1: Expr → Bool
  | Atom kind word => word.lexesAs kind
  | Paren open inner close => open.text == "(" && close.text == ")" && inner.lexical1
  | Tuple open items _ close => open.text == "(" && close.text == ")" && allLexical1 items
  | ListOf open items _ close => open.text == "[" && close.text == "]" && allLexical1 items
  | App head arguments => head.lexical1 && allLexical1 arguments
  | Infix _ left operator right => left.lexical1 && (operatorTok operator.text).isSome && right.lexical1
  | Prefix operator operand => (operatorTok operator.text).isSome && operand.lexical1
  | _ => False

def allLexical1: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.lexical1 && allLexical1 rest

def Decl.lexical1: Decl → Bool
  | Definition _ header (Assigned _ value) =>
    (header.name.lexesAs Lower || header.name.lexesAs Upper) && header.result.lexical1 && value.lexical1
  | _ => False

def Decl.shaped1: Decl → Bool
  | Definition _ header (Assigned _ value) => header.result.shaped1 && value.shaped1
  | _ => False

def SourceFile.shaped1 (file: SourceFile): Bool := file.decls.all Decl.shaped1

def SourceFile.lexical1 (file: SourceFile): Bool := file.decls.all Decl.lexical1

-- Continued lines: `hangs` (K3a).

--| The block column in force: the innermost open bracket whose current
--| item started a line, else the type's or the body's, else the `def`'s 0.
def inForce (blocks: List (Option Nat)) (top: Option Nat): Nat := match blocks with
  | [Some column, .._] => column
  | [None, ..rest] => inForce rest top
  | [] => top.getOrElse 0

def leftOf (column: Nat): Option Nat → Bool
  | Some block => column < block
  | None => True

--| The bracket columns after a leaf at `column`: a leaf that starts its
--| bracket's current item and its line gives that item its column.
def startBlocks (fresh: Bool) (column: Nat) (blocks: List (Option Nat)): List (Option Nat) := match blocks with
  | [_, ..outer] => if fresh then [Some column, ..outer] else blocks
  | [] => []

--| The type's or body's column after a leaf at `column`, likewise.
def startTop (fresh: Bool) (column: Nat) (blocks: List (Option Nat)) (top: Option Nat): Option Nat :=
  if fresh && blocks.isEmpty then Some column else top

--| Where `hangs` is in a declaration's leaves: for each open bracket,
--| innermost first, the column of its current item if that item started
--| a line (`blocks`); the same for the type or the body (`top`); whether
--| the next leaf starts an item, the type or the body (`start`); and
--| whether it must not start a line, after `->` (`glue`).
type HangState = {
  blocks: List (Option Nat),
  top: Option Nat,
  start: Bool,
  glue: Bool
}

--| After a declaration's `def`.
def HangState.initial: HangState := { blocks = [], top = None, start = False, glue = False }

--| The state after a leaf that is neither a closer nor a comma, starting
--| an item if `opens`, with `glue` after it.
def HangState.past (state: HangState) (column: Nat) (fresh opens glue: Bool): HangState :=
  let blocks := startBlocks fresh column state.blocks
  let top := startTop fresh column state.blocks state.top
  if opens then { blocks = [None, ..blocks], top, start = True, glue } else { blocks, top, start = False, glue }

--| One leaf, as the parser's line rule needs it: a leaf that starts a
--| line is right of the block column in force; a closer that starts a line
--| is left of the column its bracket's current item started a line at; no
--| comma starts a line, nor the leaf after `->`, and a `:` that starts one
--| is right of column 0. `None` where the leaf breaks the rule.
--|
--| Each clause is a place the parser looks at columns. An expression
--| whose first token starts a line is a block at that column (`expr`),
--| whose next line at the same column is a new statement (`blockLines`),
--| so a later line of it must start further right, and a closer or comma
--| that starts a line must not stand at it (the parser lets them start a
--| line at any other column). The operand of `->` is read as a full
--| expression (`resultType`), so starting it on a line of its own would
--| make it a block of its own, which this predicate doesn't track. A `:`
--| at column 0 starts a new declaration (`groupsOf`). `:=` may start a line
--| anywhere: it ends every block (`endsBlocks`).
def HangState.step (state: HangState) (leaf: Leaf): Option HangState :=
  let column := leaf.token.column
  let starts := leaf.token.lineStart
  let kind := leaf.token.kind
  let right := !starts || column > inForce state.blocks state.top
  let fresh := state.start && starts
  if state.glue && starts then None
  else if kind.isCloser then
    match state.blocks with
      | [block, ..outer] =>
        if !starts || leftOf column block then Some { blocks = outer, top = state.top, start = False, glue = False }
        else None
      | [] => None
  else if kind == Comma then
    match state.blocks with
      | [_, ..outer] =>
        if starts then None else Some { blocks = [None, ..outer], top = state.top, start = True, glue = False }
      | [] => None
  else if kind == ColonEq && state.blocks.isEmpty then Some { blocks = [], top = None, start = True, glue = False }
  else if !right then None
  else if kind == Colon && state.blocks.isEmpty then Some { blocks = [], top = None, start = True, glue = False }
  else Some (state.past column fresh kind.isOpener (kind == Arrow))

--| The leaves after a declaration's `def` keep the line rule, from `state`.
def hangsFrom (state: HangState): List Leaf → Bool
  | [] => True
  | [leaf, ..rest] =>
    match state.step leaf with
      | Some next => hangsFrom next rest
      | None => False

--| One declaration's leaves, from its `def` at column 0.
def hangs: List Leaf → Bool
  | [first, ..rest] => first.token.kind == KwDef && first.token.column == 0 && hangsFrom HangState.initial rest
  | [] => True
