--| Read-back for slice 1's top theorems (SW-4079), for declarations that print on one line (`Decl.oneLine1`, D3685):
--| the output's leaves, settled, parse to `calmTop` of the printed tree.
--|
--| The seam is one declaration's group: `readsBackDecl1` is proved from read-back's one-line theorem
--| (`readsBackLineWithin`) and two open goals about the printer's items (`printedSplit1`, `printedLines1`). The file
--| form, `readsBackFile1`, takes it as a hypothesis and is open.

namespace Fmt.TopReadBack
import Std (Bool, Eq, List, Nat, Option, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)
import Fmt.PassProofs (..)
import Syntax.SettleProofs (tokens)
import Syntax.ParseCarries (codeWords)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackLine (Spelt, inLineAll, laterInLine, lineAll, readsBackLineWithin)

-- One declaration.

--| `calm` of a declaration, and for the file's first (`top`) its `def`'s first flag cleared: what `calmTop` makes of
--| each declaration.
def Decl.calmAt (decl: Decl) (top: Bool): Decl := match top, decl.calm with
  | True, Definition attributes header body => Definition attributes { header | keyword = header.keyword.topped } body
  | _, calmed => calmed

--| One group of leaves read back: its items, run as `parseGroups` runs a declaration, give `read`.
def DeclReadsBack (seen: Seen) (group: List Leaf) (read: Decl): Prop :=
  Parse.run (items group) (() =>
    let decl := declaration seen
    decl)
    = Ok read

--| A group's items as `readsBackLineWithin` takes them: `def`, the name, `:`, the type's, `:=` and the value's;
--| `read` is the definition they make, its type and value spelt by their items and within slice 1.
def GroupSplit (group: List Leaf) (read: Decl) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr):
    Prop :=
  items group = [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]]
    ∧ read = Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)
    ∧ keyword.kind = KwDef
    ∧ name.kind = Lower
    ∧ colon.kind = Colon
    ∧ colonEq.kind = ColonEq
    ∧ Spelt result typeRead
    ∧ Spelt value valueRead
    ∧ result.within1 = True
    ∧ value.within1 = True

--| The line facts `readsBackLineWithin` takes: every item of a kind it reads on a line, no item of the type starting
--| a line, and none of the value's after its first.
def LinesRead (typeRead valueRead: List Item): Prop :=
  lineAll typeRead = True ∧ lineAll valueRead = True ∧ inLineAll typeRead = True ∧ laterInLine valueRead = True

--| What the output says of one printed declaration `decl` and the group of leaves the second run parses for it: the
--| tree facts of `decl` the driver gives, its printed tokens on one line, the group's tokens those printed tokens
--| (rule N moves only comments), and the group's words `read`'s, where `read` is `calm` of `decl`
--| (`printedSettle1`).
def PrintedGroup (decl read: Decl) (group: List Leaf): Prop :=
  decl.within1 = True
    ∧ decl.shaped1 = True
    ∧ decl.settled1 = True
    ∧ decl.lexical1 = True
    ∧ decl.commaFree = True
    ∧ decl.oneLine1 = True
    ∧ tokens group = tokens decl.leaves1
    ∧ codeWords group = read.words
    ∧ (∃ (top: Bool) => read = decl.calmAt top)

--| `printedSplit1` (open): a printed one-line declaration's group splits into the items `readsBackLineWithin` reads,
--| with `read`'s type and value spelt by them.
--|
--| What it needs: the tokens are the rules' spelling, comma between items and kinds the lexer's (`printedTokens1`);
--| the group's words are `read`'s (the hypothesis); and the glue facts each item carries (`glued`, `afterOperand`),
--| which come from the printed spacing: SW-4075 (std's `touches`), SW-4076 (`printedSpacing1`, then `Spelt` of a
--| printed expression), with SW-4077's weaker prefix equation. `Spelt` and `lineKind` take every binary operator of
--| slice 1, `&&` and `||` included (`logicLine`).
theorem printedSplit1 ∀ (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group):
    ∃ (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr) => GroupSplit group read
        keyword name colon colonEq typeRead valueRead result value :=
  ?

--| `printedLines1` (open, the stock take's U3 under one-line declarations): the items of a printed one-line
--| declaration are of the kinds read-back reads on a line, and start lines only where `oneLine1` lets them.
--|
--| What it needs: `lineAll` from slice 1's alphabet (every printed kind is one), and the rest from `oneLine1` read
--| through `items` (an item's line start is its token's) and `Spelt` (the type's items hold no `:=`). `lineKind`
--| admits every operator `Spelt` spells (`logicLine`).
theorem printedLines1 ∀ (decl read: Decl) (group: List Leaf) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (printed: PrintedGroup decl read group)
    (split: GroupSplit group read keyword name colon colonEq typeRead valueRead result value):
    LinesRead typeRead valueRead :=
  ?

--| A printed one-line declaration's group reads back to `read`: `readsBackLineWithin` on the items `printedSplit1`
--| gives, with `printedLines1`'s line facts.
theorem readsBackDecl1 ∀ (seen: Seen) (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group):
    DeclReadsBack seen group read :=
  let (keyword, name, colon, colonEq, typeRead, valueRead, result, value, split) :=
    printedSplit1 decl read group printed
  let (typeLine, valueLine, typeInLine, valueLater) :=
    printedLines1 decl read group keyword name colon colonEq typeRead valueRead result value printed split
  let (isItems, isRead, isDef, isLower, isColon, isColonEq, typeSpelt, valueSpelt, typeWithin, valueWithin) := split
  rewrite isItems, isRead then
    readsBackLineWithin seen keyword name colon colonEq typeRead valueRead result value isDef isLower isColon isColonEq
        typeSpelt valueSpelt typeLine valueLine typeInLine valueLater typeWithin valueWithin

-- The file.

--| Every printed one-line declaration's group reads back: `readsBackDecl1`'s statement, which `readsBackFile1` takes.
def DeclsReadBack: Prop :=
  ∀ (seen: Seen) (decl read: Decl) (group: List Leaf) => PrintedGroup decl read group → DeclReadsBack seen group read

theorem declsReadBack: DeclsReadBack := seen decl read group printed => readsBackDecl1 seen decl read group printed

--| `readsBackFile1` (open; the stock take's U2, SW-4044's file half): leaves whose tokens are a printed one-line
--| file's, and whose groups' words and end are `calmTop`'s, parse to `calmTop`, given each declaration's group reads
--| back.
--|
--| What it needs: the groups of `leaves` are the declarations' (`printedGroups1`, with `groupsOf` reading only
--| tokens); the first leaf is a `def` in column 0, so `fileRefusal` passes; `parseGroups` runs each group as
--| `DeclReadsBack` says (the file's first with `top`, as `calmTop` has it), and every declaration of slice 1 passes the
--| lowering's checks; the end's comments are the hypothesis's.
theorem readsBackFile1 ∀ (file: SourceFile) (lexed: Lexed)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True)
    (commaFree: file.commaFree = True)
    (oneLine: file.oneLine1 = True)
    (hung: file.hung1 = True)
    (tokensSame: tokens lexed.leaves = tokens file.lexed1.leaves)
    (words: (groupsOf lexed.leaves).map codeWords = file.calmTop.decls.map Decl.words)
    (ends: lexed.end.comments = file.calmTop.end) (decls: DeclsReadBack):
    parseFile lexed = Ok file.calmTop :=
  ?

--| `readsBackLineWithin` reads the logical operators on a line: `&&` and `||` are kinds it reads
--| (`Syntax.ReadBackLine.readsBackLexedLogicExample` reads such a line whole).
theorem logicLine: (match lex "a && b || c" with
      | Ok lexed => lineAll (items lexed.leaves)
      | Err _ => False)
      = True :=
  byComputing
