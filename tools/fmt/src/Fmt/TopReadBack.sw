--| Read-back for slice 1's top theorems (SW-4079), for declarations that print on one line (`Decl.oneLine1`, D3685):
--| the output's leaves, settled, parse to `calmTop` of the printed tree.
--|
--| The seam is one declaration's group: `readsBackDecl1` is proved from read-back's one-line theorem
--| (`readsBackLineWithin`) and an open goal about the printer's items (`printedSplit1`). The file
--| form, `readsBackFile1`, takes it as a hypothesis and is proved, with the file-level lemmas of `Fmt.ReadBackFile`.

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
import Syntax.ReadBackLine (Spelt, inLineAll, laterInLine, lineAll, readsBackLineWithin, speltExpr)
import Fmt.PrintedLines (exprLine, groupLeafTokens, laterOfValue, leafTokens, leafTokensAppend, typeLines)
import Fmt.CalmProofs (headerCalmWithin, withinCalm)
import Fmt.OutputFileProofs (printedGroups1)
import Fmt.ReadBackFile (declLowers, groupReads, groupsFromTokens, groupsTokens, refusalNone)

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
--| printed expression), with `Spelt`'s one-way prefix clause (SW-4077). `Spelt` and `lineKind` take every binary
--| operator of slice 1, `&&` and `||` included (`logicLine`).
--|
--| False as stated: a call's head may be `-` on a numeral (`def d: A := -1 n`), which `Spelt` doesn't spell
--| (`Fmt.PrefixHeadSplit.printedSplitFails`). `Spelt` must take such heads, or the slice leave them out, first.
theorem printedSplit1 ∀ (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group):
    ∃ (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr) => GroupSplit group read
        keyword name colon colonEq typeRead valueRead result value :=
  ?

--| `printedLines1` (the stock take's U3 under one-line declarations): the items of a printed one-line
--| declaration are of the kinds read-back reads on a line, and start lines only where `oneLine1` lets them.
--|
--| What it needs: `lineAll` from slice 1's alphabet (every printed kind is one), and the rest from `oneLine1` read
--| through `items` (an item's line start is its token's) and `Spelt` (the type's items hold no `:=`). `lineKind`
--| admits every operator `Spelt` spells (`logicLine`).
--|
--| Proof idea: `speltExpr` gives the type's and value's items an expression's kinds, which `lineKind` admits. The
--| group's tokens are `oneLine1`'s (`tokens group = tokens decl.leaves1`) and its items' leaves are the group
--| (`groupLeafTokens`), so `onLine1` reads over the split items: `typeLines` walks the type (no `:=` in it, by its
--| kinds) to the `:=`, leaving the value's `valueOnLine1`.
theorem printedLines1 ∀ (decl read: Decl) (group: List Leaf) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (printed: PrintedGroup decl read group)
    (split: GroupSplit group read keyword name colon colonEq typeRead valueRead result value):
    LinesRead typeRead valueRead :=
  let (within, shaped, settled, lexical, commaFree, oneLine, sameTokens, words, calmed) := printed
  let (isItems, isRead, isDef, isLower, isColon, isColonEq, typeSpelt, valueSpelt, typeWithin, valueWithin) := split
  let typeExpr := speltExpr result typeRead typeSpelt
  let valueExpr := speltExpr value valueRead valueSpelt
  let onLine: onLine1 (tokens decl.leaves1) = True := oneLine
  let itemTokens: leafTokens (items group) = leafTokens [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]] :=
    rewrite isItems
  let lines: typeOnLine1 (leafTokens typeRead ++ [colonEq.leaf.token, ..leafTokens valueRead]) = True :=
    rewrite <- sameTokens,
        <- groupLeafTokens group,
        itemTokens,
        leafTokensAppend typeRead [colonEq, ..valueRead] at onLine then
      onLine
  let (typeIn, valueLines) := typeLines typeRead valueRead colonEq typeExpr isColonEq lines
  (exprLine typeRead typeExpr, exprLine valueRead valueExpr, typeIn, laterOfValue valueRead valueLines)

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

--| `calm`, with the file's first flag cleared or not, keeps a declaration in slice 1.
theorem calmAtWithin ∀ (decl: Decl) (top: Bool) (within: decl.within1 = True): (decl.calmAt top).within1 = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } =>
          let both :=
            Bool.andIntro
              (headerCalmWithin
                {
                  exportKeyword = None,
                  opaqueKeyword = None,
                  kind = DefPlain,
                  keyword,
                  name,
                  forallKeyword = None,
                  params = [],
                  colon,
                  result,
                  decreasingClause = None,
                  unfoldingClause = None
                }
                (Bool.andLeft within))
              (withinCalm value False (Bool.andRight within))
          match top with
            | True => both
            | False => both
        | _ => cases

--| The first of a list.
def firstOr (fallback: a): List a → a
  | [] => fallback
  | [first, .._] => first

--| The groups after the file's first read back to the rest of its declarations, `calm`.
--|
--| Proof idea: by the declarations, a group each (the tokens say so); each group's facts are `PrintedGroup`'s for
--| `calm` of its declaration, so it reads back (`DeclsReadBack`), passes the lowering's checks (`declLowers`), and
--| `parseGroups` goes on to the next with the declaration pushed on `found`.
theorem groupsReadBack ∀ (seen: Seen) (decls: List Decl) (groups: List (List Leaf)) (found: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped1 = True)
    (settled: decls.all Decl.settled1 = True)
    (lexical: decls.all Decl.lexical1 = True)
    (commaFree: decls.all Decl.commaFree = True)
    (oneLine: decls.all Decl.oneLine1 = True)
    (tokensSame: groups.map tokens = decls.map (decl => tokens decl.leaves1))
    (words: groups.map codeWords = (decls.map Decl.calm).map Decl.words) (reads: DeclsReadBack):
    parseGroups seen groups found = Ok (found.reverse ++ decls.map Decl.calm) :=
  match decls, groups with
    | [], [] => rewrite List.appendNil found.reverse
    | [decl, ..rest], [group, ..others] =>
      let printed: PrintedGroup decl (decl.calmAt False) group := (
        Bool.andLeft within,
        Bool.andLeft shaped,
        Bool.andLeft settled,
        Bool.andLeft lexical,
        Bool.andLeft commaFree,
        Bool.andLeft oneLine,
        Eq.cong (firstOr (tokens group)) tokensSame,
        Eq.cong (firstOr (codeWords group)) words,
        (False, byComputing)
      )
      let next :=
        groupsReadBack
          (seen.after (decl.calmAt False))
          rest
          others
          [decl.calmAt False, ..found]
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)
          (Bool.andRight commaFree)
          (Bool.andRight oneLine)
          (Eq.cong (xs => xs.drop 1) tokensSame)
          (Eq.cong (xs => xs.drop 1) words)
          reads
      rewrite groupReads seen group others found
            (decl.calmAt False)
            (reads seen decl (decl.calmAt False) group printed)
            (declLowers (decl.calmAt False) (calmAtWithin decl False (Bool.andLeft within))),
          next,
          List.reverseCons (decl.calmAt False) found,
          List.appendAssoc found.reverse [decl.calmAt False] (rest.map Decl.calm)

--| A printed file's groups read back to `calmTop`'s declarations: the first with its flag cleared, then
--| `groupsReadBack`.
theorem fileGroupsRead ∀ (file: SourceFile) (groups: List (List Leaf))
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True)
    (commaFree: file.commaFree = True)
    (oneLine: file.oneLine1 = True)
    (tokensSame: groups.map tokens = file.decls.map (decl => tokens decl.leaves1))
    (words: groups.map codeWords = file.calmTop.decls.map Decl.words) (reads: DeclsReadBack):
    parseGroups Seen.start groups [] = Ok file.calmTop.decls :=
  match file with
    | { decls = [], end } =>
      match groups with
        | [] => byComputing
    | { decls = [first, ..rest], end } =>
      match first, groups with
        | Definition [] header (Assigned colonEq value), [group, ..others] =>
          let decl := Definition [] header (Assigned colonEq value)
          let declsSettled := Bool.andLeft settled
          let printed: PrintedGroup decl (decl.calmAt True) group := (
            Bool.andLeft within,
            Bool.andLeft shaped,
            Bool.andLeft declsSettled,
            Bool.andLeft lexical,
            Bool.andLeft commaFree,
            Bool.andLeft oneLine,
            Eq.cong (firstOr (tokens group)) tokensSame,
            Eq.cong (firstOr (codeWords group)) words,
            (True, byComputing)
          )
          let next :=
            groupsReadBack
              (Seen.start.after (decl.calmAt True))
              rest
              others
              [decl.calmAt True]
              (Bool.andRight within)
              (Bool.andRight shaped)
              (Bool.andRight declsSettled)
              (Bool.andRight lexical)
              (Bool.andRight commaFree)
              (Bool.andRight oneLine)
              (Eq.cong (xs => xs.drop 1) tokensSame)
              (Eq.cong (xs => xs.drop 1) words)
              reads
          rewrite groupReads Seen.start group others []
                (decl.calmAt True)
                (reads Seen.start decl (decl.calmAt True) group printed)
                (declLowers (decl.calmAt True) (calmAtWithin decl True (Bool.andLeft within))) then
            next

--| `readsBackFile1` (the stock take's U2, SW-4044's file half): leaves whose tokens are a printed one-line file's,
--| and whose groups' words and end are `calmTop`'s, parse to `calmTop`, given each declaration's group reads back.
--|
--| Proof idea: the splitter reads only tokens (`groupsTokens`), so the leaves' groups have the tokens of the printed
--| file's groups, which are the declarations' (`printedGroups1`, `groupsFromTokens`); the first leaf is a `def` in
--| column 0, so `fileRefusal` passes (`refusalNone`); each group reads back to its declaration, `calm`, and the
--| file's first with its flag cleared (`fileGroupsRead`); and the end's comments are the hypothesis's.
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
  let groupsSame: (groupsOf lexed.leaves).map tokens = file.decls.map (decl => tokens decl.leaves1) :=
    Eq.trans
      (groupsTokens lexed.leaves file.lexed1.leaves tokensSame)
      (rewrite printedGroups1 file within shaped settled lexical hung then groupsFromTokens True file.decls)
  let refusal := refusalNone lexed.leaves file.decls within shaped (Bool.andLeft settled) lexical hung tokensSame
  let parsed :=
    fileGroupsRead file (groupsOf lexed.leaves) within shaped settled lexical commaFree oneLine groupsSame words decls
  rewrite refusal, parsed, ends

--| `readsBackLineWithin` reads the logical operators on a line: `&&` and `||` are kinds it reads
--| (`Syntax.ReadBackLine.readsBackLexedLogicExample` reads such a line whole).
theorem logicLine: (match lex "a && b || c" with
      | Ok lexed => lineAll (items lexed.leaves)
      | Err _ => False)
      = True :=
  byComputing
