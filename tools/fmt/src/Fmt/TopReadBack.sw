--| Read-back for slice 1's top theorems (SW-4079): the output's leaves, settled, parse to `calmTop` of the printed
--| tree, on any number of lines.
--|
--| The seam is one declaration's group: `readsBackDecl1` is proved from read-back's theorem over lines that keep the
--| line rule (`readsBackHung`) and the split of the printer's items (`printedSplit1`, in `Fmt.GroupSlots`). The file
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
import Syntax.ReadBackLine (Spelt, exprLine, lineAll, speltExpr)
import Syntax.ReadBackHungDeep (hangsTokens)
import Syntax.ReadBackHungTop (readsBackHung)
import Fmt.CalmProofs (headerCalmWithin, withinCalm)
import Fmt.OutputFileProofs (printedGroups1)
import Fmt.ReadBackFile (declLowers, groupReads, groupsFromTokens, groupsTokens, refusalNone)
import Fmt.GroupFacts (..)
import Fmt.GroupSlots (printedSplit1)
import Fmt.PlacedProofs (declPlacedCalmAt)
import Syntax.AutoPlaced (..)

-- One declaration.

--| One group of leaves read back: its items, run as `parseGroups` runs a declaration, give `read`.
def DeclReadsBack (seen: Seen) (group: List Leaf) (read: Decl): Prop :=
  Parse.run (items group) (() =>
    let decl := declaration seen
    decl)
    = Ok read

--| The line facts `readsBackHung` takes: every item of the type and the value of a kind it reads.
def LinesRead (typeRead valueRead: List Item): Prop := lineAll typeRead = True ∧ lineAll valueRead = True

--| `printedLines1` (the stock take's U3): the items of a printed declaration's type and value are of the kinds
--| read-back reads, from slice 1's alphabet: `speltExpr` gives them an expression's kinds, which `lineKind` admits
--| (`logicLine` for the logical operators). Where they start lines is `hangs`' business, not this lemma's.
theorem printedLines1 ∀ (group: List Leaf) (read: Decl) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (split: GroupSplit group read keyword name colon colonEq typeRead valueRead result value):
    LinesRead typeRead valueRead :=
  let (_, _, _, _, _, _, typeSpelt, valueSpelt, _, _) := split
  (exprLine typeRead (speltExpr result typeRead typeSpelt), exprLine valueRead (speltExpr value valueRead valueSpelt))

--| A printed declaration's group reads back to `read`, on any number of lines: `readsBackHung` on the items
--| `printedSplit1` gives, with `printedLines1`'s kinds, the group keeping the line rule because its tokens are the
--| printed leaves' (`hangsTokens`).
theorem readsBackDecl1 ∀ (seen: Seen) (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group)
    (placed: read.autoPlaced = True):
    DeclReadsBack seen group read :=
  let (keyword, name, colon, colonEq, typeRead, valueRead, result, value, split) :=
    printedSplit1 decl read group printed
  let (typeLine, valueLine) := printedLines1 group read keyword name colon colonEq typeRead valueRead result value split
  let (_, _, _, _, _, printedHangs, sameTokens, _, _) := printed
  let (isItems, isRead, isDef, isLower, isColon, isColonEq, typeSpelt, valueSpelt, typeWithin, valueWithin) := split
  let hung: hangs group = True := rewrite hangsTokens group decl.leaves sameTokens then printedHangs
  let bothPlaced: Decl.autoPlaced
    (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value))
    = True :=
    rewrite <- isRead then placed
  rewrite isRead then
    readsBackHung seen group keyword name colon colonEq typeRead valueRead result value isItems hung isDef isLower
        isColon isColonEq typeSpelt valueSpelt typeLine valueLine
        (Bool.andLeft bothPlaced)
        (Bool.andRight bothPlaced)

-- The file.

--| Every printed declaration's group reads back: `readsBackDecl1`'s statement, which `readsBackFile1` takes.
def DeclsReadBack: Prop :=
  ∀ (seen: Seen) (decl read: Decl) (group: List Leaf) => PrintedGroup decl read group
    → read.autoPlaced = True
    → DeclReadsBack seen group read

theorem declsReadBack: DeclsReadBack := seen decl read group printed placed =>
  readsBackDecl1 seen decl read group printed placed

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
            | True | False => both
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
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True)
    (commaFree: decls.all Decl.commaFree = True)
    (hung: decls.all (decl => hangs decl.leaves) = True)
    (placed: decls.all Decl.autoPlaced = True)
    (tokensSame: groups.map tokens = decls.map (decl => tokens decl.leaves))
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
        Bool.andLeft hung,
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
          (Bool.andRight hung)
          (Bool.andRight placed)
          (Eq.cong (xs => xs.drop 1) tokensSame)
          (Eq.cong (xs => xs.drop 1) words)
          reads
      rewrite groupReads seen group others found
            (decl.calmAt False)
            (reads seen decl
              (decl.calmAt False)
              group
              printed
              (rewrite declPlacedCalmAt decl False then Bool.andLeft placed))
            (declLowers (decl.calmAt False) (calmAtWithin decl False (Bool.andLeft within))),
          next,
          List.reverseCons (decl.calmAt False) found,
          List.appendAssoc found.reverse [decl.calmAt False] (rest.map Decl.calm)

--| A printed file's groups read back to `calmTop`'s declarations: the first with its flag cleared, then
--| `groupsReadBack`.
theorem fileGroupsRead ∀ (file: SourceFile) (groups: List (List Leaf))
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (commaFree: file.commaFree = True)
    (hung: file.hung = True)
    (placed: file.autoPlaced = True)
    (tokensSame: groups.map tokens = file.decls.map (decl => tokens decl.leaves))
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
            Bool.andLeft hung,
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
              (Bool.andRight hung)
              (Bool.andRight placed)
              (Eq.cong (xs => xs.drop 1) tokensSame)
              (Eq.cong (xs => xs.drop 1) words)
              reads
          rewrite groupReads Seen.start group others []
                (decl.calmAt True)
                (reads Seen.start decl
                  (decl.calmAt True)
                  group
                  printed
                  (rewrite declPlacedCalmAt decl True then Bool.andLeft placed))
                (declLowers (decl.calmAt True) (calmAtWithin decl True (Bool.andLeft within))) then
            next

--| `readsBackFile1` (the stock take's U2, SW-4044's file half): leaves whose tokens are a printed file's,
--| and whose groups' words and end are `calmTop`'s, parse to `calmTop`, given each declaration's group reads back.
--|
--| Proof idea: the splitter reads only tokens (`groupsTokens`), so the leaves' groups have the tokens of the printed
--| file's groups, which are the declarations' (`printedGroups1`, `groupsFromTokens`); the first leaf is a `def` in
--| column 0, so `fileRefusal` passes (`refusalNone`); each group reads back to its declaration, `calm`, and the
--| file's first with its flag cleared (`fileGroupsRead`); and the end's comments are the hypothesis's.
theorem readsBackFile1 ∀ (file: SourceFile) (lexed: Lexed)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (commaFree: file.commaFree = True)
    (hung: file.hung = True)
    (placed: file.autoPlaced = True)
    (tokensSame: tokens lexed.leaves = tokens file.lexed.leaves)
    (words: (groupsOf lexed.leaves).map codeWords = file.calmTop.decls.map Decl.words)
    (ends: lexed.end.comments = file.calmTop.end) (decls: DeclsReadBack):
    parseFile lexed = Ok file.calmTop :=
  let groupsSame: (groupsOf lexed.leaves).map tokens = file.decls.map (decl => tokens decl.leaves) :=
    Eq.trans
      (groupsTokens lexed.leaves file.lexed.leaves tokensSame)
      (rewrite printedGroups1 file within shaped settled lexical hung then groupsFromTokens True file.decls)
  let refusal := refusalNone lexed.leaves file.decls within shaped (Bool.andLeft settled) lexical hung tokensSame
  let parsed :=
    fileGroupsRead file
      (groupsOf lexed.leaves)
      within
      shaped
      settled
      lexical
      commaFree
      hung
      placed
      groupsSame
      words
      decls
  rewrite refusal, parsed, ends
