--| `printedFileLexes1` (SW-4039, ticket B of docs/reviews/SW-4025-output-statements.md): the file loop's text lexes
--| to `SourceFile.lexed1`. The text is the lexer proofs' pieces of each item (an own-line comment, or a
--| declaration's printed pieces) after one or two line breaks, so `lexPrintedPairs` reads it as `Laid.lay` folded
--| over them; a declaration laid from the start of a line gives its own leaves, the first holding the comments and
--| blank lines waiting there (`layShifted`), as long as it starts with a token and ends with nothing waiting
--| (`Seamed`, the open goal `printedSeam1`).

namespace Fmt.FileLexProofs
import Std (Bool, Char, Doc, Eq, List, Nat, Option, Parse, Result, Text, Void, byDecision)
import Std.Doc.Proofs (Every, Joins, Plain, Uniform, printedJoins, printedPieces)
import Syntax (..)
import Syntax.Proofs (AllPlain, AllSpelled, Laid, PairsFollow, Piece, lexPrintedPairs, pieceSteps, piecesText)
import Fmt (..)
import Fmt.PrintLexProofs (
  Chrono,
  Follows,
  Printable,
  adjOfChrono,
  chronoOfPairs,
  goodOfChrono,
  mayFollowBreak,
  pairsFollowFold,
  pieceFold,
  pieceFoldOk,
  piecesTextIsConcat,
  remarkSpelled
)
import Fmt.JoinProofs (doc1Passes)
import Fmt.SpellProofs (declSoundOfSettled, doc1Spells)
import Fmt.TreeJoinProofs (declJoins, declOperators, declPrintable, declReal, lexKind)
import Fmt.OutputStatements (..)

-- A declaration's pieces.

--| The lexer proofs' pieces of a declaration's printed text, as `Decl.leaves1` lays them.
def Decl.pieces1 (decl: Decl): List Piece := match decl.doc1 with
  | Some doc => pieceFold lexKind (printedPieces doc width)
  | None => []

theorem leavesOfPieces ∀ (decl: Decl): decl.leaves1 = (decl.pieces1.foldLeft Laid.start Laid.lay).leaves.reverse :=
  match decl.doc1 with
    | Some doc => byComputing
    | None => byComputing

--| What `printedLexes` asks of a document's pieces, taken apart: they are plain, spelled and follow one another, and
--| they are the printed text.
theorem printedPiecesOk ∀ (doc: Doc) (width: Nat) (kinds: Text → Tok)
    (uniform: Uniform doc)
    (joins: Joins (Follows kinds) doc (Plain None) (after => True))
    (all: Every (Printable kinds) doc.words):
    AllPlain (pieceFold kinds (printedPieces doc width))
      ∧ AllSpelled (pieceFold kinds (printedPieces doc width))
      ∧ PairsFollow (pieceFold kinds (printedPieces doc width))
      ∧ Doc.print doc width = piecesText (pieceFold kinds (printedPieces doc width)) :=
  let (printed, every, pairs) := printedJoins (Follows kinds) (Printable kinds) doc width uniform joins all
  let chrono := chronoOfPairs (Follows kinds) (printedPieces doc width).reverse pairs
  let ordered: Chrono (Follows kinds) (printedPieces doc width) :=
    rewrite List.reverseReverse (printedPieces doc width) at chrono then chrono
  let good := goodOfChrono kinds (printedPieces doc width) ordered every
  let (plain, spelled) := pieceFoldOk kinds (printedPieces doc width) good
  (
    plain,
    spelled,
    pairsFollowFold kinds (printedPieces doc width) (adjOfChrono kinds (printedPieces doc width) ordered good) good,
    Eq.trans printed (piecesTextIsConcat kinds (printedPieces doc width)).flipped
  )

--| `printedPiecesOk` of a slice 1 declaration, from the tree's facts, as `printLexes1Settled` takes them.
theorem declPiecesOk ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True):
    AllPlain decl.pieces1
      ∧ AllSpelled decl.pieces1
      ∧ PairsFollow decl.pieces1
      ∧ (decl.printed1.getOrElse "").toList = Parse.joinReads (pieceSteps decl.pieces1) :=
  let operators := declOperators decl within
  let sound := declSoundOfSettled decl within settled (declReal decl within lexical operators)
  match shows: decl.doc1 with
    | Some doc =>
      let (uniform, _, words) := doc1Spells decl doc within sound shows
      let (plain, spelled, pairs, printed) :=
        printedPiecesOk doc width lexKind uniform
          (doc1Passes lexKind decl doc within (declJoins decl within shaped sound lexical operators) shows)
          (rewrite words then declPrintable decl within sound lexical operators)
      (plain, spelled, pairs, rewrite within, printed)
    | None =>
      match decl, within, shows with
        | Definition [] header (Assigned colonEq value), _, never => cases

-- What the file's pieces need of one another.

--| Any piece may stand before a line break.
theorem followsBreak ∀ (piece: Piece) (rest: List Char): piece.Follows ['\n', ..rest] := match piece with
  | Code kind text => mayFollowBreak kind text rest
  | Gap count => Both byDecision byDecision
  | Break => byComputing
  | Remark text => byComputing

def startsBreak: List Piece → Bool
  | [Break, .._] => True
  | _ => False

--| Pieces that follow one another, then pieces that start with a line break, or nothing.
theorem pairsAppend ∀ (front back: List Piece)
    (frontPairs: PairsFollow front)
    (backPairs: PairsFollow back)
    (joinable: (front.isEmpty || back.isEmpty || startsBreak back) = True):
    PairsFollow (front ++ back) :=
  match front, frontPairs with
    | [], _ => backPairs
    | [piece], follows =>
      match back, backPairs, joinable with
        | [], _, _ => follows
        | [Break, ..more], laterPairs, _ => (followsBreak piece [], laterPairs)
        | [Code kind text, ..more], _, never => cases
        | [Gap count, ..more], _, never => cases
        | [Remark text, ..more], _, never => cases
    | [piece, next, ..rest], (follows, later) => (follows, pairsAppend [next, ..rest] back later backPairs joinable)

theorem plainAppend ∀ (front back: List Piece)
    (frontPlain: AllPlain front)
    (backPlain: AllPlain back):
    AllPlain (front ++ back) :=
  match front, frontPlain with
    | [], _ => backPlain
    | [piece, ..rest], Both piecePlain restPlain => Both piecePlain (plainAppend rest back restPlain backPlain)

theorem spelledAppend ∀ (front back: List Piece)
    (frontSpelled: AllSpelled front)
    (backSpelled: AllSpelled back):
    AllSpelled (front ++ back) :=
  match front, frontSpelled with
    | [], _ => backSpelled
    | [piece, ..rest], Both pieceSpelled restSpelled =>
      Both pieceSpelled (spelledAppend rest back restSpelled backSpelled)

theorem charsAppend ∀ (front back: List Piece):
    Parse.joinReads (pieceSteps (front ++ back))
      = Parse.joinReads (pieceSteps front) ++ Parse.joinReads (pieceSteps back) :=
  match front with
    | [] => byComputing
    | [piece, ..rest] =>
      rewrite charsAppend rest back then
        (List.appendAssoc piece.chars (Parse.joinReads (pieceSteps rest)) (Parse.joinReads (pieceSteps back))).flipped

-- A declaration laid after what comes before it in the file.

--| Leaves, the newest first, with the oldest given these own-line comments and blank lines: `headed` read from the
--| other end.
def topped (above: List Comment) (blank: Nat): List Leaf → List Leaf
  | [] => []
  | [leaf] => [{ leaf | trivia = { leaf.trivia | leading = above, blankLines = blank } }]
  | [leaf, next, ..rest] => [leaf, ..topped above blank [next, ..rest]]

theorem headedAppend ∀ (above: List Comment) (blank: Nat) (front: List Leaf) (last: Leaf) (tail: List Leaf):
    headed above blank ((front ++ [last]) ++ tail) = headed above blank (front ++ [last]) ++ tail :=
  match front with
    | [] => byComputing
    | [first, ..rest] => byComputing

theorem toppedReverse ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    (topped above blank leaves).reverse = headed above blank leaves.reverse :=
  match leaves with
    | [] => byComputing
    | [leaf] => byComputing
    | [leaf, next, ..rest] =>
      rewrite List.reverseCons leaf (topped above blank [next, ..rest]),
          toppedReverse above blank [next, ..rest],
          List.reverseCons leaf [next, ..rest],
          List.reverseCons next rest,
          headedAppend above blank rest.reverse next [leaf]

--| A layout continued after `earlier` leaves: its oldest leaf holds `above` and `blank`.
def shifted (laid: Laid) (earlier: List Leaf) (above: List Comment) (blank: Nat): Laid :=
  { laid | leaves = topped above blank laid.leaves ++ earlier }

theorem layFilled ∀ (laid: Laid) (piece: Piece)
    (filled: laid.leaves.isEmpty = False):
    (laid.lay piece).leaves.isEmpty = False :=
  match laid with
    | { leaves, pending, blankRun, lineBlank, freshLine, column } =>
      match piece with
        | Code kind text => byComputing
        | Gap count => filled
        | Break => filled
        | Remark text =>
          match freshLine, leaves, filled with
            | True, _, filled => filled
            | False, [last, ..earlier], _ => byComputing
            | False, [], never => cases

--| Laying a piece after earlier leaves is laying it alone, once a leaf has been made.
theorem layShifted ∀ (laid: Laid) (piece: Piece) (earlier: List Leaf) (above: List Comment) (blank: Nat)
    (filled: laid.leaves.isEmpty = False):
    (shifted laid earlier above blank).lay piece = shifted (laid.lay piece) earlier above blank :=
  match laid with
    | { leaves, pending, blankRun, lineBlank, freshLine, column } =>
      match piece with
        | Code kind text =>
          match leaves, filled with
            | [last, ..older], _ => byComputing
            | [], never => cases
        | Gap count => byComputing
        | Break => byComputing
        | Remark text =>
          match freshLine with
            | True => byComputing
            | False =>
              match leaves, filled with
                | [{ token, trivia = { leading, blankLines, trailing } }], _ => byComputing
                | [last, next, ..older], _ => byComputing
                | [], never => cases

theorem foldShifted ∀ (pieces: List Piece) (laid: Laid) (earlier: List Leaf) (above: List Comment) (blank: Nat)
    (filled: laid.leaves.isEmpty = False):
    pieces.foldLeft (shifted laid earlier above blank) Laid.lay
      = shifted (pieces.foldLeft laid Laid.lay) earlier above blank :=
  match pieces with
    | [] => byComputing
    | [piece, ..rest] =>
      rewrite layShifted laid piece earlier above blank filled then
        foldShifted rest (laid.lay piece) earlier above blank (layFilled laid piece filled)

--| The layout at the start of a line after line breaks: leaves made, comments waiting, and blank lines.
def lineStart (leaves: List Leaf) (pending: List Comment) (blank: Nat): Laid :=
  { leaves, pending, blankRun = blank, lineBlank = True, freshLine = True, column = 0 }

--| A token at the start of a line takes the comments and blank lines waiting there.
theorem codeShifted ∀ (kind: Tok) (text: Text) (leaves: List Leaf) (pending: List Comment) (blank: Nat):
    (lineStart leaves pending blank).lay (Code kind text)
      = shifted (Laid.start.lay (Code kind text)) leaves pending.reverse blank :=
  byComputing

-- The file's pieces.

--| The line breaks the file loop writes before an item (`Output.item`): none at the start of the file, else one, or
--| two for a blank line.
def gapPieces (empty blank: Bool): List Piece :=
  if empty then []
  else if blank then [Break, Break]
  else [Break]

--| The pieces of own-line comments, each on its own line.
def notesPieces (empty: Bool): List Note → List Piece
  | [] => []
  | [note, ..rest] => gapPieces empty note.blankBefore ++ [Remark note.text, ..notesPieces False rest]

--| The pieces of declarations, each after its own-line comments (`printDecls`).
def declsPieces (empty: Bool): List Decl → List Piece
  | [] => []
  | [decl, ..rest] =>
    let first := decl.firstComments
    notesPieces empty first.above
      ++ (gapPieces (empty && first.above.isEmpty) first.blankBefore ++ (decl.pieces1 ++ declsPieces False rest))

--| The pieces of the file's text (`SourceFile.printedBy`): a line break ends it unless it is empty.
def filePieces (file: SourceFile): List Piece :=
  if file.decls.isEmpty && file.end.above.isEmpty then []
  else (declsPieces True file.decls ++ notesPieces file.decls.isEmpty file.end.above) ++ [Break]

-- How the layout runs over them.

--| A layout after an item: these leaves and waiting comments, and the line not blank, with no blank lines counted.
def Ends (laid: Laid) (leaves: List Leaf) (pending: List Comment): Prop :=
  laid.leaves = leaves ∧ laid.pending = pending ∧ laid.blankRun = 0 ∧ laid.lineBlank = False

--| The layout before an item: at the start of the file, or after an item.
def Before (empty: Bool) (laid: Laid) (leaves: List Leaf) (pending: List Comment): Prop := match empty with
  | True => laid = lineStart leaves pending 0
  | False => Ends laid leaves pending

theorem gapFrom ∀ (empty blank: Bool) (laid: Laid) (leaves: List Leaf) (pending: List Comment)
    (before: Before empty laid leaves pending):
    (gapPieces empty blank).foldLeft laid Laid.lay = lineStart leaves pending (if blank && !empty then 1 else 0) :=
  match empty, before with
    | True, before => rewrite before, Bool.andFalse blank then byComputing
    | False, (sameLeaves, samePending, noBlank, notBlank) =>
      match laid with
        | { leaves = made, pending = waiting, blankRun, lineBlank, freshLine, column } =>
          rewrite sameLeaves, samePending, noBlank, notBlank then
            match blank with
              | True => byComputing
              | False => byComputing

--| What a run of own-line comments leaves waiting, newest first: `laidNotes` read from the other end.
theorem notesLay ∀ (notes: List Note) (empty: Bool) (laid: Laid) (leaves: List Leaf) (pending: List Comment)
    (before: Before empty laid leaves pending):
    Before
      (empty && notes.isEmpty)
      ((notesPieces empty notes).foldLeft laid Laid.lay)
      leaves
      ((laidNotes empty notes).reverse ++ pending) :=
  match notes with
    | [] => rewrite Bool.andTrue empty then before
    | [note, ..rest] =>
      let gapped := gapFrom empty note.blankBefore laid leaves pending before
      let comment: Comment :=
        { text = withoutReturn note.text, column = 0, blankLines = if note.blankBefore && !empty then 1 else 0 }
      let noted := (lineStart leaves pending (if note.blankBefore && !empty then 1 else 0)).lay (Remark note.text)
      let ends: Ends noted leaves [comment, ..pending] := (byComputing, byComputing, byComputing, byComputing)
      let later := notesLay rest False noted leaves [comment, ..pending] ends
      let sameComment: { noteComment note | blankLines = if empty then 0 else (noteComment note).blankLines }
        = comment :=
        match empty, note.blankBefore with
          | True, True => byComputing
          | True, False => byComputing
          | False, True => byComputing
          | False, False => byComputing
      let first: (laidNotes empty [note, ..rest]).reverse ++ pending
        = (laidNotes False rest).reverse ++ [comment, ..pending] :=
        rewrite laidNotesFalse rest, <- sameComment then
          reverseConsAppend
            { noteComment note | blankLines = if empty then 0 else (noteComment note).blankLines }
            (rest.map noteComment)
            pending
      rewrite Bool.andFalse empty,
          List.foldLeftAppend
            (gapPieces empty note.blankBefore)
            laid
            [Remark note.text, ..notesPieces False rest]
            Laid.lay,
          gapped,
          first then
        later

theorem reverseConsAppend ∀ (first: a) (rest after: List a):
    [first, ..rest].reverse ++ after = rest.reverse ++ [first, ..after] :=
  rewrite List.reverseCons first rest then List.appendAssoc rest.reverse [first] after

theorem laidNotesFalse ∀ (notes: List Note): laidNotes False notes = notes.map noteComment := match notes with
  | [] => byComputing
  | [note, ..rest] => byComputing
