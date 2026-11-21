--| `printedFileLexes1` (SW-4039, ticket B of docs/reviews/SW-4025-output-statements.md): the file loop's text lexes
--| to `SourceFile.lexed`. The text is the lexer proofs' pieces of each item (an own-line comment, or a
--| declaration's printed pieces) after one or two line breaks, so `lexPrintedPairs` reads it as `Laid.lay` folded
--| over them; a declaration laid from the start of a line gives its own leaves, the first holding the comments and
--| blank lines waiting there (`layShifted`), as long as it starts with a token and ends with nothing waiting
--| (`Seamed`, `printedSeam1`: the document leads with `def` and finishes with a token, `printedStart1` and
--| `printedFinish1`).

namespace Fmt.FileLexProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Parse, Result, Text, Void, byDecision)
import Std.Doc.Proofs (
  Every,
  Finishes,
  Joins,
  Leads,
  Plain,
  Uniform,
  leadsConcat,
  printedFinishes,
  printedJoins,
  printedLeads,
  printedPieces,
  spacedComments
)
import Syntax (..)
import Syntax.LexProofs (AllPlain, AllSpelled, Laid, PairsFollow, Piece, lexPrintedPairs, pieceSteps, piecesText)
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
  addPiece,
  pieceOf,
  piecesTextIsConcat,
  remarkSpelled
)
import Fmt.FinishProofs (Final, defFinishes, finalSolid)
import Fmt.CalmProofs (plainDef, plainDefIs)
import Fmt.JoinProofs (doc1Passes)
import Fmt.SpellProofs (closesText, commentsText, declSoundOfSettled, doc1Spells, notesSound, textsAll)
import Fmt.TreeJoinProofs (declJoins, declOperators, declPrintable, declReal, lexKind)
import Fmt.OutputStatements (..)

-- A declaration's pieces.

--| The lexer proofs' pieces of a declaration's printed text, as `Decl.leaves` lays them.
def Decl.pieces (decl: Decl): List Piece := match decl.doc1 with
  | Some doc => pieceFold lexKind (printedPieces doc width)
  | None => []

theorem leavesOfPieces ∀ (decl: Decl): decl.leaves = (decl.pieces.foldLeft Laid.start Laid.lay).leaves.reverse :=
  match decl.doc1 with | Some _ | None => byComputing

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
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    AllPlain decl.pieces
      ∧ AllSpelled decl.pieces
      ∧ PairsFollow decl.pieces
      ∧ (decl.printed1.getOrElse "").toList = Parse.joinReads (pieceSteps decl.pieces) :=
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
  | Break | Remark _ => byComputing

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
  match front with | [] | [_, .._] => byComputing

theorem toppedReverse ∀ (above: List Comment) (blank: Nat) (leaves: List Leaf):
    (topped above blank leaves).reverse = headed above blank leaves.reverse :=
  match leaves with
    | [] | [_] => byComputing
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
      ++ (gapPieces (empty && first.above.isEmpty) first.blankBefore ++ (decl.pieces ++ declsPieces False rest))

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
    | True, before => rewrite before, Bool.andFalse blank
    | False, (sameLeaves, samePending, noBlank, notBlank) =>
      match laid with
        | { leaves = made, pending = waiting, blankRun, lineBlank, freshLine, column } =>
          rewrite sameLeaves, samePending, noBlank, notBlank then cases blank then byComputing

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
          | True, True | False => byComputing
          | False, True | False => byComputing
      let first: (laidNotes empty [note, ..rest]).reverse ++ pending
        = (laidNotes False rest).reverse ++ [comment, ..pending] :=
        rewrite laidNotesFalse rest, <- sameComment then
          List.reverseConsAppend
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

theorem laidNotesFalse ∀ (notes: List Note): laidNotes False notes = notes.map noteComment := match notes with
  | [] | [_, .._] => byComputing

-- A declaration in the file.

--| Nothing waits after the layout: no comment, no blank line, and the line not blank.
def Ended (laid: Laid): Prop := laid.pending = [] ∧ laid.blankRun = 0 ∧ laid.lineBlank = False

--| A declaration's pieces start with a token and leave nothing waiting: its text starts with `def` and ends with a
--| token or the token's trailing comment.
def Seamed (pieces: List Piece): Prop :=
  ∃ (kind: Tok) => ∃ (text: Text) => ∃ (rest: List Piece) => pieces = [Code kind text, ..rest]
    ∧ Ended (pieces.foldLeft Laid.start Laid.lay)

--| What may follow a declaration's last token: spaces and a trailing comment, no line break.
def TailOk: List Piece → Prop
  | [] | [Gap _] | [Remark _] | [Gap _, Remark _] => True
  | _ => False

--| Pieces that start with a token and have no line break after their last one leave nothing waiting: a trailing
--| comment is on the token's line, so it waits for nothing.
theorem seamedOfTail ∀ (pieces front: List Piece) (kind first: Tok) (start text: Text) (rest tail: List Piece)
    (starts: pieces = [Code first start, ..rest])
    (split: pieces = front ++ [Code kind text, ..tail])
    (ok: TailOk tail):
    Seamed pieces :=
  let ended: Ended (pieces.foldLeft Laid.start Laid.lay) :=
    rewrite split, List.foldLeftAppend front Laid.start [Code kind text, ..tail] Laid.lay then
      match tail, ok with | [] | [Gap _] | [Remark _] | [Gap _, Remark _], _ => (byComputing, byComputing, byComputing)
  Witness first (Witness start (Witness rest (Both starts ended)))

--| A plain definition's document starts with its `def` chunk: the keyword's own-line comments are the file's
--| (`hoisted`), and each `Doc.concat` on the way keeps its first document first.
theorem plainDefLeads ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr):
    Leads "def" (plainDef keyword name colon result colonEq value) :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let keywordWord := fixedWord "def" keyword
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let headWords := [keywordWord, name]
  let colonAround := start.next (trailsBack headWords.reverse) 2
  let typeDoc := result.el (start.next colonWord.trails 3)
  let headDoc := spaced (headDocs start headWords)
  let typed := if colonWord.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
  let headerDoc := Doc.concat ([headDoc, colonWord.leaf colonAround 2] ++ typed)
  let inside :=
    (headWords.reverse.drop 1 |> .any Word.trails)
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode headWords).trails)
  let body := bodyAfter value assign (start.next assign.trails (4 + result.size)) False
  let assignLeaf := assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size)
  let keywordLeads: Leads "def" (keywordWord.leaf start 0) :=
    leadsConcat "def" (Doc.text "def") keywordWord.trailing byComputing
  let headLeads: Leads "def" headDoc :=
    leadsConcat "def"
      (keywordWord.leaf start 0)
      [Doc.text " ", name.leaf (start.next keywordWord.trails 1) 1]
      keywordLeads
  let headerLeads: Leads "def" headerDoc :=
    leadsConcat "def" headDoc ([colonWord.leaf colonAround 2] ++ typed) headLeads
  leadsConcat "def"
    (IdGroup 0 headerDoc (headerDoc.forcesBreak || inside))
    [Doc.text " ", assignLeaf, IfBroken 0 body.fst body.snd]
    headerLeads

--| `printedStart1`, the first half of `printedSeam1`: a slice 1 declaration's printed text starts with a token, its
--| `def`, with no space, line break or comment before it: the document leads with the `def` chunk
--| (`plainDefLeads`), which the printer writes first at every width (`printedLeads`).
theorem printedStart1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    ∃ (kind: Tok) => ∃ (text: Text) => ∃ (rest: List Piece) => decl.pieces = [Code kind text, ..rest] :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header, within with
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
          }, _ =>
          match printedLeads "def"
            (plainDef keyword name colon result colonEq value)
            width
            (plainDefLeads keyword name colon result colonEq value)
            byComputing
            byComputing with
            | (more, starts) =>
              let printed :=
                Eq.trans
                  (Eq.cong ((doc: Doc) => printedPieces doc width) (plainDefIs keyword name colon result colonEq value))
                  starts
              Witness
                (lexKind "def")
                (Witness "def"
                  (Witness (pieceFold lexKind more) (Eq.cong ((texts: List Text) => pieceFold lexKind texts) printed)))
        | _, never => cases

-- The end of a declaration's pieces.

--| A comment, starting with `--`, isn't spaces or a line break.
theorem commentShape ∀ (text: Text)
    (starts: text.startsWith "--" = True):
    text.all (char => char == ' ') = False ∧ (text == "\n") = False :=
  match text with
    | MkText [first] => cases
    | MkText [first, second, ..rest] =>
      match dash: Text.sameChar '-' first with
        | True =>
          let firstDash: '-' = first := DecEq.sound (rewrite Text.sameCharEq '-' first at dash then dash)
          rewrite <- firstDash then (byComputing, byComputing)

--| An instance of `commentShape`, so it isn't vacuous: the audit's random search rarely makes a text that starts
--| with `--`.
theorem commentShapeExample: "-- c".all (char => char == ' ') = False ∧ ("-- c" == "\n") = False :=
  commentShape "-- c" byComputing

--| A comment's piece is a remark.
theorem remarkPiece ∀ (kinds: Text → Tok) (text: Text)
    (starts: text.startsWith "--" = True):
    pieceOf kinds text = Remark text :=
  let (notSpaces, notBreak) := commentShape text starts
  rewrite notSpaces, notBreak, starts

--| A token's piece is code.
theorem codePiece ∀ (kinds: Text → Tok) (text: Text) (final: Final text): pieceOf kinds text = Code (kinds text) text :=
  let solid := final.left
  match spaces: text.all (char => char == ' ') with
    | False =>
      match lineBreak: text == "\n" with
        | False => rewrite final.right

--| A piece in front of pieces with code in them takes what is before the code.
theorem addPieceCode ∀ (piece: Piece) (front: List Piece) (kind: Tok) (text: Text) (rest: List Piece):
    addPiece piece (front ++ [Code kind text, ..rest]) = addPiece piece front ++ [Code kind text, ..rest] :=
  cases piece, front then byComputing

--| The pieces of texts with a token among them: those before it, its code, those after it.
theorem pieceFoldCode ∀ (kinds: Text → Tok) (front: List Text) (word: Text) (rest: List Text)
    (code: pieceOf kinds word = Code (kinds word) word):
    pieceFold kinds (front ++ [word, ..rest])
      = pieceFold kinds front ++ [Code (kinds word) word, ..pieceFold kinds rest] :=
  match front with
    | [] => rewrite code
    | [text, ..others] =>
      rewrite pieceFoldCode kinds others word rest code then
        addPieceCode (pieceOf kinds text) (pieceFold kinds others) (kinds word) word (pieceFold kinds rest)

--| A trailing comment after its space is a gap and a remark.
theorem spacedFold ∀ (kinds: Text → Tok) (comment: Text) (comments: List Text)
    (starts: comment.startsWith "--" = True):
    pieceFold kinds (spacedComments [comment, ..comments])
      = [Gap 1, Remark comment, ..pieceFold kinds (spacedComments comments)] :=
  rewrite remarkPiece kinds comment starts

--| Pieces that follow one another after some in front still do.
theorem pairsDrop ∀ (front back: List Piece) (pairs: PairsFollow (front ++ back)): PairsFollow back :=
  match front, back, pairs with
    | [], back, pairs => pairs
    | [piece], [], _ => byComputing
    | [piece], [next, ..more], pairs => pairs.right
    | [piece, second, ..rest], back, pairs => pairsDrop [second, ..rest] back pairs.right

--| What follows a declaration's last token is at most one trailing comment after a space: a comment is followed
--| only by a line break, never by the space before a second.
theorem tailOfComments ∀ (kinds: Text → Tok) (front: List Piece) (code: Piece) (comments: List Text)
    (each: Every commentsText comments)
    (pairs: PairsFollow (front ++ [code, ..pieceFold kinds (spacedComments comments)])):
    TailOk (pieceFold kinds (spacedComments comments)) :=
  match comments, each with
    | [], _ => byComputing
    | [comment], (first, _) => rewrite spacedFold kinds comment [] (Bool.andLeft first)
    | [comment, next, ..more], (first, (second, _)) =>
      let later := pairsDrop front [code, ..pieceFold kinds (spacedComments [comment, next, ..more])] pairs
      rewrite spacedFold kinds comment [next, ..more] (Bool.andLeft first),
          spacedFold kinds next more (Bool.andLeft second) at later then
        match later with
          | (_, (_, (follows, _))) => (List.consNotNil ' ' [] follows).impossible

--| `printedFinish1`, the second half of `printedSeam1`: a slice 1 declaration's printed text has a last token, and
--| after it only a space and a trailing comment on its line.
--|
--| Proof idea: The document finishes with its value's last token in every layout (`defFinishes`), so the printed
--| pieces are those before it, the token, and the trailing comments that wait, each after a space
--| (`printedFinishes`); their pieces split at the token's code (`pieceFoldCode`), and a comment is followed only by
--| a line break (`PairsFollow`, from `declPiecesOk`), so there is at most one (`tailOfComments`).
theorem printedFinish1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    ∃ (front: List Piece) => ∃ (kind: Tok) => ∃ (text: Text) => ∃ (tail: List Piece) => decl.pieces
      = front ++ [Code kind text, ..tail]
      ∧ TailOk tail :=
  let operators := declOperators decl within
  let sound := declSoundOfSettled decl within settled (declReal decl within lexical operators)
  let joins := declJoins decl within shaped sound lexical operators
  let pairs := (declPiecesOk decl within shaped settled lexical).right.right.left
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header, within, joins with
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
          }, _, (_, _, _, _, _, valueJoins) =>
          let doc := defDoc header colonEq value
          let (_, marked, _) := doc1Spells (Definition [] header (Assigned colonEq value)) doc within sound byComputing
          let finishes: Finishes Final doc :=
            defFinishes lexKind keyword name colon result colonEq value (Bool.andRight within) valueJoins
          match printedFinishes Final closesText commentsText doc width finishes finalSolid marked with
            | Witness front (Witness word (Witness comments (Both final (Both quiet printed)))) =>
              let pieces: pieceFold lexKind (printedPieces doc width)
                = pieceFold lexKind front
                  ++ [Code (lexKind word) word, ..pieceFold lexKind (spacedComments comments)] :=
                rewrite printed then
                  pieceFoldCode lexKind front word (spacedComments comments) (codePiece lexKind word final)
              Witness
                (pieceFold lexKind front)
                (Witness
                  (lexKind word)
                  (Witness word
                    (Witness
                      (pieceFold lexKind (spacedComments comments))
                      (Both pieces
                        (tailOfComments lexKind
                          (pieceFold lexKind front)
                          (Code (lexKind word) word)
                          comments
                          quiet
                          (rewrite pieces at pairs then pairs))))))
        | _, never, _ => cases

--| `printedSeam1`: a slice 1 declaration's printed text starts with its `def` and ends with its last token or that
--| token's trailing comment, with no line break after.
theorem printedSeam1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    Seamed decl.pieces :=
  match printedStart1 decl within shaped settled lexical, printedFinish1 decl within shaped settled lexical with
    | Witness first (Witness start (Witness rest starts)), Witness front
        (Witness kind (Witness text (Witness tail (Both split ok)))) =>
      seamedOfTail decl.pieces front kind first start text rest tail starts split ok

--| The layout after a declaration's own-line comments, the line breaks before it and its pieces: its leaves, the
--| first holding the comments and blank line, after the earlier ones, with nothing waiting.
theorem declLay ∀ (decl: Decl) (empty: Bool) (laid: Laid) (leaves: List Leaf)
    (before: Before empty laid leaves [])
    (seam: Seamed decl.pieces):
    Ends
      (decl.pieces.foldLeft
        ((gapPieces (empty && decl.firstComments.above.isEmpty) decl.firstComments.blankBefore).foldLeft
          ((notesPieces empty decl.firstComments.above).foldLeft laid Laid.lay)
          Laid.lay)
        Laid.lay)
      ((decl.laid empty).reverse ++ leaves)
      [] :=
  match seam with
    | Witness kind (Witness text (Witness rest (Both same ended))) =>
      declLaySeamed decl empty laid leaves before kind text rest same ended

theorem declLaySeamed ∀ (decl: Decl) (empty: Bool) (laid: Laid) (leaves: List Leaf)
    (before: Before empty laid leaves [])
    (kind: Tok) (text: Text) (rest: List Piece)
    (same: decl.pieces = [Code kind text, ..rest])
    (ended: Ended (decl.pieces.foldLeft Laid.start Laid.lay)):
    Ends
      (decl.pieces.foldLeft
        ((gapPieces (empty && decl.firstComments.above.isEmpty) decl.firstComments.blankBefore).foldLeft
          ((notesPieces empty decl.firstComments.above).foldLeft laid Laid.lay)
          Laid.lay)
        Laid.lay)
      ((decl.laid empty).reverse ++ leaves)
      [] :=
  let first := decl.firstComments
  let above := laidNotes empty first.above
  let blank: Nat := if first.blankBefore && !(empty && first.above.isEmpty) then 1 else 0
  let noted := notesLay first.above empty laid leaves [] before
  let gapped :=
    gapFrom
      (empty && first.above.isEmpty)
      first.blankBefore
      ((notesPieces empty first.above).foldLeft laid Laid.lay)
      leaves
      (above.reverse ++ [])
      noted
  let waiting: (above.reverse ++ []).reverse = above :=
    rewrite List.appendNil above.reverse then List.reverseReverse above
  let topLeaves: topped above blank (decl.pieces.foldLeft Laid.start Laid.lay).leaves = (decl.laid empty).reverse :=
    rewrite leavesOfPieces decl,
        <- toppedReverse above blank (decl.pieces.foldLeft Laid.start Laid.lay).leaves,
        List.reverseReverse (topped above blank (decl.pieces.foldLeft Laid.start Laid.lay).leaves)
  let laidAfter: decl.pieces.foldLeft (lineStart leaves (above.reverse ++ []) blank) Laid.lay
    = shifted (decl.pieces.foldLeft Laid.start Laid.lay) leaves above blank :=
    rewrite same, codeShifted kind text leaves (above.reverse ++ []) blank, waiting then
      foldShifted rest (Laid.start.lay (Code kind text)) leaves above blank byComputing

  rewrite gapped, laidAfter, topLeaves then (byComputing, ended.left, ended.right.left, ended.right.right)

--| The layout after declarations: their leaves in the file after the earlier ones, nothing waiting.
theorem declsLay ∀ (decls: List Decl) (empty: Bool) (laid: Laid) (leaves: List Leaf)
    (before: Before empty laid leaves [])
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True):
    Before
      (empty && decls.isEmpty)
      ((declsPieces empty decls).foldLeft laid Laid.lay)
      ((groupsFrom empty decls).concat.reverse ++ leaves)
      [] :=
  match decls with
    | [] => rewrite Bool.andTrue empty then before
    | [decl, ..rest] =>
      let first := decl.firstComments
      let notes := notesPieces empty first.above
      let gap := gapPieces (empty && first.above.isEmpty) first.blankBefore
      let later := declsPieces False rest
      let seam :=
        printedSeam1 decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let laidDecl := declLay decl empty laid leaves before seam
      let laidRest :=
        declsLay rest False
          (decl.pieces.foldLeft (gap.foldLeft (notes.foldLeft laid Laid.lay) Laid.lay) Laid.lay)
          ((decl.laid empty).reverse ++ leaves)
          laidDecl
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)
      rewrite Bool.andFalse empty,
          List.foldLeftAppend notes laid (gap ++ (decl.pieces ++ later)) Laid.lay,
          List.foldLeftAppend gap (notes.foldLeft laid Laid.lay) (decl.pieces ++ later) Laid.lay,
          List.foldLeftAppend decl.pieces (gap.foldLeft (notes.foldLeft laid Laid.lay) Laid.lay) later Laid.lay,
          List.reverseAppend (decl.laid empty) (groupsFrom False rest).concat,
          List.appendAssoc (groupsFrom False rest).concat.reverse (decl.laid empty).reverse leaves then
        laidRest

theorem breakEnds ∀ (laid: Laid) (leaves: List Leaf) (pending: List Comment)
    (ends: Ends laid leaves pending):
    (laid.lay Break).leaves = leaves ∧ (laid.lay Break).pending = pending ∧ (laid.lay Break).blankRun = 0 :=
  match laid, ends with
    | { leaves = made, pending = waiting, blankRun, lineBlank, freshLine, column }, (sameLeaves, samePending, noBlank,
        notBlank) => rewrite notBlank then (sameLeaves, samePending, noBlank)

--| The layout of the whole file: the declarations' leaves, and the file's last comments waiting at the end.
theorem fileLaid ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    ((filePieces file).foldLeft Laid.start Laid.lay).leaves.reverse = (groupsFrom True file.decls).concat
      ∧ ((filePieces file).foldLeft Laid.start Laid.lay).pending.reverse = laidNotes file.decls.isEmpty file.end.above
      ∧ ((filePieces file).foldLeft Laid.start Laid.lay).blankRun = 0 :=
  match file with
    | { decls, end } =>
      let body := declsPieces True decls
      let made := (groupsFrom True decls).concat.reverse ++ []
      let declsDone := declsLay decls True Laid.start [] byComputing within shaped (Bool.andLeft settled) lexical
      let notesDone := notesLay end.above decls.isEmpty (body.foldLeft Laid.start Laid.lay) made [] declsDone
      let leavesBack: made.reverse = (groupsFrom True decls).concat :=
        rewrite List.appendNil (groupsFrom True decls).concat.reverse then
          List.reverseReverse (groupsFrom True decls).concat
      let pendingBack: ((laidNotes decls.isEmpty end.above).reverse ++ []).reverse
        = laidNotes decls.isEmpty end.above :=
        rewrite List.appendNil (laidNotes decls.isEmpty end.above).reverse then
          List.reverseReverse (laidNotes decls.isEmpty end.above)
      match nothing: decls.isEmpty && end.above.isEmpty with
        | True =>
          match decls, end.above, nothing with
            | [], [], _ => (byComputing, byComputing, byComputing)
            | [], [note, ..rest], never => cases
        | False =>
          let (sameLeaves, samePending, noBlank) :=
            breakEnds
              ((notesPieces decls.isEmpty end.above).foldLeft (body.foldLeft Laid.start Laid.lay) Laid.lay)
              made
              ((laidNotes decls.isEmpty end.above).reverse ++ [])
              notesDone
          rewrite List.foldLeftAppend (body ++ notesPieces decls.isEmpty end.above) Laid.start [Break] Laid.lay,
              List.foldLeftAppend body Laid.start (notesPieces decls.isEmpty end.above) Laid.lay,
              sameLeaves,
              samePending,
              noBlank,
              leavesBack,
              pendingBack then
            (byComputing, byComputing, byComputing)

-- The file's text is its pieces.

--| The characters of the file loop's texts, the newest first.
def outChars: List Text → List Char
  | [] => []
  | [text, ..earlier] => outChars earlier ++ text.toList

theorem concatReversed ∀ (texts after: List Text):
    List.concat ((texts.reverse ++ after).map Text.toList) = outChars texts ++ List.concat (after.map Text.toList) :=
  match texts with
    | [] => byComputing
    | [text, ..earlier] =>
      rewrite List.reverseCons text earlier,
          List.appendAssoc earlier.reverse [text] after,
          concatReversed earlier [text, ..after] then
        (List.appendAssoc (outChars earlier) text.toList (List.concat (after.map Text.toList))).flipped

--| The file loop's output so far has the characters of these pieces.
def Shows (output: Output) (pieces: List Piece): Prop := outChars output.pieces = Parse.joinReads (pieceSteps pieces)

theorem itemShows ∀ (output: Output) (pieces: List Piece) (blank: Bool) (text: Text) (item: List Piece)
    (shows: Shows output pieces)
    (chars: text.toList = Parse.joinReads (pieceSteps item)):
    Shows (output.item blank text) (pieces ++ (gapPieces output.empty blank ++ item))
      ∧ (output.item blank text).empty = False :=
  match output, shows with
    | { pieces = out, empty }, shows =>
      rewrite charsAppend pieces (gapPieces empty blank ++ item),
          charsAppend (gapPieces empty blank) item,
          <- shows,
          <- chars then
        match empty, blank with
          | True, _ => (byComputing, byComputing)
          | False, True => (List.appendAssoc (outChars out) ['\n', '\n'] text.toList, byComputing)
          | False, False => (List.appendAssoc (outChars out) ['\n'] text.toList, byComputing)

theorem notesShows ∀ (notes: List Note) (output: Output) (pieces: List Piece)
    (shows: Shows output pieces):
    Shows (output.notes notes) (pieces ++ notesPieces output.empty notes)
      ∧ (output.notes notes).empty = (output.empty && notes.isEmpty) :=
  match notes with
    | [] => rewrite List.appendNil pieces, Bool.andTrue output.empty then (shows, byComputing)
    | [note, ..rest] =>
      let gap := gapPieces output.empty note.blankBefore
      let (itemOk, itemFull) :=
        itemShows output pieces note.blankBefore note.text
          [Remark note.text]
          shows
          (List.appendNil note.text.toList).flipped
      let (restOk, restEmpty) :=
        notesShows rest (output.item note.blankBefore note.text) (pieces ++ (gap ++ [Remark note.text])) itemOk
      let joined: (pieces ++ (gap ++ [Remark note.text])) ++ notesPieces False rest
        = pieces ++ notesPieces output.empty [note, ..rest] :=
        rewrite List.appendAssoc pieces (gap ++ [Remark note.text]) (notesPieces False rest),
            List.appendAssoc gap [Remark note.text] (notesPieces False rest)
      (rewrite <- joined, <- itemFull then restOk, rewrite Bool.andFalse output.empty, restEmpty, itemFull)

theorem declsShows ∀ (decls: List Decl) (output: Output) (pieces: List Piece)
    (shows: Shows output pieces)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True):
    Shows (printDecls Decl.printed1 output decls) (pieces ++ declsPieces output.empty decls)
      ∧ (printDecls Decl.printed1 output decls).empty = (output.empty && decls.isEmpty) :=
  match decls with
    | [] => rewrite List.appendNil pieces, Bool.andTrue output.empty then (shows, byComputing)
    | [decl, ..rest] =>
      let first := decl.firstComments
      let notes := notesPieces output.empty first.above
      let noted := output.notes first.above
      let (notedOk, notedEmpty) := notesShows first.above output pieces shows
      let gap := gapPieces (output.empty && first.above.isEmpty) first.blankBefore
      let (_, _, _, chars) :=
        declPiecesOk decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let (itemOk, itemFull) :=
        itemShows noted (pieces ++ notes) first.blankBefore (decl.printed1.getOrElse "") decl.pieces notedOk chars
      let item := noted.item first.blankBefore (decl.printed1.getOrElse "")
      let (restOk, restEmpty) :=
        declsShows rest item
          ((pieces ++ notes) ++ (gap ++ decl.pieces))
          (rewrite <- notedEmpty then itemOk)
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)
      let joined: ((pieces ++ notes) ++ (gap ++ decl.pieces)) ++ declsPieces False rest
        = pieces ++ declsPieces output.empty [decl, ..rest] :=
        rewrite List.appendAssoc (pieces ++ notes) (gap ++ decl.pieces) (declsPieces False rest),
            List.appendAssoc pieces notes ((gap ++ decl.pieces) ++ declsPieces False rest),
            List.appendAssoc gap decl.pieces (declsPieces False rest)
      (rewrite <- joined, <- itemFull then restOk, rewrite Bool.andFalse output.empty, restEmpty, itemFull)

--| The file's text is the text of its pieces.
theorem fileText ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    file.printed1 = piecesText (filePieces file) :=
  match file with
    | { decls, end } =>
      let start: Output := { pieces = [], empty = True }
      let body := printDecls Decl.printed1 start decls
      let (bodyOk, bodyEmpty) := declsShows decls start [] byComputing within shaped (Bool.andLeft settled) lexical
      let (doneOk, doneEmpty) := notesShows end.above body ([] ++ declsPieces True decls) bodyOk
      let done := body.notes end.above
      match nothing: decls.isEmpty && end.above.isEmpty with
        | True => rewrite doneEmpty, bodyEmpty, nothing
        | False =>
          rewrite doneEmpty, bodyEmpty, nothing then
            Text.ext _ _
              (rewrite Text.concatToList ["\n", ..done.pieces].reverse,
                  List.reverseCons "\n" done.pieces,
                  concatReversed done.pieces ["\n"],
                  Text.toFromList
                    (Parse.joinReads
                      (pieceSteps ((declsPieces True decls ++ notesPieces decls.isEmpty end.above) ++ [Break]))),
                  charsAppend (declsPieces True decls ++ notesPieces decls.isEmpty end.above) [Break],
                  doneOk,
                  bodyEmpty)

-- The file's pieces lex.

theorem remarkOk ∀ (text: Text) (comment: commentText text = True): (Remark text).Plain ∧ (Remark text).Spells :=
  remarkSpelled text (Bool.andLeft comment) (Bool.notTrue _ (Bool.andLeft (Bool.andRight comment)))

--| Line breaks may come before any pieces that follow one another.
theorem gapPairs ∀ (empty blank: Bool) (pieces: List Piece)
    (pairs: PairsFollow pieces):
    PairsFollow (gapPieces empty blank ++ pieces) :=
  match empty, blank, pieces with
    | True, _, _ => pairs
    | False, True, [] => (byComputing, byComputing)
    | False, True, [piece, ..rest] => (byComputing, byComputing, pairs)
    | False, False, [] => byComputing
    | False, False, [piece, ..rest] => (byComputing, pairs)

theorem gapOk ∀ (empty blank: Bool): AllPlain (gapPieces empty blank) ∧ AllSpelled (gapPieces empty blank) :=
  match empty, blank with
    | True, _ => (byComputing, byComputing)
    | False, True => ((byComputing, byComputing, byComputing), (byComputing, byComputing, byComputing))
    | False, False => ((byComputing, byComputing), (byComputing, byComputing))

theorem gapLed ∀ (blank: Bool) (pieces: List Piece): startsBreak (gapPieces False blank ++ pieces) = True :=
  match blank with | True | False => byComputing

--| The pieces of own-line comments are plain, spelled and follow one another, and after the first item they start
--| with a line break.
theorem notesOk ∀ (empty: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    AllPlain (notesPieces empty notes)
      ∧ AllSpelled (notesPieces empty notes)
      ∧ PairsFollow (notesPieces empty notes)
      ∧ ((notesPieces False notes).isEmpty || startsBreak (notesPieces False notes)) = True :=
  match notes with
    | [] => (byComputing, byComputing, byComputing, byComputing)
    | [note, ..rest] =>
      let (remarkPlain, remarkSpells) := remarkOk note.text (Bool.andLeft sound)
      let (restPlain, restSpelled, restPairs, restLed) := notesOk False rest (Bool.andRight sound)
      let (gapPlain, gapSpelled) := gapOk empty note.blankBefore
      let remarkPairs: PairsFollow [Remark note.text, ..notesPieces False rest] :=
        pairsAppend [Remark note.text] (notesPieces False rest) byComputing restPairs restLed
      (
        plainAppend
          (gapPieces empty note.blankBefore)
          [Remark note.text, ..notesPieces False rest]
          gapPlain
          (Both remarkPlain restPlain),
        spelledAppend
          (gapPieces empty note.blankBefore)
          [Remark note.text, ..notesPieces False rest]
          gapSpelled
          (Both remarkSpells restSpelled),
        gapPairs empty note.blankBefore [Remark note.text, ..notesPieces False rest] remarkPairs,
        rewrite gapLed note.blankBefore [Remark note.text, ..notesPieces False rest],
            Bool.orTrue (gapPieces False note.blankBefore ++ [Remark note.text, ..notesPieces False rest]).isEmpty
      )

--| A declaration's own-line comments are comments as rule N leaves them.
theorem firstNotesSound ∀ (decl: Decl)
    (within: decl.within1 = True)
    (settled: decl.settled = True):
    notesSound decl.firstComments.above = True :=
  match decl, within with
    | Definition [] header (Assigned colonEq value), _ =>
      let first := Bool.andLeft (Bool.andRight (Bool.andRight settled))
      Bool.andLeft (rewrite textsAll header.keyword.above header.keyword.after at first then first)

theorem notesGapLed ∀ (empty blank: Bool) (above: List Note) (rest: List Piece):
    ((notesPieces empty above).isEmpty
      || (gapPieces (empty && above.isEmpty) blank ++ rest).isEmpty
      || startsBreak (gapPieces (empty && above.isEmpty) blank ++ rest))
      = True :=
  match above with
    | [] => byComputing
    | [note, ..more] => rewrite Bool.andFalse empty then Bool.orRight (Bool.orRight (gapLed blank rest))

theorem declsLed ∀ (above: List Note) (blank: Bool) (rest: List Piece):
    startsBreak (notesPieces False above ++ (gapPieces (False && above.isEmpty) blank ++ rest)) = True :=
  match above with
    | [] => gapLed blank rest
    | [note, ..more] =>
      rewrite List.appendAssoc
            (gapPieces False note.blankBefore)
            [Remark note.text, ..notesPieces False more]
            (gapPieces False blank ++ rest) then
        gapLed note.blankBefore ([Remark note.text, ..notesPieces False more] ++ (gapPieces False blank ++ rest))

--| The pieces of declarations are plain, spelled and follow one another, and after the first item they start with
--| a line break.
theorem declsOk ∀ (empty: Bool) (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True):
    AllPlain (declsPieces empty decls)
      ∧ AllSpelled (declsPieces empty decls)
      ∧ PairsFollow (declsPieces empty decls)
      ∧ ((declsPieces False decls).isEmpty || startsBreak (declsPieces False decls)) = True :=
  match decls with
    | [] => (byComputing, byComputing, byComputing, byComputing)
    | [decl, ..rest] =>
      let first := decl.firstComments
      let notes := notesPieces empty first.above
      let gap := gapPieces (empty && first.above.isEmpty) first.blankBefore
      let later := declsPieces False rest
      let (laterPlain, laterSpelled, laterPairs, laterLed) :=
        declsOk False rest (Bool.andRight within) (Bool.andRight shaped) (Bool.andRight settled) (Bool.andRight lexical)
      let (declPlain, declSpelled, declPairs, _) :=
        declPiecesOk decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let (notesPlain, notesSpelled, notesPairs, _) :=
        notesOk empty first.above (firstNotesSound decl (Bool.andLeft within) (Bool.andLeft settled))
      let (gapPlain, gapSpelled) := gapOk (empty && first.above.isEmpty) first.blankBefore
      let tailPairs: PairsFollow (decl.pieces ++ later) :=
        pairsAppend decl.pieces later declPairs laterPairs (Bool.orRight laterLed)
      let gappedPairs: PairsFollow (gap ++ (decl.pieces ++ later)) :=
        gapPairs (empty && first.above.isEmpty) first.blankBefore (decl.pieces ++ later) tailPairs
      (
        plainAppend notes
          (gap ++ (decl.pieces ++ later))
          notesPlain
          (plainAppend gap (decl.pieces ++ later) gapPlain (plainAppend decl.pieces later declPlain laterPlain)),
        spelledAppend notes
          (gap ++ (decl.pieces ++ later))
          notesSpelled
          (spelledAppend gap
            (decl.pieces ++ later)
            gapSpelled
            (spelledAppend decl.pieces later declSpelled laterSpelled)),
        pairsAppend notes
          (gap ++ (decl.pieces ++ later))
          notesPairs
          gappedPairs
          (notesGapLed empty first.blankBefore first.above (decl.pieces ++ later)),
        Bool.orRight (declsLed first.above first.blankBefore (decl.pieces ++ later))
      )

--| The file's pieces are plain, spelled and follow one another.
theorem filePiecesOk ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    AllPlain (filePieces file) ∧ AllSpelled (filePieces file) ∧ PairsFollow (filePieces file) :=
  match file with
    | { decls, end } =>
      let endTexts := Bool.andLeft (Bool.andRight settled)
      let endSound := Bool.andLeft (rewrite textsAll end.above end.after at endTexts then endTexts)
      let (declsPlain, declsSpelled, declsPairs, _) := declsOk True decls within shaped (Bool.andLeft settled) lexical
      let (notesPlain, notesSpelled, notesPairs, notesLed) := notesOk decls.isEmpty end.above endSound
      let body := declsPieces True decls ++ notesPieces decls.isEmpty end.above
      let joinable: ((declsPieces True decls).isEmpty
        || (notesPieces decls.isEmpty end.above).isEmpty
        || startsBreak (notesPieces decls.isEmpty end.above))
        = True :=
        match decls with
          | [] => byComputing
          | [decl, ..rest] => Bool.orRight notesLed
      let bodyPairs :=
        pairsAppend (declsPieces True decls) (notesPieces decls.isEmpty end.above) declsPairs notesPairs joinable
      match decls.isEmpty && end.above.isEmpty with
        | True => (byComputing, byComputing, byComputing)
        | False => (
          plainAppend body
            [Break]
            (plainAppend (declsPieces True decls) (notesPieces decls.isEmpty end.above) declsPlain notesPlain)
            (byComputing, byComputing),
          spelledAppend body
            [Break]
            (spelledAppend (declsPieces True decls) (notesPieces decls.isEmpty end.above) declsSpelled notesSpelled)
            (byComputing, byComputing),
          pairsAppend body [Break] bodyPairs byComputing (Bool.orRight byComputing)
        )

--| `printedFileLexes1`: the file loop's text lexes, to the declarations' leaves in order, each `def` holding its
--| declaration's own-line comments, and the file's last comments at the end.
--|
--| Proof idea: the text is the file's pieces (`fileText`), which are plain, spelled and follow one another
--| (`filePiecesOk`), so `lexPrintedPairs` reads it as `Laid.lay` folded over them; that fold makes each declaration's
--| leaves after the earlier ones, the first holding the comments and blank line before it (`fileLaid`).
theorem printedFileLexes1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    lex file.printed1 = Ok file.lexed :=
  let (plain, spelled, pairs) := filePiecesOk file within shaped settled lexical
  let (leavesOk, pendingOk, blankOk) := fileLaid file within shaped settled lexical
  rewrite fileText file within shaped settled lexical,
      lexPrintedPairs (filePieces file) plain spelled pairs,
      leavesOk,
      pendingOk,
      blankOk
