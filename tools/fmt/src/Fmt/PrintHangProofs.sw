--| From the printer's trace to the lexer's leaves, for `printedHangs` (docs/proposals/self-hosted-fmt-s1-sketch.md
--| §1.4, ticket 18e): the fold `Fmt.HangProofs.hangOf` takes over the trace of the printed pieces (`eventsOf`) as
--| `hangs` does over the leaves the lexer reads of the same pieces (`Laid.lay`, columns in bytes), so a fold that
--| never broke over the trace means the leaves keep the line rule.
--|
--| A leaf the lexer reads starts its line exactly when the trace's event does (only spaces before it on its line,
--| as no code follows a comment on its line), and then at the same column: the spaces before it, in bytes as in
--| characters. Where it doesn't start its line its column differs, but `HangState.step` doesn't read it then.

namespace Fmt.PrintHangProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (Carry)
import Std.Doc.Proofs (
  AtStart,
  Event,
  Every,
  Joins,
  Pairs,
  Plain,
  Uniform,
  eventsOf,
  isLayout,
  lineBlank,
  lineWidth,
  printedJoins,
  printedPieces
)
import Syntax (Comment, Leaf, Lexed, Tok, Token, Trivia, lex, withTrailing)
import Syntax.LexProofs (Laid, Piece)
import Fmt (HangState, hangs, hangsFrom, startBlocks)
import Fmt.HangProofs (
  Hang,
  HangLays,
  blankHang,
  codeEvent,
  eventLeaf,
  hangCode,
  hangOf,
  hangSnoc,
  hangStep,
  hangsPrinted,
  staleBlocks
)
import Fmt.PrintLexProofs (Follows, Printable, addPiece, pieceFold, pieceOf, printedLexes)

-- The fold over the leaves.

--| A leaf as `hangs` takes it: the declaration's `def` at column 0 first, then `HangState.step`.
def leafHang (hang: Hang) (leaf: Leaf): Hang := match hang with
  | Opening => if leaf.token.kind == KwDef && leaf.token.column == 0 then Hang.At HangState.initial else Broke
  | Hang.At state => Hang.ofStep (state.step leaf)
  | Broke => Broke

--| The fold over leaves, the newest first, as the lexer's layout keeps them.
def leavesHang: List Leaf → Hang
  | [] => Opening
  | [leaf, ..older] => leafHang (leavesHang older) leaf

theorem brokeStays ∀ (leaves: List Leaf): leaves.foldLeft Broke leafHang = Broke := match leaves with
  | [] => byComputing
  | [leaf, ..rest] => brokeStays rest

--| Leaves after a state the fold never broke on keep the line rule from it.
theorem hangsFromFold ∀ (state: HangState) (leaves: List Leaf)
    (whole: leaves.foldLeft (Hang.At state) leafHang ≠ Broke):
    hangsFrom state leaves = True :=
  match leaves, whole with
    | [], _ => byComputing
    | [leaf, ..rest], whole =>
      match stepped: state.step leaf, whole with
        | Some next, whole => hangsFromFold next rest whole
        | None, whole => (whole (brokeStays rest)).impossible

--| A declaration's leaves, oldest first, keep the line rule where the fold never broke.
theorem hangsOfFold ∀ (leaves: List Leaf) (whole: leaves.foldLeft Opening leafHang ≠ Broke): hangs leaves = True :=
  match leaves, whole with
    | [], _ => byComputing
    | [first, ..rest], whole =>
      match isDef: first.token.kind == KwDef, zero: first.token.column == 0, whole with
        | True, True, whole => hangsFromFold HangState.initial rest whole
        | True, False, whole => (whole (brokeStays rest)).impossible
        | False, _, whole => (whole (brokeStays rest)).impossible

theorem leavesHangFold ∀ (leaves: List Leaf): leavesHang leaves = leaves.reverse.foldLeft Opening leafHang :=
  match leaves with
    | [] => byComputing
    | [leaf, ..older] =>
      rewrite List.reverseCons leaf older,
          List.foldLeftAppend older.reverse Opening [leaf] leafHang,
          <- leavesHangFold older

--| A leaf steps by its token alone.
theorem stepTrivia ∀ (state: HangState) (token: Token) (one other: Trivia):
    state.step { token, trivia = one } = state.step { token, trivia = other } :=
  match state with | { blocks = ([] | [_, .._]), top, start, glue } => byComputing

--| A comment trailing the newest leaf changes no token.
theorem trailingHangSame ∀ (leaves: List Leaf) (comment: Comment):
    leavesHang (withTrailing leaves comment) = leavesHang leaves :=
  match leaves with
    | [] => byComputing
    | [{ token, trivia }, ..earlier] =>
      match leavesHang earlier with
        | Opening => byComputing
        | Hang.At state => rewrite stepTrivia state token { trivia | trailing = Some comment } trivia
        | Broke => byComputing

-- The step's columns.

--| A leaf that doesn't start its line steps the same at any column, whatever its comments.
theorem stepColumn ∀ (state: HangState) (kind: Tok) (text: Text) (first second: Nat) (one other: Trivia):
    state.step { token = { kind, text, column = first, lineStart = False }, trivia = one }
      = state.step { token = { kind, text, column = second, lineStart = False }, trivia = other } :=
  match state with
    | { blocks, top, start, glue } => rewrite Bool.andFalse glue, Bool.andFalse start, staleBlocks first blocks

-- The two folds, piece by piece.

--| The fold over the trace refines the fold over the leaves: broken, or the same.
def Refines (event leaf: Hang): Prop := event = Broke ∨ event = leaf

--| A code piece's event and leaf step alike: they start their line together, at the same column if they do.
--|
--| Proof idea: by cases on the folds and on whether the piece starts its line; at the `def` the conditions agree, and
--| after it `HangState.step` reads the same token, the column only where the line starts (`stepColumn`), and no trivia
--| (`stepTrivia`).
theorem codeRefines ∀ (kinds: Text → Tok) (text: Text) (blank: Bool) (width column: Nat)
    (event leaf: Hang) (trivia: Trivia)
    (refines: Refines event leaf)
    (lands: blank = True → column = width):
    Refines
      (hangCode kinds event { word = text, start = if blank then Some width else None })
      (leafHang leaf { token = { kind = kinds text, text, column, lineStart = blank }, trivia }) :=
  match refines with
    | Inl broke => rewrite broke then Inl byComputing
    | Inr same =>
      rewrite same then
        match leaf, blank, lands with
          | Opening, True, lands => rewrite lands byComputing then Inr byComputing
          | Opening, False, _ => Inl (rewrite Bool.andFalse (kinds text == KwDef))
          | Hang.At state, True, lands =>
            rewrite lands byComputing then
              Inr
                (rewrite stepTrivia state
                  { kind = kinds text, text, column = width, lineStart = True }
                  { leading = [], blankLines = 0, trailing = None }
                  trivia)
          | Hang.At state, False, _ =>
            Inr
              (rewrite stepColumn state
                (kinds text)
                text
                0
                column
                { leading = [], blankLines = 0, trailing = None }
                trivia)
          | Broke, _, _ => Inl byComputing

--| The lexer's layout of the output's texts, the last first, each read as `pieceOf` reads it.
def laidOf (kinds: Text → Tok): List Text → Laid
  | [] => Laid.start
  | [text, ..earlier] => (laidOf kinds earlier).lay (pieceOf kinds text)

--| Whether the last text is a comment.
def lastComment: List Text → Bool
  | [] => False
  | [text, .._] => text.startsWith "--"

--| No text follows a comment on its line: a line break comes next (the texts the last first).
def CommentsEnd: List Text → Prop
  | [] | [_] => True
  | [text, earlier, ..rest] => (earlier.startsWith "--" = True → text = "\n") ∧ CommentsEnd [earlier, ..rest]

--| What the layout and the trace agree on after some texts: at a line with only spaces on it, a fresh line at its
--| width; on any other, not a fresh line unless a comment ends it; and the folds.
def Tracks (kinds: Text → Tok) (laid: Laid) (events: List Event) (blank: Bool) (width: Nat) (note: Bool): Prop :=
  (blank = True → laid.freshLine = True ∧ laid.column = width)
    ∧ (blank = False → laid.freshLine = False ∨ note = True)
    ∧ Refines (hangOf kinds events) (leavesHang laid.leaves)

theorem afterComment ∀ (text: Text) (earlier: List Text)
    (ends: CommentsEnd [text, ..earlier])
    (note: lastComment earlier = True):
    text = "\n" :=
  match earlier, ends, note with
    | [], _, never => (Bool.falseNotTrue never).impossible
    | [previous, ..rest], (after, _), note => after note

--| Where the line has only spaces, the next code piece starts it, at its width.
theorem freshIsBlank ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (ends: CommentsEnd [text, ..earlier])
    (notBreak: (text == "\n") = False)
    (blankBefore: lineBlank earlier = True
      → (laidOf kinds earlier).freshLine = True ∧ (laidOf kinds earlier).column = lineWidth earlier)
    (fresh: lineBlank earlier = False → (laidOf kinds earlier).freshLine = False ∨ lastComment earlier = True):
    (laidOf kinds earlier).freshLine = lineBlank earlier :=
  match blank: lineBlank earlier, blankBefore, fresh with
    | True, blankBefore, _ => (blankBefore byComputing).left
    | False, _, fresh =>
      match fresh byComputing with
        | Inl stale => stale
        | Inr note =>
          let broken := afterComment text earlier ends note
          (Bool.trueNotFalse (rewrite broken at notBreak then notBreak)).impossible

theorem endsRest ∀ (text: Text) (earlier: List Text) (ends: CommentsEnd [text, ..earlier]): CommentsEnd earlier :=
  match earlier, ends with
    | [], _ => byComputing
    | [previous, ..rest], (_, others) => others

--| Spaces widen the line and change no fold.
theorem tracksSpaces ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = True)
    (ends: CommentsEnd [text, ..earlier])
    (before: Tracks kinds
      (laidOf kinds earlier)
      (eventsOf earlier)
      (lineBlank earlier)
      (lineWidth earlier)
      (lastComment earlier)):
    Tracks kinds
      (laidOf kinds [text, ..earlier])
      (eventsOf [text, ..earlier])
      (lineBlank [text, ..earlier])
      (lineWidth [text, ..earlier])
      (lastComment [text, ..earlier]) :=
  let notBreak := Doc.Proofs.gapNoBreak text spaces
  let (blankBefore, fresh, refines) := before
  let laid := laidOf kinds earlier
  let blank: lineBlank [text, ..earlier] = lineBlank earlier := rewrite spaces
  let width: lineWidth [text, ..earlier] = text.length + lineWidth earlier := rewrite notBreak
  let events: eventsOf [text, ..earlier] = eventsOf earlier := rewrite spaces, notBreak
  let wider: laidOf kinds [text, ..earlier] = { laid | column = laid.column + text.length } := rewrite spaces
  rewrite blank, width, events, wider then
    (
      onlySpaces =>
        let (started, column) := blankBefore onlySpaces
        (started, arithmetic),
      words =>
        match fresh words with
          | Inl stale => Inl stale
          | Inr note =>
            let broken := afterComment text earlier ends note
            (Bool.trueNotFalse (rewrite broken at notBreak then notBreak)).impossible,
      refines
    )

--| A line break starts a fresh line; a blank line is skipped.
theorem tracksBreak ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = True)
    (before: Tracks kinds
      (laidOf kinds earlier)
      (eventsOf earlier)
      (lineBlank earlier)
      (lineWidth earlier)
      (lastComment earlier)):
    Tracks kinds
      (laidOf kinds [text, ..earlier])
      (eventsOf [text, ..earlier])
      (lineBlank [text, ..earlier])
      (lineWidth [text, ..earlier])
      (lastComment [text, ..earlier]) :=
  let (_, _, refines) := before
  let laid := laidOf kinds earlier
  let blank: lineBlank [text, ..earlier] = True := rewrite spaces, broken
  let width: lineWidth [text, ..earlier] = 0 := rewrite broken
  let fresh: laidOf kinds [text, ..earlier] = laid.lay Break := rewrite spaces, broken
  let skipped: hangOf kinds (eventsOf [text, ..earlier]) = hangOf kinds (eventsOf earlier) :=
    rewrite spaces, broken then
      match lineBlank earlier with
        | True => blankHang kinds (eventsOf earlier)
        | False => byComputing
  rewrite blank, width, fresh, skipped then
    ((_ => (byComputing, byComputing)), (never => (Bool.trueNotFalse never).impossible), refines)

--| A comment changes no fold: the trace skips it, and the layout holds it as trivia.
theorem tracksRemark ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = False)
    (comment: text.startsWith "--" = True)
    (before: Tracks kinds
      (laidOf kinds earlier)
      (eventsOf earlier)
      (lineBlank earlier)
      (lineWidth earlier)
      (lastComment earlier)):
    Tracks kinds
      (laidOf kinds [text, ..earlier])
      (eventsOf [text, ..earlier])
      (lineBlank [text, ..earlier])
      (lineWidth [text, ..earlier])
      (lastComment [text, ..earlier]) :=
  let (_, _, refines) := before
  let laid := laidOf kinds earlier
  let event: Event := { word = text, start = if lineBlank earlier then Some (lineWidth earlier) else None }
  let blank: lineBlank [text, ..earlier] = False := rewrite spaces, broken
  let noted: laidOf kinds [text, ..earlier] = laid.lay (Remark text) := rewrite spaces, broken, comment
  let skipped: hangOf kinds (eventsOf [text, ..earlier]) = hangOf kinds (eventsOf earlier) :=
    rewrite spaces, broken, hangSnoc kinds (eventsOf earlier) event, comment
  let same: leavesHang (laid.lay (Remark text)).leaves = leavesHang laid.leaves := match laid.freshLine with
    | True => byComputing
    | False => trailingHangSame laid.leaves _
  rewrite blank, noted, skipped then
    ((never => (Bool.falseNotTrue never).impossible), (_ => Inr comment), rewrite same then refines)

--| A token is a leaf: it starts its line when the trace's event does, at the same column.
theorem tracksCode ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = False)
    (comment: text.startsWith "--" = False)
    (ends: CommentsEnd [text, ..earlier])
    (before: Tracks kinds
      (laidOf kinds earlier)
      (eventsOf earlier)
      (lineBlank earlier)
      (lineWidth earlier)
      (lastComment earlier)):
    Tracks kinds
      (laidOf kinds [text, ..earlier])
      (eventsOf [text, ..earlier])
      (lineBlank [text, ..earlier])
      (lineWidth [text, ..earlier])
      (lastComment [text, ..earlier]) :=
  let (blankBefore, fresh, refines) := before
  let laid := laidOf kinds earlier
  let event: Event := { word = text, start = if lineBlank earlier then Some (lineWidth earlier) else None }
  let blank: lineBlank [text, ..earlier] = False := rewrite spaces, broken
  let token: laidOf kinds [text, ..earlier] = laid.lay (Code (kinds text) text) := rewrite spaces, broken, comment
  let stepped: hangOf kinds (eventsOf [text, ..earlier]) = hangCode kinds (hangOf kinds (eventsOf earlier)) event :=
    rewrite spaces, broken, hangSnoc kinds (eventsOf earlier) event, comment, broken
  let sameLine := freshIsBlank kinds text earlier ends broken blankBefore fresh
  rewrite blank, token, stepped then
    (
      (never => (Bool.falseNotTrue never).impossible),
      (_ => Inl byComputing),
      rewrite sameLine then
        codeRefines kinds text
          (lineBlank earlier)
          (lineWidth earlier)
          laid.column
          (hangOf kinds (eventsOf earlier))
          (leavesHang laid.leaves)
          { leading = laid.pending.reverse, blankLines = laid.blankRun, trailing = None }
          refines
          (onlySpaces => (blankBefore onlySpaces).right)
    )

--| Over the output's texts (the last first), where no text follows a comment on its line, the layout and the trace
--| agree (`Tracks`).
--|
--| Proof idea: by induction on the texts, one piece at a time: spaces, a line break, a comment and a token each keep
--| the agreement (`tracksSpaces`, `tracksBreak`, `tracksRemark`, `tracksCode`).
theorem tracks ∀ (kinds: Text → Tok) (texts: List Text)
    (ends: CommentsEnd texts):
    Tracks kinds (laidOf kinds texts) (eventsOf texts) (lineBlank texts) (lineWidth texts) (lastComment texts) :=
  match texts, ends with
    | [], _ => ((_ => (byComputing, byComputing)), (never => (Bool.trueNotFalse never).impossible), Inr byComputing)
    | [text, ..earlier], ends =>
      let goal: Prop :=
        Tracks kinds
          (laidOf kinds [text, ..earlier])
          (eventsOf [text, ..earlier])
          (lineBlank [text, ..earlier])
          (lineWidth [text, ..earlier])
          (lastComment [text, ..earlier])
      let before := tracks kinds earlier (endsRest text earlier ends)
      Bool.inspect
        (text.all (char => char == ' '))
        (_ => goal)
        (spaces => tracksSpaces kinds text earlier spaces ends before)
        (spaces =>
          Bool.inspect
            (text == "\n")
            (_ => goal)
            (broken => tracksBreak kinds text earlier spaces broken before)
            (broken =>
              Bool.inspect
                (text.startsWith "--")
                (_ => goal)
                (comment => tracksRemark kinds text earlier spaces broken comment before)
                (comment => tracksCode kinds text earlier spaces broken comment ends before)))

-- From the lexer's pieces to the texts.

--| Spaces after spaces lay as one run of them.
theorem addPieceLay ∀ (piece: Piece) (rest: List Piece) (laid: Laid):
    (addPiece piece rest).foldLeft laid Laid.lay = rest.foldLeft (laid.lay piece) Laid.lay :=
  match piece, rest with
    | Gap first, [Gap second, ..more] =>
      let joined: laid.lay (Gap (first + second)) = (laid.lay (Gap first)).lay (Gap second) :=
        rewrite Nat.addAssoc laid.column first second
      rewrite joined
    | _, _ => cases piece, rest then byComputing

--| The lexer's pieces of the texts lay as the texts do, one at a time.
theorem pieceFoldLay ∀ (kinds: Text → Tok) (texts: List Text) (laid: Laid):
    (pieceFold kinds texts).foldLeft laid Laid.lay
      = texts.foldLeft laid (later text => later.lay (pieceOf kinds text)) :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      rewrite addPieceLay (pieceOf kinds text) (pieceFold kinds rest) laid then
        pieceFoldLay kinds rest (laid.lay (pieceOf kinds text))

theorem laidOfFold ∀ (kinds: Text → Tok) (texts: List Text):
    laidOf kinds texts = texts.reverse.foldLeft Laid.start (later text => later.lay (pieceOf kinds text)) :=
  match texts with
    | [] => byComputing
    | [text, ..earlier] =>
      rewrite List.reverseCons text earlier,
          List.foldLeftAppend earlier.reverse Laid.start [text] (later text => later.lay (pieceOf kinds text)),
          <- laidOfFold kinds earlier

--| The leaves the lexer reads of the printed texts keep the line rule where the fold over the trace never broke and
--| no text follows a comment on its line.
--|
--| Proof idea: the lexer's pieces lay as the texts do one at a time (`pieceFoldLay`), which is `laidOf` of the texts
--| the last first; there the trace's fold refines the leaves' (`tracks`), so it never broke either (`hangsOfFold`).
theorem leavesHangOfTrace ∀ (kinds: Text → Tok) (texts: List Text)
    (ends: CommentsEnd texts.reverse)
    (whole: hangOf kinds (eventsOf texts.reverse) ≠ Broke):
    hangs ((pieceFold kinds texts).foldLeft Laid.start Laid.lay).leaves.reverse = True :=
  let laid: (pieceFold kinds texts).foldLeft Laid.start Laid.lay = laidOf kinds texts.reverse :=
    rewrite pieceFoldLay kinds texts Laid.start, laidOfFold kinds texts.reverse, List.reverseReverse texts
  let (_, _, refines) := tracks kinds texts.reverse ends
  let leavesWhole: leavesHang (laidOf kinds texts.reverse).leaves ≠ Broke := match refines with
    | Inl broke => (whole broke).impossible
    | Inr same => rewrite <- same then whole
  rewrite laid then
    hangsOfFold
      (laidOf kinds texts.reverse).leaves.reverse
      (rewrite <- leavesHangFold (laidOf kinds texts.reverse).leaves then leavesWhole)

-- The printer's pieces.

--| A comment isn't layout: it starts `--`.
theorem commentLayout ∀ (text: Text) (starts: text.startsWith "--" = True): isLayout text = False := match text with
  | MkText [first, ..rest] =>
    match same: Text.sameChar '-' first with
      | True => rewrite (DecEq.sound (rewrite Text.sameCharEq '-' first at same then same)).flipped

--| Pieces that may stand after one another have no text after a comment on its line.
theorem pairsEnd ∀ (kinds: Text → Tok) (out: List Text) (pairs: Pairs (Follows kinds) out): CommentsEnd out :=
  match out, pairs with
    | [] | [_], _ => byComputing
    | [text, earlier, ..rest], (_, pair, others) => (
      comment =>
        match pair with
          | Inl layout => (Bool.falseNotTrue (rewrite commentLayout earlier comment at layout then layout)).impossible
          | Inr (Inl broken) => broken
          | Inr (Inr (notComment, _)) => (Bool.trueNotFalse (rewrite comment at notComment then notComment)).impossible,
      pairsEnd kinds [earlier, ..rest] others
    )

--| The engine's half of `printedHangs`: a document whose every layout keeps the fold unbroken from the start of the
--| output (the rules' triple, `HangLays`), and whose pieces the lexer reads (`printedLexes`' hypotheses), prints text
--| whose leaves keep the line rule.
--|
--| Proof idea: `hangsPrinted` takes the triple to the printed trace; `printedJoins` says no text follows a comment on
--| its line (`pairsEnd`); `leavesHangOfTrace` takes the trace's fold to the leaves `printedLexes` says the lexer reads.
theorem hangsOfLays ∀ (kinds: Text → Tok) [doc: Doc] (width: Nat)
    (uniform: Uniform doc)
    (joins: Joins (Follows kinds) doc (Plain None) (after => True))
    (all: Every (Printable kinds) doc.words)
    (lays: HangLays kinds doc 0 (place hang => place = AtStart 0 Carry.none ∧ hang = Opening) (place hang =>
      hang ≠ Broke)) (lexed: Lexed)
    (read: lex (Doc.print doc width) = Ok lexed):
    hangs lexed.leaves = True :=
  let (_, _, pairs) := printedJoins (Follows kinds) (Printable kinds) doc width uniform joins all
  let whole := hangsPrinted width lays
  let leaves :=
    leavesHangOfTrace kinds (printedPieces doc width) (pairsEnd kinds (printedPieces doc width).reverse pairs) whole
  let same := Eq.trans (printedLexes doc width kinds uniform joins all).flipped read
  match lexed, same with | { leaves = found, end }, same => cases then leaves
