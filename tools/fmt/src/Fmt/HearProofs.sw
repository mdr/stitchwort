--| The lexer's reading of the printed events as a fold (`hearAll`), and its agreement with `Laid.lay` over the printed
--| pieces (`laidHears`); split from `StandsProofs`.

namespace Fmt.HearProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (Carry)
import Std.Doc.Proofs (
  Closer,
  Event,
  Gap,
  IsComment,
  Kept,
  ReadsAs,
  Said,
  Stretch,
  Told,
  Tucked,
  closesText,
  commentStarts,
  eventsOf,
  isLayout,
  laidOf,
  lineBlank,
  lineWidth,
  printTold,
  printedJoins,
  printedOf,
  printedPieces,
  startsAs
)
import Std.Doc.Proofs (AtStart, Place, Spot)
import Syntax (
  Comment,
  Comments,
  Decl,
  DefBody,
  DefKind,
  Expr,
  Header,
  InfixKind,
  Leaf,
  Note,
  Tok,
  Token,
  Trivia,
  Word,
  withTrailing,
  withoutReturn
)
import Syntax.LexProofs (Spells)
import Fmt (..)
import Fmt.TreeJoinProofs (
  declJoins,
  declOperators,
  declPrintable,
  declReal,
  OperatorSpells,
  PrefixSpells,
  QuietKind,
  infixWithin,
  lexKind,
  lexKindOfSpells,
  lowerQuiet,
  spellsNotComment,
  operatorSpellsOf,
  prefixSpellsOf,
  spellsOfText1,
  spellsQuiet,
  wordQuiet
)
import Fmt.SettleOutputProofs (..)
import Fmt.SpellProofs (..)
import Fmt.TriviaStatements (..)
import Fmt.ToldWordProofs (..)
import Fmt.ToldDeclProofs (..)
import Syntax.LexProofs (Laid, Piece)
import Fmt.PrintHangProofs (
  CommentsEnd,
  Tracks,
  endsRest,
  freshIsBlank,
  laidOfFold,
  lastComment,
  pairsEnd,
  pieceFoldLay,
  tracks
)
import Fmt.JoinProofs (doc1Passes)
import Fmt.DeclHangProofs (DeclHangs, doc1Hangs, lexKindFixed)
import Fmt.OutputStatements (..)
import Fmt.PrintLexProofs (Follows, Printable, pieceFold, pieceOf)

-- What the lexer reads of a leaf.

--| What `stands` reads of a leaf: its kind, its text and comments, and whether it starts its line.
type View = { kind: Tok, word: Word, starts: Bool }

def Leaf.view (leaf: Leaf): View := { kind = leaf.token.kind, word = leaf.word, starts = leaf.token.lineStart }

--| A comment the lexer keeps, as `Leaf.word` reads it.
def noteOf (comment: Comment): Note := { text = comment.text, blankBefore = comment.blankLines > 0 }

-- The lexer over the printed events.

--| What the lexer has read of the printed events so far: the leaves' views, the newest first; the own-line comments
--| waiting for the next token, the newest first; and whether a blank line came since the last comment or token.
type Hearing = { views: List View, above: List Note, blank: Bool }

def Hearing.start: Hearing := { views = [], above = [], blank = False }

--| The newest view with a comment after it.
def trailView (views: List View) (text: Text): List View := match views with
  | [] => []
  | [view, ..older] =>
    [{ view | word = { view.word | comments = { view.word.comments | after = Some text } } }, ..older]

--| One event as the lexer reads it: a blank line; a comment on a line of its own, waiting for the next token; a comment
--| after words, the newest token's; or a token.
def Hearing.hear (heard: Hearing) (kinds: Text → Tok) (event: Event): Hearing :=
  if event.word == "\n" then { heard | blank = True }
  else if event.word.startsWith "--" then
    match event.start with
      | Some _ => { heard |
        above = [{ text = withoutReturn event.word, blankBefore = heard.blank }, ..heard.above],
        blank = False
      }
      | None => { heard | views = trailView heard.views (withoutReturn event.word) }
  else
    {
      views = [
        {
          kind = kinds event.word,
          word = {
            text = event.word,
            comments = { above = heard.above.reverse, after = None, blankBefore = heard.blank }
          },
          starts = event.start.isSome
        },
        ..heard.views
      ],
      above = [],
      blank = False
    }

def hearOn (kinds: Text → Tok) (heard: Hearing) (event: Event): Hearing := heard.hear kinds event

def hearAll (kinds: Text → Tok) (events: List Event): Hearing := events.foldLeft Hearing.start (hearOn kinds)

theorem hearSnoc ∀ (kinds: Text → Tok) (events: List Event) (event: Event):
    hearAll kinds (events ++ [event]) = (hearAll kinds events).hear kinds event :=
  List.foldLeftAppend events Hearing.start [event] (hearOn kinds)

-- `Laid.lay` against the events.

--| The layout after some texts (the last first) and the lexer's reading of their events agree: the leaves, the
--| waiting comments and the blank line; and the layout's blank line is the texts'.
def Hears (kinds: Text → Tok) (laid: Laid) (texts: List Text): Prop :=
  laid.leaves.map Leaf.view = (hearAll kinds (eventsOf texts)).views
    ∧ laid.pending.map noteOf = (hearAll kinds (eventsOf texts)).above
    ∧ (laid.blankRun > 0) = (hearAll kinds (eventsOf texts)).blank
    ∧ laid.lineBlank = lineBlank texts
    ∧ (laid.freshLine = False → laid.lineBlank = False)

--| A comment after the newest leaf is its view's.
theorem trailingViews ∀ (leaves: List Leaf) (comment: Comment):
    (withTrailing leaves comment).map Leaf.view = trailView (leaves.map Leaf.view) comment.text :=
  match leaves with | [] | [_, .._] => byComputing

theorem startIsSome ∀ (texts: List Text):
    (if lineBlank texts then Some (lineWidth texts) else None).isSome = lineBlank texts :=
  match lineBlank texts with | True | False => byComputing

--| Spaces change nothing the lexer reads.
theorem hearsSpaces ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = True)
    (before: Hears kinds (Fmt.PrintHangProofs.laidOf kinds earlier) earlier):
    Hears kinds (Fmt.PrintHangProofs.laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let notBreak: (text == "\n") = False := Doc.Proofs.gapNoBreak text spaces
  let events: eventsOf [text, ..earlier] = eventsOf earlier := rewrite spaces, notBreak
  let blank: lineBlank [text, ..earlier] = lineBlank earlier := rewrite spaces
  let wider: Fmt.PrintHangProofs.laidOf kinds [text, ..earlier]
    = { Fmt.PrintHangProofs.laidOf kinds earlier |
      column = (Fmt.PrintHangProofs.laidOf kinds earlier).column + text.length
    } :=
    rewrite spaces
  rewrite events, blank, wider then before

--| A line break: a blank line if the line had nothing on it.
theorem hearsBreak ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = True)
    (before: Hears kinds (Fmt.PrintHangProofs.laidOf kinds earlier) earlier):
    Hears kinds (Fmt.PrintHangProofs.laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (views, above, blankRun, lineSame, _) := before
  let laid := Fmt.PrintHangProofs.laidOf kinds earlier
  let fresh: Fmt.PrintHangProofs.laidOf kinds [text, ..earlier] = laid.lay Break := rewrite spaces, broken
  let blank: lineBlank [text, ..earlier] = True := rewrite spaces, broken
  let events: eventsOf [text, ..earlier]
    = (if lineBlank earlier then eventsOf earlier ++ [Event.blankLine] else eventsOf earlier) :=
    rewrite spaces, broken
  rewrite fresh, blank, events then
    match wasBlank: lineBlank earlier with
      | True =>
        let laidBlank: laid.lineBlank = True := Eq.trans lineSame wasBlank
        rewrite hearSnoc kinds (eventsOf earlier) Event.blankLine, laidBlank then
          (views, above, byComputing, byComputing, never => (Bool.trueNotFalse never).impossible)
      | False =>
        let laidBlank: laid.lineBlank = False := Eq.trans lineSame wasBlank
        rewrite laidBlank then (views, above, blankRun, byComputing, never => (Bool.trueNotFalse never).impossible)

--| A comment: waiting for the next token on a line of its own, or the newest token's after words.
theorem hearsRemark ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = False)
    (comment: text.startsWith "--" = True)
    (ends: CommentsEnd [text, ..earlier])
    (before: Hears kinds (Fmt.PrintHangProofs.laidOf kinds earlier) earlier):
    Hears kinds (Fmt.PrintHangProofs.laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (views, above, blankRun, lineSame, staleBlank) := before
  let (blankBefore, freshBefore, _) := tracks kinds earlier (endsRest text earlier ends)
  let laid := Fmt.PrintHangProofs.laidOf kinds earlier
  let event: Event := { word = text, start = if lineBlank earlier then Some (lineWidth earlier) else None }
  let noted: Fmt.PrintHangProofs.laidOf kinds [text, ..earlier] = laid.lay (Remark text) :=
    rewrite spaces, broken, comment
  let events: eventsOf [text, ..earlier] = eventsOf earlier ++ [event] := rewrite spaces, broken
  let blank: lineBlank [text, ..earlier] = False := rewrite spaces, broken
  let sameLine: laid.freshLine = lineBlank earlier :=
    freshIsBlank kinds text earlier ends broken blankBefore freshBefore
  rewrite noted, events, hearSnoc kinds (eventsOf earlier) event, blank then
    match wasBlank: lineBlank earlier with
      | True =>
        let fresh: laid.freshLine = True := Eq.trans sameLine wasBlank
        rewrite fresh, broken, comment then
          (views, (rewrite above, blankRun), byComputing, byComputing, never => (Bool.trueNotFalse never).impossible)
      | False =>
        let stale: laid.freshLine = False := Eq.trans sameLine wasBlank
        rewrite stale, broken, comment then
          (
            (rewrite trailingViews laid.leaves { text = withoutReturn text, column = laid.column, blankLines = 0 },
                views),
            above,
            blankRun,
            staleBlank stale,
            _ => staleBlank stale
          )

--| A token: a leaf with the waiting comments above it, starting its line where its event does.
theorem hearsCode ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = False)
    (comment: text.startsWith "--" = False)
    (ends: CommentsEnd [text, ..earlier])
    (before: Hears kinds (Fmt.PrintHangProofs.laidOf kinds earlier) earlier):
    Hears kinds (Fmt.PrintHangProofs.laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (views, above, blankRun, lineSame, _) := before
  let (blankBefore, freshBefore, _) := tracks kinds earlier (endsRest text earlier ends)
  let laid := Fmt.PrintHangProofs.laidOf kinds earlier
  let event: Event := { word = text, start = if lineBlank earlier then Some (lineWidth earlier) else None }
  let token: Fmt.PrintHangProofs.laidOf kinds [text, ..earlier] = laid.lay (Code (kinds text) text) :=
    rewrite spaces, broken, comment
  let events: eventsOf [text, ..earlier] = eventsOf earlier ++ [event] := rewrite spaces, broken
  let blank: lineBlank [text, ..earlier] = False := rewrite spaces, broken
  let sameLine: laid.freshLine = lineBlank earlier :=
    freshIsBlank kinds text earlier ends broken blankBefore freshBefore
  rewrite token, events, hearSnoc kinds (eventsOf earlier) event, blank, broken, comment then
    (
      (rewrite views, List.mapReverse laid.pending noteOf, above, blankRun, sameLine, startIsSome earlier),
      byComputing,
      byComputing,
      byComputing,
      _ => byComputing
    )

--| Over the output's texts (the last first), where no text follows a comment on its line, the lexer's layout reads
--| what the fold over the events does.
--|
--| Proof idea: by induction on the texts, as `tracks`: spaces, a line break, a comment and a token each keep the
--| agreement (`hearsSpaces`, `hearsBreak`, `hearsRemark`, `hearsCode`), with `tracks`' facts for where a line starts.
theorem laidHears ∀ (kinds: Text → Tok) (texts: List Text)
    (ends: CommentsEnd texts):
    Hears kinds (Fmt.PrintHangProofs.laidOf kinds texts) texts :=
  match texts, ends with
    | [], _ => (byComputing, byComputing, byComputing, byComputing, never => (Bool.trueNotFalse never).impossible)
    | [text, ..earlier], ends =>
      let goal: Prop := Hears kinds (Fmt.PrintHangProofs.laidOf kinds [text, ..earlier]) [text, ..earlier]
      let before := laidHears kinds earlier (endsRest text earlier ends)
      Bool.inspect
        (text.all (char => char == ' '))
        (_ => goal)
        (spaces => hearsSpaces kinds text earlier spaces before)
        (spaces =>
          Bool.inspect
            (text == "\n")
            (_ => goal)
            (broken => hearsBreak kinds text earlier spaces broken before)
            (broken =>
              Bool.inspect
                (text.startsWith "--")
                (_ => goal)
                (comment => hearsRemark kinds text earlier spaces broken comment ends before)
                (comment => hearsCode kinds text earlier spaces broken comment ends before)))
