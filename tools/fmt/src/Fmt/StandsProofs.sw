--| `printedStands1`, the engine end (SW-4051, F4 of SW-4042's trivia plan; docs/reviews/SW-4042-trivia-statement.md).
--| The lexer reads the printed events as a fold (`hearAll`), as `Laid.lay` reads the printed pieces (`laidHears`).

namespace Fmt.StandsProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (Event, Gap, Said, Told, eventsOf, isLayout, lineBlank, lineWidth)
import Syntax (Comment, Comments, Leaf, Note, Tok, Token, Trivia, Word, withTrailing, withoutReturn)
import Fmt (isCloserText)
import Fmt.TriviaStatements (..)
import Fmt.ToldDeclProofs (..)
import Syntax.Proofs (Laid, Piece)
import Fmt.PrintHangProofs (CommentsEnd, Tracks, endsRest, freshIsBlank, laidOf, lastComment, tracks)
import Fmt.PrintLexProofs (pieceOf)

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

def hearAll (kinds: Text → Tok) (events: List Event): Hearing :=
  events.foldLeft Hearing.start (heard event => heard.hear kinds event)

theorem hearSnoc ∀ (kinds: Text → Tok) (events: List Event) (event: Event):
    hearAll kinds (events ++ [event]) = (hearAll kinds events).hear kinds event :=
  List.foldLeftAppend events Hearing.start [event] (heard event => heard.hear kinds event)

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
  match leaves with
    | [] => byComputing
    | [last, ..earlier] => byComputing

theorem startIsSome ∀ (texts: List Text):
    (if lineBlank texts then Some (lineWidth texts) else None).isSome = lineBlank texts :=
  match lineBlank texts with
    | True => byComputing
    | False => byComputing

--| Spaces change nothing the lexer reads.
theorem hearsSpaces ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = True)
    (before: Hears kinds (laidOf kinds earlier) earlier):
    Hears kinds (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let notBreak: (text == "\n") = False := Fmt.PrintHangProofs.spacesNotBreak text spaces
  let events: eventsOf [text, ..earlier] = eventsOf earlier := rewrite spaces, notBreak
  let blank: lineBlank [text, ..earlier] = lineBlank earlier := rewrite spaces
  let wider: laidOf kinds [text, ..earlier]
    = { laidOf kinds earlier | column = (laidOf kinds earlier).column + text.length } :=
    rewrite spaces
  rewrite events, blank, wider then before

--| A line break: a blank line if the line had nothing on it.
theorem hearsBreak ∀ (kinds: Text → Tok) (text: Text) (earlier: List Text)
    (spaces: text.all (char => char == ' ') = False)
    (broken: (text == "\n") = True)
    (before: Hears kinds (laidOf kinds earlier) earlier):
    Hears kinds (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (views, above, blankRun, lineSame, _) := before
  let laid := laidOf kinds earlier
  let fresh: laidOf kinds [text, ..earlier] = laid.lay Break := rewrite spaces, broken
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
    (before: Hears kinds (laidOf kinds earlier) earlier):
    Hears kinds (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (views, above, blankRun, lineSame, staleBlank) := before
  let (blankBefore, freshBefore, _) := tracks kinds earlier (endsRest text earlier ends)
  let laid := laidOf kinds earlier
  let event: Event := { word = text, start = if lineBlank earlier then Some (lineWidth earlier) else None }
  let noted: laidOf kinds [text, ..earlier] = laid.lay (Remark text) := rewrite spaces, broken, comment
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
    (before: Hears kinds (laidOf kinds earlier) earlier):
    Hears kinds (laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let (views, above, blankRun, lineSame, _) := before
  let (blankBefore, freshBefore, _) := tracks kinds earlier (endsRest text earlier ends)
  let laid := laidOf kinds earlier
  let event: Event := { word = text, start = if lineBlank earlier then Some (lineWidth earlier) else None }
  let token: laidOf kinds [text, ..earlier] = laid.lay (Code (kinds text) text) := rewrite spaces, broken, comment
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
    Hears kinds (laidOf kinds texts) texts :=
  match texts, ends with
    | [], _ => (byComputing, byComputing, byComputing, byComputing, never => (Bool.trueNotFalse never).impossible)
    | [text, ..earlier], ends =>
      let goal: Prop := Hears kinds (laidOf kinds [text, ..earlier]) [text, ..earlier]
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

-- The tree's words, with the bare commas the rules write between a bracket's items.

type Bit = | AWord (word: Word) | AComma

def bitsWords: List Bit → List Word
  | [] => []
  | [AWord word, ..rest] => [word, ..bitsWords rest]
  | [AComma, ..rest] => bitsWords rest

def Bit.shape: Bit → List Told
  | AWord word => word.shapeW
  | AComma => [Said "," True True]

def bitsShape: List Bit → List Told
  | [] => []
  | [bit, ..rest] => bit.shape ++ bitsShape rest

-- What the lexer reads, as `stands` takes it.

--| The views are the lexer's reading of `bits`, where `owed` is the comment of a word already passed that the lexer has
--| not met: each comma a comma with no comments above it; each word its text and own-line comments, of a kind no comma,
--| and a closer exactly if the word is; a trailing comment on its word's view or owed past the commas and closers after
--| it, none of which starts a line, to the first that holds it; a closer that holds a comment starting its line.
def Heard (owed: Option Text): List Bit → List View → Prop
  | [], [] => owed = None
  | [AComma, ..rest], [view, ..more] =>
    view.kind = Comma
      ∧ view.word.comments.above = []
      ∧ view.word.comments.blankBefore = False
      ∧ (match owed with
        | None => view.word.comments.after = None ∧ Heard None rest more
        | Some text =>
          view.starts = False
            ∧ ((view.word.comments.after = Some text ∧ Heard None rest more)
              ∨ (view.word.comments.after = None ∧ Heard (Some text) rest more)))
  | [AWord word, ..rest], [view, ..more] =>
    view.word.text = word.text
      ∧ view.word.comments.above = word.comments.above
      ∧ view.word.comments.blankBefore = word.comments.blankBefore
      ∧ (view.kind == Comma) = False
      ∧ view.kind.isCloser = isCloserText word.text
      ∧ (match owed, word.comments.after with
        | Some _, Some _ => False
        | Some text, None =>
          isCloserText word.text = True
            ∧ view.starts = False
            ∧ ((view.word.comments.after = Some text ∧ Heard None rest more)
              ∨ (view.word.comments.after = None ∧ Heard (Some text) rest more))
        | None, None => view.word.comments.after = None ∧ Heard None rest more
        | None, Some text =>
          (isCloserText word.text = True → view.starts = True)
            ∧ ((view.word.comments.after = Some text ∧ Heard None rest more)
              ∨ (view.word.comments.after = None ∧ Heard (Some text) rest more)))
  | _, _ => False

theorem noLeading ∀ (leaf: Leaf) (none: leaf.word.comments.above = []): leaf.trivia.leading.isEmpty = True :=
  match leaf with
    | { token, trivia = { leading, blankLines, trailing } } =>
      match leading, none with
        | [], _ => byComputing
        | [comment, ..more], never => cases

theorem noBlank ∀ (leaf: Leaf) (none: leaf.word.comments.blankBefore = False): (leaf.trivia.blankLines == 0) = True :=
  match leaf with
    | { token, trivia = { leading, blankLines, trailing } } =>
      match blankLines, none with
        | Zero, _ => byComputing
        | Succ less, never => (Bool.trueNotFalse never).impossible

theorem noTrail ∀ (leaf: Leaf) (none: leaf.word.comments.after = None): leaf.trivia.trailing = None := match leaf with
  | { token, trivia = { leading, blankLines, trailing } } =>
    match trailing, none with
      | None, _ => byComputing
      | Some comment, never => cases

theorem someTrail ∀ (leaf: Leaf) (text: Text)
    (some: leaf.word.comments.after = Some text):
    ∃ (comment: Comment) => leaf.trivia.trailing = Some comment ∧ comment.text = text :=
  match leaf with
    | { token, trivia = { leading, blankLines, trailing } } =>
      match trailing, some with
        | Some comment, some => (comment, byComputing, Option.someInjective some)
        | None, never => cases

theorem tuckedNone ∀ (leaf: Leaf) (none: leaf.word.comments.after = None): tucked None leaf = Some None :=
  rewrite noTrail leaf none

theorem tuckedPass ∀ (leaf: Leaf) (text: Text)
    (stays: leaf.token.lineStart = False)
    (none: leaf.word.comments.after = None):
    tucked (Some text) leaf = Some (Some text) :=
  rewrite noTrail leaf none, stays

theorem tuckedHolds ∀ (leaf: Leaf) (text: Text)
    (stays: leaf.token.lineStart = False)
    (holds: leaf.word.comments.after = Some text):
    tucked (Some text) leaf = Some None :=
  match someTrail leaf text holds with | (comment, trailing, same) => rewrite trailing, stays, same, DecEq.refl text

theorem headedOf ∀ (leaf: Leaf) (word: Word)
    (text: leaf.view.word.text = word.text)
    (above: leaf.view.word.comments.above = word.comments.above)
    (blank: leaf.view.word.comments.blankBefore = word.comments.blankBefore):
    leaf.headedAs word = True :=
  rewrite text, above, blank, DecEq.refl word.text, DecEq.refl word.comments.above, DecEq.refl word.comments.blankBefore

--| Leaves the lexer reads as `Heard` says stand against the words.
--|
--| Proof idea: by induction on the bits, one leaf each, reading `stands`' branch from the view: a comma's, a word's
--| with its trailing comment held, owed or passed on (`tuckedNone`, `tuckedPass`, `tuckedHolds`).
theorem heardStands ∀ (owed: Option Text) (bits: List Bit) (leaves: List Leaf)
    (heard: Heard owed bits (leaves.map Leaf.view)):
    stands owed (bitsWords bits) leaves = True :=
  match owed, bits, leaves, heard with
    | owed, [], [], none => rewrite none
    | owed, [AComma, ..rest], [leaf, ..more], (comma, above, blank, tail) =>
      let isComma: (leaf.kind == Comma) = True := rewrite comma
      rewrite isComma, noLeading leaf above, noBlank leaf blank then
        match owed, tail with
          | None, (after, heardRest) => rewrite tuckedNone leaf after then heardStands None rest more heardRest
          | Some text, (stays, Inl (holds, heardRest)) =>
            rewrite tuckedHolds leaf text stays holds then heardStands None rest more heardRest
          | Some text, (stays, Inr (none, heardRest)) =>
            rewrite tuckedPass leaf text stays none then heardStands (Some text) rest more heardRest
    | owed, [AWord word, ..rest], [leaf, ..more], (text, above, blank, notComma, closer, tail) =>
      let notCommaLeaf: (leaf.kind == Comma) = False := notComma
      let closerLeaf: leaf.kind.isCloser = isCloserText word.text := closer
      rewrite notCommaLeaf, headedOf leaf word text above blank then
        match owed, after: word.comments.after, tail with
          | Some _, Some _, never => cases
          | Some owedText, None, (shut, stays, Inl (holds, heardRest)) =>
            rewrite closerLeaf, shut, tuckedHolds leaf owedText stays holds then heardStands None rest more heardRest
          | Some owedText, None, (shut, stays, Inr (none, heardRest)) =>
            rewrite closerLeaf, shut, tuckedPass leaf owedText stays none then
              heardStands (Some owedText) rest more heardRest
          | None, None, (none, heardRest) => rewrite noTrail leaf none then heardStands None rest more heardRest
          | None, Some trail, (startsIf, owing) =>
            let opens: (!leaf.kind.isCloser || leaf.token.lineStart) = True :=
              rewrite closerLeaf then
                match shut: isCloserText word.text with
                  | True => rewrite startsIf shut
                  | False => byComputing
            rewrite opens then
              match owing with
                | Inl (holds, heardRest) =>
                  match someTrail leaf trail holds with
                    | (comment, trailing, same) =>
                      rewrite trailing, same, DecEq.refl trail then heardStands None rest more heardRest
                | Inr (none, heardRest) => rewrite noTrail leaf none then heardStands (Some trail) rest more heardRest
