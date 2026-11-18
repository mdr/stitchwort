--| `printedStands1`, the engine end (SW-4051, F4 of SW-4042's trivia plan; docs/reviews/SW-4042-trivia-statement.md).
--| The lexer reads the printed events as a fold (`hearAll`), as `Laid.lay` reads the printed pieces (`laidHears`).

namespace Fmt.StandsProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)
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
  printedOf,
  startsAs
)
import Syntax (Comment, Comments, Leaf, Note, Tok, Token, Trivia, Word, withTrailing, withoutReturn)
import Fmt (isCloserText)
import Fmt.TriviaStatements (..)
import Fmt.ToldWordProofs (..)
import Fmt.ToldDeclProofs (..)
import Syntax.Proofs (Laid, Piece)
import Fmt.PrintHangProofs (CommentsEnd, Tracks, endsRest, freshIsBlank, lastComment, tracks)
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
    (before: Hears kinds (Fmt.PrintHangProofs.laidOf kinds earlier) earlier):
    Hears kinds (Fmt.PrintHangProofs.laidOf kinds [text, ..earlier]) [text, ..earlier] :=
  let notBreak: (text == "\n") = False := Fmt.PrintHangProofs.spacesNotBreak text spaces
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

-- The tuck: the printed events of a reading of the bits, as the lexer hears them.

--| A comment as the rules print it and the lexer reads it back: `--` first, no carriage return to take off.
def CommentFine (text: Text): Prop := text.startsWith "--" = True ∧ withoutReturn text = text

def NotesFine: List Note → Prop
  | [] => Unit
  | [note, ..rest] => CommentFine note.text ∧ NotesFine rest

def AfterFine: Option Text → Prop
  | None => Unit
  | Some text => CommentFine text

--| A word the lexer reads back as itself: a token of a kind that is a comma or closer exactly when its text is, and its
--| comments.
def WordFine (kinds: Text → Tok) (word: Word): Prop :=
  (kinds word.text == Comma) = False
    ∧ (kinds word.text).isCloser = isCloserText word.text
    ∧ word.text.startsWith "--" = False
    ∧ (word.text == "\n") = False
    ∧ (word.text == ",") = False
    ∧ NotesFine word.comments.above
    ∧ AfterFine word.comments.after

def BitsFine (kinds: Text → Tok): List Bit → Prop
  | [] => Unit
  | [AComma, ..rest] => kinds "," = Comma ∧ BitsFine kinds rest
  | [AWord word, ..rest] => WordFine kinds word ∧ BitsFine kinds rest

--| A trailing comment that waits while the closers `pending` are printed on its line, or none.
def Waiting: Option Event → List Event → Prop
  | None, pending => pending = []
  | Some comment, pending => pending ≠ [] ∧ List.All Closer pending ∧ comment.start = None ∧ CommentFine comment.word

--| The events still to print: the waiting comment's closers and then it, then the stretches'.
def nowPrinted: Option Event → List Event → List Stretch → List Event
  | None, _, stretches => printedOf stretches
  | Some comment, pending, stretches => pending ++ [comment] ++ printedOf stretches

--| An entry whose event can't start a tucked stretch: a blank line, a word, or a comment that starts its line.
def Unmoved (told: Told): Bool := match told with
  | Told.Gap => True
  | Said text _ follows => !follows || !text.startsWith "--"
  | _ => False

theorem blankNotComment ∀ (event: Event) (blank: event = Event.blankLine) (comment: IsComment event.word): Void :=
  Bool.falseNotTrue (rewrite blank at comment then commentStarts "\n" comment)

theorem codeNotComment ∀ (text: Text) (code: text.startsWith "--" = False) (comment: IsComment text): Void :=
  let starts := commentStarts text comment
  Bool.falseNotTrue (rewrite code at starts then starts)

--| Entries no tucked stretch can start are each kept as they stand.
--|
--| Proof idea: by induction on the entries; a tucked stretch starts with a comment that starts no line, which a blank
--| line, a word or an own-line comment's event is not.
theorem keptFront ∀ (told more: List Told) (stretches: List Stretch)
    (unmoved: told.all Unmoved = True)
    (fits: List.All Stretch.Fits stretches)
    (reads: ReadsAs (told ++ more) (laidOf stretches)):
    ∃ (front: List Event) => ∃ (rest: List Stretch) => printedOf stretches = front ++ printedOf rest
      ∧ ReadsAs told front
      ∧ ReadsAs more (laidOf rest)
      ∧ List.All Stretch.Fits rest :=
  match told, unmoved with
    | [], _ => ([], stretches, byComputing, byComputing, reads, fits)
    | [entry, ..others], unmoved =>
      let othersUnmoved: others.all Unmoved = True := Bool.andRight unmoved
      match stretches, fits, entry, unmoved, reads with
        | [], _, Told.Gap, _, never => cases
        | [], _, Said _ _ _, _, never => cases
        | [Kept event, ..later], (_, fitsLater), Told.Gap, _, (blank, readsLater) =>
          match keptFront others more later othersUnmoved fitsLater readsLater with
            | (front, rest, printed, readsFront, readsMore, fitsRest) =>
              ([event, ..front], rest, (rewrite printed), (blank, readsFront), readsMore, fitsRest)
        | [Kept event, ..later], (_, fitsLater), Said text starts follows, _, (word, start, readsLater) =>
          match keptFront others more later othersUnmoved fitsLater readsLater with
            | (front, rest, printed, readsFront, readsMore, fitsRest) =>
              ([event, ..front], rest, (rewrite printed), (word, start, readsFront), readsMore, fitsRest)
        | [Tucked comment closers, ..later], ((_, isComment, _), _), Told.Gap, _, (blank, _) =>
          (blankNotComment comment blank isComment).impossible
        | [Tucked comment closers, ..later], ((unstarted, isComment, _), _), Said text starts follows, moves, (word,
            start, _) =>
          let follows: follows = True := rewrite unstarted at start then start
          let code: text.startsWith "--" = False := rewrite follows at moves then Bool.notTrue _ (Bool.andLeft moves)
          (codeNotComment text code (rewrite word at isComment then isComment)).impossible

--| The view of a token heard with `above` waiting and `blank` before it.
def tokenView (kinds: Text → Tok) (text: Text) (above: List Note) (blank: Bool) (event: Event): View := {
  kind = kinds text,
  word = { text, comments = { above, after = None, blankBefore = blank } },
  starts = event.start.isSome
}

theorem commentNotBreak ∀ (text: Text) (comment: text.startsWith "--" = True): (text == "\n") = False :=
  match same: text == "\n" with
    | False => byComputing
    | True => (Bool.falseNotTrue (rewrite DecEq.sound same at comment then comment)).impossible

--| A word's own-line comments, its blank line and its token, heard where no blank line waits: the token's view, with
--| the comments above it.
--|
--| Proof idea: by induction on the comments: a blank line sets the flag, an own-line comment (its event starts a line)
--| waits with it, and the token takes them.
theorem hearHead ∀ (kinds: Text → Tok) (notes: List Note) (blankW: Bool) (text: Text) (flag: Bool)
    (events: List Event) (heard: Hearing)
    (fine: NotesFine notes)
    (code: text.startsWith "--" = False)
    (unbroken: (text == "\n") = False)
    (blank: heard.blank = False)
    (reads: ReadsAs (notesTold notes ++ ((if blankW then [Told.Gap] else []) ++ [Said text True flag])) events):
    ∃ (event: Event) => event.word = text
      ∧ startsAs True flag event.start
      ∧ events.foldLeft heard (hearOn kinds)
        = {
          views = [tokenView kinds text (heard.above.reverse ++ notes) blankW event, ..heard.views],
          above = [],
          blank = False
        } :=
  match notes, fine with
    | [], _ =>
      match blankW, events, reads with
        | True, [gapEvent, event, ..rest], (isBlank, (word, start, done)) =>
          rewrite isBlank, done then
            (event, word, start, rewrite word, unbroken, code, List.appendNil heard.above.reverse)
        | False, [event, ..rest], (word, start, done) =>
          rewrite done, blank then
            (event, word, start, rewrite word, unbroken, code, List.appendNil heard.above.reverse)
        | True, [], never => cases
        | True, [gapEvent], (_, never) => cases
        | False, [], never => cases
    | [{ text = noteText, blankBefore = noteBlank }, ..others], ((starts, plain), fineOthers) =>
      let unbrokenNote := commentNotBreak noteText starts
      match noteBlank, events, reads with
        | True, [gapEvent, noteEvent, ..rest], (isBlank, (word, start, readsRest)) =>
          match started: noteEvent.start, start with
            | Some at, _ =>
              let after: Hearing :=
                { views = heard.views, above = [{ text = noteText, blankBefore = True }, ..heard.above], blank = False }
              match hearHead kinds others blankW text flag rest after fineOthers code unbroken byComputing
                  readsRest with
                | (event, eventWord, eventStart, folds) =>
                  rewrite isBlank, word, unbrokenNote, starts, plain then
                    (
                      event,
                      eventWord,
                      eventStart,
                      rewrite folds,
                          List.reverseCons { text = noteText, blankBefore = True } heard.above,
                          List.appendAssoc heard.above.reverse [{ text = noteText, blankBefore = True }] others
                    )
            | None, never => cases
        | False, [noteEvent, ..rest], (word, start, readsRest) =>
          match started: noteEvent.start, start with
            | Some at, _ =>
              let after: Hearing := {
                views = heard.views,
                above = [{ text = noteText, blankBefore = False }, ..heard.above],
                blank = False
              }
              match hearHead kinds others blankW text flag rest after fineOthers code unbroken byComputing
                  readsRest with
                | (event, eventWord, eventStart, folds) =>
                  rewrite word, unbrokenNote, starts, plain, blank then
                    (
                      event,
                      eventWord,
                      eventStart,
                      rewrite folds,
                          List.reverseCons { text = noteText, blankBefore = False } heard.above,
                          List.appendAssoc heard.above.reverse [{ text = noteText, blankBefore = False }] others
                    )
            | None, never => cases
        | True, [], never => cases
        | True, [gapEvent], (_, never) => cases
        | False, [], never => cases
