--| `printedStands1`, the engine end (SW-4051, F4 of SW-4042's trivia plan; docs/reviews/SW-4042-trivia-statement.md).
--| The lexer reads the printed events as a fold (`hearAll`, in `Fmt.HearProofs`, with `laidHears`).

namespace Fmt.StandsProofs
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
  infixListed,
  nameKinded,
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
import Fmt.HearProofs (..)
import Fmt.SpellProofs (..)
import Fmt.TriviaStatements (..)
import Fmt.ToldWordProofs (..)
import Fmt.ToldDeclProofs (..)
import Syntax.LexProofs (Laid)
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
  | [] => True
  | [note, ..rest] => CommentFine note.text ∧ NotesFine rest

def AfterFine: Option Text → Prop
  | None => True
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
  | [] => True
  | [AComma, ..rest] => kinds "," = Comma ∧ BitsFine kinds rest
  | [AWord word, ..rest] => WordFine kinds word ∧ BitsFine kinds rest

--| A trailing comment that waits while the closers `pending` are printed on its line, or none.
def Waiting: Option Event → List Event → Prop
  | None, pending => pending = []
  | Some comment, pending => pending ≠ [] ∧ List.All Closer pending ∧ comment.start = None ∧ CommentFine comment.word

--| The events still to print: the waiting comment's closers and then it, then the stretches'.
def nowPrinted: Option Event → List Event → List Stretch → List Event
  | None, _, stretches => printedOf stretches
  | Some comment, pending, stretches => (pending ++ [comment]) ++ printedOf stretches

--| An entry whose event can't start a tucked stretch: a blank line, a word, or a comment that starts its line.
def Unmoved (told: Told): Bool := match told with
  | Gap => True
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
        | [], _, Gap | Said _ _ _, _, never => cases
        | [Kept event, ..later], (_, fitsLater), Gap, _, (blank, readsLater) =>
          match keptFront others more later othersUnmoved fitsLater readsLater with
            | (front, rest, printed, readsFront, readsMore, fitsRest) =>
              ([event, ..front], rest, (rewrite printed), (blank, readsFront), readsMore, fitsRest)
        | [Kept event, ..later], (_, fitsLater), Said text starts follows, _, (word, start, readsLater) =>
          match keptFront others more later othersUnmoved fitsLater readsLater with
            | (front, rest, printed, readsFront, readsMore, fitsRest) =>
              ([event, ..front], rest, (rewrite printed), (word, start, readsFront), readsMore, fitsRest)
        | [Tucked comment closers, ..later], ((_, isComment, _), _), Gap, _, (blank, _) =>
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
    (reads: ReadsAs (notesTold notes ++ ((if blankW then [Gap] else []) ++ [Said text True flag])) events):
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

theorem closesCloser ∀ (text: Text)
    (closes: closesText text = True)
    (notComma: (text == ",") = False):
    isCloserText text = True :=
  match paren: text == ")" with
    | True => byComputing
    | False =>
      match square: text == "]" with
        | True => byComputing
        | False => (Bool.falseNotTrue (rewrite notComma at closes then closes)).impossible

--| A word's own-line comments, blank line and token can't start a tucked stretch.
theorem headUnmoved ∀ (notes: List Note) (blank: Bool) (text: Text) (flag: Bool)
    (code: text.startsWith "--" = False):
    (notesTold notes ++ ((if blank then [Gap] else []) ++ [Said text True flag])).all Unmoved = True :=
  match notes with
    | [] =>
      match blank, flag with
        | True, True => rewrite code
        | True, False => byComputing
        | False, True => rewrite code
        | False, False => byComputing
    | [{ text = noteText, blankBefore = noteBlank }, ..others] =>
      match noteBlank with
        | True | False => headUnmoved others blank text flag code

--| A word's reading, split after its token.
theorem shapeSplit ∀ (text: Text) (notes: List Note) (after: Option Text) (blank: Bool) (more: List Told):
    { text, comments = { above = notes, after, blankBefore = blank } }.shapeW ++ more
      = (notesTold notes
        ++ ((if blank then [Gap] else [])
          ++ [Said text True (!closerTrails { text, comments = { above = notes, after, blankBefore = blank } })]))
        ++ ({ text, comments = { above = notes, after, blankBefore = blank } }.toldTrail ++ more) :=
  match blank with
    | True =>
      rewrite List.appendAssoc
            (notesTold notes ++ [Gap])
            ([Said text True (!closerTrails { text, comments = { above = notes, after, blankBefore = True } })]
              ++ { text, comments = { above = notes, after, blankBefore = True } }.toldTrail)
            more,
          List.appendAssoc
            (notesTold notes)
            [Gap]
            ([Said text True (!closerTrails { text, comments = { above = notes, after, blankBefore = True } })]
              ++ ({ text, comments = { above = notes, after, blankBefore = True } }.toldTrail ++ more)),
          List.appendAssoc
            (notesTold notes)
            [Gap, Said text True (!closerTrails { text, comments = { above = notes, after, blankBefore = True } })]
            ({ text, comments = { above = notes, after, blankBefore = True } }.toldTrail ++ more)
    | False =>
      rewrite List.appendAssoc
            (notesTold notes ++ [])
            ([Said text True (!closerTrails { text, comments = { above = notes, after, blankBefore = False } })]
              ++ { text, comments = { above = notes, after, blankBefore = False } }.toldTrail)
            more,
          List.appendNil (notesTold notes),
          List.appendAssoc
            (notesTold notes)
            [Said text True (!closerTrails { text, comments = { above = notes, after, blankBefore = False } })]
            ({ text, comments = { above = notes, after, blankBefore = False } }.toldTrail ++ more)

--| The view with `after` for its trailing comment.
def View.withAfter (view: View) (after: Option Text): View :=
  { view | word = { view.word | comments = { view.word.comments | after } } }

--| What `bitsHeard` says of `bits`: from wherever the lexer is between tokens, the printed events of a reading of the
--| bits (a comment owed with closers to print before it, or none) add views that `Heard` reads as the bits.
def HeardFrom (kinds: Text → Tok) (bits: List Bit): Prop :=
  ∀ (owe: Option Event) (pending: List Event) (stretches: List Stretch) (heard: Hearing) => BitsFine kinds bits
    → List.All Stretch.Fits stretches
    → Waiting owe pending
    → ReadsAs (bitsShape bits) (pending ++ laidOf stretches)
    → heard.above = []
    → heard.blank = False
    → ∃ (views: List View) => ((nowPrinted owe pending stretches).foldLeft heard (hearOn kinds)).views
      = views ++ heard.views
      ∧ Heard (owe.map (comment => comment.word)) bits views.reverse

--| A comma or closer printed while `comment` waits: its view, holding the comment if it is the last before it.
theorem tuckedStep ∀ (kinds: Text → Tok) (rest: List Bit) (comment closer: Event) (closers: List Event)
    (stretches: List Stretch) (heard: Hearing)
    (next: HeardFrom kinds rest)
    (fineRest: BitsFine kinds rest)
    (fits: List.All Stretch.Fits stretches)
    (closersAll: List.All Closer closers)
    (unstarted: comment.start = None)
    (fineComment: CommentFine comment.word)
    (code: closer.word.startsWith "--" = False)
    (unbroken: (closer.word == "\n") = False)
    (reads: ReadsAs (bitsShape rest) (closers ++ laidOf stretches))
    (above: heard.above = [])
    (blank: heard.blank = False):
    ∃ (more: List View) => ∃ (after: Option Text) => (((([closer, ..closers] ++ [comment])
      ++ printedOf stretches).foldLeft heard
      (hearOn kinds)).views
      = more ++ [(tokenView kinds closer.word [] False closer).withAfter after, ..heard.views])
      ∧ ((after = Some comment.word ∧ Heard None rest more.reverse)
        ∨ (after = None ∧ Heard (Some comment.word) rest more.reverse)) :=
  let (starts, plain) := fineComment
  let first: Hearing :=
    { views = [tokenView kinds closer.word [] False closer, ..heard.views], above = [], blank = False }
  match closers, closersAll with
    | [], _ =>
      let held: Hearing := {
        views = [(tokenView kinds closer.word [] False closer).withAfter (Some comment.word), ..heard.views],
        above = [],
        blank = False
      }
      match next None [] stretches held fineRest fits byComputing reads byComputing byComputing with
        | (more, folds, heardRest) => (
          more,
          Some comment.word,
          (rewrite unbroken, code, above, blank, commentNotBreak comment.word starts, starts, unstarted, plain, folds),
          Inl (byComputing, heardRest)
        )
    | [second, ..others], closersAll =>
      match next
        (Some comment)
        [second, ..others]
        stretches
        first
        fineRest
        fits
        (List.consNotNil second others, closersAll, unstarted, fineComment)
        reads
        byComputing
        byComputing with
        | (more, folds, heardRest) =>
          (more, None, (rewrite unbroken, code, above, blank, folds), Inr (byComputing, heardRest))

--| A word's token that holds a comment, if a closer, starts its line where the reading says.
theorem closerStarts ∀ (text: Text) (event: Event)
    (start: startsAs True (!(isCloserText text && True)) event.start = True)
    (shut: isCloserText text = True):
    event.start.isSome = True :=
  match started: event.start, start with
    | Some at, _ => byComputing
    | None, never => (Bool.falseNotTrue (rewrite shut at never then never)).impossible

--| The tuck: the printed events of a reading of the bits, each trailing comment after the closers and commas tucked in
--| front of it on its line, are heard as `Heard` says.
--|
--| Proof idea: by induction on the bits. A word's own-line comments, blank line and token are kept as they stand
--| (`keptFront`) and heard as the token's view (`hearHead`); its trailing comment is kept, then heard as the view's, or
--| tucked, and then the closers and commas after it are heard as owing it (`tuckedStep`) until the last, which holds
--| it. Each step hears from where the one before left the lexer, so the views add up.
theorem bitsHeard ∀ (kinds: Text → Tok) (bits: List Bit): HeardFrom kinds bits :=
  owe pending stretches heard fine fits waiting reads above blank =>
    match bits, fine with
      | [], _ =>
        match owe, waiting with
          | None, nil =>
            let empty: laidOf stretches = [] := rewrite nil at reads then reads
            match stretches, empty with
              | [], _ => ([], byComputing, byComputing)
              | [Kept event, ..later], never => cases
          | Some comment, (notNil, _) =>
            match pending, reads with
              | [], _ => (notNil byComputing).impossible
              | [first, ..others], never => cases
      | [AComma, ..rest], (commaKind, fineRest) =>
        match owe, waiting with
          | None, nil =>
            let readsLaid: ReadsAs (bitsShape [AComma, ..rest]) (laidOf stretches) := rewrite nil at reads then reads
            match stretches, fits, readsLaid with
              | [Kept event, ..later], (_, fitsLater), (word, _, readsRest) =>
                let view := tokenView kinds "," [] False event
                let after: Hearing := { views = [view, ..heard.views], above = [], blank = False }
                match bitsHeard kinds rest None [] later after fineRest fitsLater byComputing readsRest byComputing
                    byComputing with
                  | (more, folds, heardRest) => (
                    more ++ [view],
                    (rewrite word, above, blank, folds, List.appendAssoc more [view] heard.views),
                    (rewrite List.reverseSnoc more view then
                      (commaKind, byComputing, byComputing, (byComputing, heardRest)))
                  )
              | [Tucked comment closers, ..later], ((_, isComment, _), _), (word, _, _) =>
                (codeNotComment "," byComputing (rewrite word at isComment then isComment)).impossible
          | Some comment, (notNil, closersAll, unstarted, fineComment) =>
            match pending, closersAll, reads with
              | [], _, _ => (notNil byComputing).impossible
              | [closer, ..closers], ((closerStart, _), closersRest), (word, _, readsRest) =>
                match tuckedStep kinds rest comment closer closers stretches heard
                  (bitsHeard kinds rest)
                  fineRest
                  fits
                  closersRest
                  unstarted
                  fineComment
                  (rewrite word)
                  (rewrite word)
                  readsRest
                  above
                  blank with
                  | (more, after, folds, choice) =>
                    let view := (tokenView kinds closer.word [] False closer).withAfter after
                    (
                      more ++ [view],
                      (rewrite folds, List.appendAssoc more [view] heard.views),
                      (rewrite List.reverseSnoc more view, word then
                        (commaKind, byComputing, byComputing, ((rewrite closerStart), choice)))
                    )
      | [AWord { text, comments = { above = notes, after = trail, blankBefore = wordBlank } }, ..rest], (
          (notComma, closerKind, code, unbroken, textNotComma, notesFine, trailFine),
          fineRest
        ) =>
        match owe, waiting with
          | Some comment, (notNil, closersAll, unstarted, fineComment) =>
            match pending, closersAll with
              | [], _ => (notNil byComputing).impossible
              | [closer, ..closers], ((closerStart, closes), closersRest) =>
                match notes, wordBlank, reads with
                  | [{ text = noteText, blankBefore = True }, ..others], _, (isBlank, _) =>
                    (Bool.falseNotTrue (rewrite isBlank at closes then closes)).impossible
                  | [{ text = noteText, blankBefore = False }, ..others], _, (_, start, _) =>
                    (Bool.falseNotTrue (rewrite closerStart at start then start)).impossible
                  | [], True, (isBlank, _) => (Bool.falseNotTrue (rewrite isBlank at closes then closes)).impossible
                  | [], False, (word, start, readsRest) =>
                    let shut: isCloserText text = True :=
                      closesCloser text (rewrite word at closes then closes) textNotComma
                    match trail, readsRest with
                      | Some trailText, _ =>
                        (Bool.falseNotTrue (rewrite closerStart, shut at start then start)).impossible
                      | None, readsRest =>
                        match tuckedStep kinds rest comment closer closers stretches heard
                          (bitsHeard kinds rest)
                          fineRest
                          fits
                          closersRest
                          unstarted
                          fineComment
                          (rewrite word then code)
                          (rewrite word then unbroken)
                          readsRest
                          above
                          blank with
                          | (more, after, folds, choice) =>
                            let view := (tokenView kinds closer.word [] False closer).withAfter after
                            (
                              more ++ [view],
                              (rewrite folds, List.appendAssoc more [view] heard.views),
                              (rewrite List.reverseSnoc more view, word then
                                (
                                  byComputing,
                                  byComputing,
                                  byComputing,
                                  notComma,
                                  closerKind,
                                  (shut, (rewrite closerStart), choice)
                                ))
                            )
          | None, nil =>
            let flag := !closerTrails { text, comments = { above = notes, after = trail, blankBefore = wordBlank } }
            let split: ReadsAs
              ((notesTold notes ++ ((if wordBlank then [Gap] else []) ++ [Said text True flag]))
                ++ ({ text, comments = { above = notes, after = trail, blankBefore = wordBlank } }.toldTrail
                  ++ bitsShape rest))
              (laidOf stretches) :=
              rewrite nil, shapeSplit text notes trail wordBlank (bitsShape rest) at reads then reads
            match keptFront
              (notesTold notes ++ ((if wordBlank then [Gap] else []) ++ [Said text True flag]))
              ({ text, comments = { above = notes, after = trail, blankBefore = wordBlank } }.toldTrail
                ++ bitsShape rest)
              stretches
              (headUnmoved notes wordBlank text flag code)
              fits
              split with
              | (front, later, printed, readsFront, readsMore, fitsLater) =>
                match hearHead kinds notes wordBlank text flag front heard notesFine code unbroken blank readsFront with
                  | (event, word, start, heads) =>
                    let view := tokenView kinds text notes wordBlank event
                    let first: Hearing := { views = [view, ..heard.views], above = [], blank = False }
                    let reached: (printedOf stretches).foldLeft heard (hearOn kinds)
                      = (printedOf later).foldLeft first (hearOn kinds) :=
                      rewrite printed, List.foldLeftAppend front heard (printedOf later) (hearOn kinds), heads, above
                    match trail, trailFine, readsMore with
                      | None, _, readsRest =>
                        match bitsHeard kinds rest None [] later first fineRest fitsLater byComputing readsRest
                            byComputing byComputing with
                          | (more, folds, heardRest) => (
                            more ++ [view],
                            (rewrite reached, folds, List.appendAssoc more [view] heard.views),
                            (rewrite List.reverseSnoc more view then
                              (byComputing, byComputing, byComputing, notComma, closerKind, (byComputing, heardRest)))
                          )
                      | Some trailText, (trailStarts, trailPlain), readsTrail =>
                        let opens: isCloserText text = True → view.starts = True := shut =>
                          closerStarts text event start shut
                        let held := view.withAfter (Some trailText)
                        let second: Hearing := { views = [held, ..heard.views], above = [], blank = False }
                        match later, fitsLater, readsTrail with
                          | [], _, never => cases
                          | [Kept comment, ..after], (_, fitsAfter), (commentWord, commentStart, readsRest) =>
                            match started: comment.start, commentStart with
                              | Some at, never => cases
                              | None, _ =>
                                match bitsHeard kinds rest None [] after second fineRest fitsAfter byComputing readsRest
                                    byComputing byComputing with
                                  | (more, folds, heardRest) => (
                                    more ++ [held],
                                    (rewrite reached,
                                        commentWord,
                                        commentNotBreak trailText trailStarts,
                                        trailStarts,
                                        trailPlain,
                                        folds,
                                        List.appendAssoc more [held] heard.views),
                                    (rewrite List.reverseSnoc more held then
                                      (
                                        byComputing,
                                        byComputing,
                                        byComputing,
                                        notComma,
                                        closerKind,
                                        (opens, Inl (byComputing, heardRest))
                                      ))
                                  )
                          | [Tucked comment closers, ..after], ((unstarted, _, closersAll), fitsAfter), (commentWord, _,
                              readsRest) =>
                            match closers, closersAll with
                              | [], _ =>
                                match bitsHeard kinds rest None [] after second fineRest fitsAfter byComputing readsRest
                                    byComputing byComputing with
                                  | (more, folds, heardRest) => (
                                    more ++ [held],
                                    (rewrite reached,
                                        unstarted,
                                        commentWord,
                                        commentNotBreak trailText trailStarts,
                                        trailStarts,
                                        trailPlain,
                                        folds,
                                        List.appendAssoc more [held] heard.views),
                                    (rewrite List.reverseSnoc more held then
                                      (
                                        byComputing,
                                        byComputing,
                                        byComputing,
                                        notComma,
                                        closerKind,
                                        (opens, Inl (byComputing, heardRest))
                                      ))
                                  )
                              | [closer, ..others], closersAll =>
                                match bitsHeard kinds rest
                                  (Some comment)
                                  [closer, ..others]
                                  after
                                  first
                                  fineRest
                                  fitsAfter
                                  (
                                    List.consNotNil closer others,
                                    closersAll,
                                    unstarted,
                                    (rewrite commentWord then (trailStarts, trailPlain))
                                  )
                                  readsRest
                                  byComputing
                                  byComputing with
                                  | (more, folds, heardRest) => (
                                    more ++ [view],
                                    (rewrite reached, folds, List.appendAssoc more [view] heard.views),
                                    (rewrite List.reverseSnoc more view then
                                      (
                                        byComputing,
                                        byComputing,
                                        byComputing,
                                        notComma,
                                        closerKind,
                                        (opens, Inr (byComputing, rewrite commentWord at heardRest then heardRest))
                                      ))
                                  )

-- The tree's bits.

--| A token as a declaration's reading has it: with no comments above it where its frame wrote them (`hoisted`), else
--| as `calm` keeps it.
def Word.bitK (word: Word) (item hoisted: Bool): Word :=
  if hoisted then { word | comments = { above = [], after = word.comments.after, blankBefore = False } }
  else word.kept item (isCloserText word.text)

--| An expression's tokens and the bare commas between a bracket's items, as `Expr.shape` reads them.
def Expr.bits: Expr → Bool → Bool → List Bit
  | Atom _ word, item, hoisted => [AWord (word.bitK item hoisted)]
  | Paren open inner close, item, hoisted =>
    [AWord (open.bitK item hoisted), ..inner.bits False False] ++ [AWord (close.bitK False False)]
  | Tuple open items _ close, item, hoisted =>
    [AWord (open.bitK item hoisted), ..itemsBits True items] ++ [AWord (close.bitK False False)]
  | ListOf open items _ close, item, hoisted =>
    [AWord (open.bitK item hoisted), ..itemsBits (!items.all Expr.plainItem) items] ++ [AWord (close.bitK False False)]
  | App head arguments, item, hoisted => head.bits item hoisted ++ argumentsBits arguments
  | Infix _ left operator right, item, hoisted =>
    left.bits item hoisted ++ [AWord (operator.bitK False False), ..right.bits False False]
  | Prefix operator operand, item, hoisted => [AWord (operator.bitK item hoisted), ..operand.bits False False]
  | _, _, _ => []

def itemsBits (first: Bool): List Expr → List Bit
  | [] => []
  | [item] => item.bits first False
  | [item, ..rest] => item.bits first False ++ [AComma] ++ itemsBits True rest

def argumentsBits: List Expr → List Bit
  | [] => []
  | [argument, ..rest] => argument.bits False False ++ argumentsBits rest

def Decl.bits: Decl → List Bit
  | Definition _ header (Assigned colonEq value) => [
    AWord ((fixedWord "def" header.keyword).bitK False True),
    AWord (header.name.bitK False False),
    AWord ((fixedWord ":" header.colon).bitK False False),
    ..(header.result.bits False False ++ [AWord ((fixedWord ":=" colonEq).bitK False False), ..value.bits False False])
  ]
  | _ => []

theorem bitsShapeAppend ∀ (front back: List Bit): bitsShape (front ++ back) = bitsShape front ++ bitsShape back :=
  match front with
    | [] => byComputing
    | [bit, ..rest] => rewrite bitsShapeAppend rest back, List.appendAssoc bit.shape (bitsShape rest) (bitsShape back)

theorem bitsWordsAppend ∀ (front back: List Bit): bitsWords (front ++ back) = bitsWords front ++ bitsWords back :=
  match front with
    | [] => byComputing
    | [AWord word, ..rest] => rewrite bitsWordsAppend rest back
    | [AComma, ..rest] => bitsWordsAppend rest back

theorem bitsFineAppend ∀ (kinds: Text → Tok) (front back: List Bit)
    (frontFine: BitsFine kinds front)
    (backFine: BitsFine kinds back):
    BitsFine kinds (front ++ back) :=
  match front, frontFine with
    | [], _ => backFine
    | [AWord _, ..rest] | [AComma, ..rest], (fine, restFine) => (fine, bitsFineAppend kinds rest back restFine backFine)

theorem bitShapeOne ∀ (word: Word): bitsShape [AWord word] = word.shapeW := List.appendNil word.shapeW

--| What an expression tells is its bits' reading.
--|
--| Proof idea: by induction on the expression, as `Expr.shape` and `Expr.bits` are written alike, joining with
--| `bitsShapeAppend`.
theorem shapeBits ∀ (expr: Expr) (item hoisted: Bool): expr.shape item hoisted = bitsShape (expr.bits item hoisted) :=
  match expr with
    | Atom kind word => (bitShapeOne (word.bitK item hoisted)).flipped
    | Paren open inner close =>
      rewrite bitsShapeAppend [AWord (open.bitK item hoisted), ..inner.bits False False] [
            AWord (close.bitK False False)
          ],
          bitShapeOne (close.bitK False False),
          <- shapeBits inner False False,
          List.appendAssoc (open.bitK item hoisted).shapeW (inner.shape False False) (close.bitK False False).shapeW
    | Tuple open items comma close =>
      rewrite bitsShapeAppend [AWord (open.bitK item hoisted), ..itemsBits True items] [AWord (close.bitK False False)],
          bitShapeOne (close.bitK False False),
          <- itemsShapeBits True items,
          List.appendAssoc (open.bitK item hoisted).shapeW (itemsShape True items) (close.bitK False False).shapeW
    | ListOf open items comma close =>
      rewrite bitsShapeAppend [AWord (open.bitK item hoisted), ..itemsBits (!items.all Expr.plainItem) items] [
            AWord (close.bitK False False)
          ],
          bitShapeOne (close.bitK False False),
          <- itemsShapeBits (!items.all Expr.plainItem) items,
          List.appendAssoc
            (open.bitK item hoisted).shapeW
            (itemsShape (!items.all Expr.plainItem) items)
            (close.bitK False False).shapeW
    | App head arguments =>
      rewrite bitsShapeAppend (head.bits item hoisted) (argumentsBits arguments),
          <- shapeBits head item hoisted,
          <- argumentsShapeBits arguments
    | Infix kind left operator right =>
      rewrite bitsShapeAppend (left.bits item hoisted) [AWord (operator.bitK False False), ..right.bits False False],
          <- shapeBits left item hoisted,
          <- shapeBits right False False
    | Prefix operator operand => rewrite <- shapeBits operand False False
    | _ => byComputing

theorem itemsShapeBits ∀ (first: Bool) (items: List Expr): itemsShape first items = bitsShape (itemsBits first items) :=
  match items with
    | [] => byComputing
    | [item] => shapeBits item first False
    | [item, next, ..more] =>
      rewrite bitsShapeAppend (item.bits first False) ([AComma] ++ itemsBits True [next, ..more]),
          <- shapeBits item first False,
          <- itemsShapeBits True [next, ..more]

theorem argumentsShapeBits ∀ (arguments: List Expr): argumentsShape arguments = bitsShape (argumentsBits arguments) :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite bitsShapeAppend (argument.bits False False) (argumentsBits rest),
          <- shapeBits argument False False,
          <- argumentsShapeBits rest

theorem declShapeBits ∀ (decl: Decl): decl.shape = bitsShape decl.bits := match decl with
  | Definition attributes header (Assigned colonEq value) =>
    rewrite bitsShapeAppend (header.result.bits False False) [
          AWord ((fixedWord ":=" colonEq).bitK False False),
          ..value.bits False False
        ],
        <- shapeBits header.result False False,
        <- shapeBits value False False
  | _ => byComputing

-- The bits' tokens and comments, from the tree's facts.

--| No comment after a token ends in a carriage return or a space, which the lexer takes off.
def afterUnreturned: Option Text → Bool
  | None => True
  | Some text => !text.endsWith "\r" && !text.endsWith " "

def Word.unreturned (word: Word): Bool := word.comments.above.all Note.unreturned && afterUnreturned word.comments.after

def Expr.unreturned: Expr → Bool
  | Atom _ word => word.unreturned
  | Paren open inner close => open.unreturned && inner.unreturned && close.unreturned
  | Tuple open items _ close | ListOf open items _ close => open.unreturned && allUnreturned items && close.unreturned
  | App head arguments => head.unreturned && allUnreturned arguments
  | Infix _ left operator right => left.unreturned && operator.unreturned && right.unreturned
  | Prefix operator operand => operator.unreturned && operand.unreturned
  | _ => False

def allUnreturned: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.unreturned && allUnreturned rest

--| No comment of the declaration ends in a carriage return.
def Decl.unreturned: Decl → Bool
  | Definition _ header (Assigned colonEq value) =>
    (fixedWord "def" header.keyword).unreturned
      && header.name.unreturned
      && (fixedWord ":" header.colon).unreturned
      && header.result.unreturned
      && (fixedWord ":=" colonEq).unreturned
      && value.unreturned
  | _ => False

--| A token's text the lexer reads as one token of a kind that is a comma or closer exactly when the text is, and no
--| comment.
def KindOk (text: Text): Prop :=
  (lexKind text == Comma) = False
    ∧ (lexKind text).isCloser = isCloserText text
    ∧ text.startsWith "--" = False
    ∧ (text == ",") = False

theorem quietCloser ∀ (kind: Tok) (quiet: QuietKind kind): kind.isCloser = False :=
  let (_, paren, square, brace) := quiet
  match closer: kind.isCloser with
    | False => byComputing
    | True =>
      match kind, closer with
        | RParen, _ => (paren byComputing).impossible
        | RBracket, _ => (square byComputing).impossible
        | RBrace, _ => (brace byComputing).impossible
        | _, never => cases

theorem quietKindOk ∀ (kind: Tok) (text: Text) (spells: Spells kind text) (quiet: QuietKind kind): KindOk text :=
  let (notComma, notCloser) := spellsQuiet kind text spells quiet
  let (comma, _, _, _) := quiet
  let same: lexKind text = kind := lexKindOfSpells kind text spells
  (
    (rewrite same then
      match isComma: kind == Comma with
        | True => (comma (DecEq.sound isComma).flipped).impossible
        | False => byComputing),
    (rewrite same, notCloser then quietCloser kind quiet),
    spellsNotComment kind text spells,
    notComma
  )

theorem notBreakOfSound ∀ (text: Text) (real: (!isLayout text) = True): (text == "\n") = False :=
  match broken: text == "\n" with
    | False => byComputing
    | True =>
      match spaces: text.all (char => char == ' ') with
        | False => (Bool.falseNotTrue real).impossible

theorem commentFineOf ∀ (text: Text)
    (sound: commentText text = True)
    (plain: (!text.endsWith "\r" && !text.endsWith " ") = True):
    CommentFine text :=
  (Bool.andLeft sound, unreturnedSame text plain)

theorem notesFineOf ∀ (notes: List Note)
    (sound: notesSound notes = True)
    (plain: notes.all Note.unreturned = True):
    NotesFine notes :=
  match notes with
    | [] => byComputing
    | [note, ..rest] => (
      commentFineOf note.text (Bool.andLeft sound) (Bool.andLeft plain),
      notesFineOf rest (Bool.andRight sound) (Bool.andRight plain)
    )

theorem afterFineOf ∀ (after: Option Text)
    (sound: afterSound after = True)
    (plain: afterUnreturned after = True):
    AfterFine after :=
  match after with
    | None => byComputing
    | Some text => commentFineOf text sound plain

--| A token of the tree, as its reading has it, is one the lexer reads back.
theorem bitFine ∀ (word: Word) (item hoisted: Bool)
    (ok: KindOk word.text)
    (sound: word.sound = True)
    (plain: word.unreturned = True):
    WordFine lexKind (word.bitK item hoisted) :=
  let (notComma, closer, code, textNotComma) := ok
  let unbroken := notBreakOfSound word.text (Bool.andLeft sound)
  let after := afterFineOf word.comments.after (Bool.andRight (Bool.andRight sound)) (Bool.andRight plain)
  let notes := notesFineOf word.comments.above (Bool.andLeft (Bool.andRight sound)) (Bool.andLeft plain)
  match hoisted with
    | True => (notComma, closer, code, unbroken, textNotComma, byComputing, after)
    | False =>
      match word, notes with
        | { text, comments = { above = [], after = trail, blankBefore } }, _ =>
          (notComma, closer, code, unbroken, textNotComma, byComputing, after)
        | { text, comments = { above = [first, ..rest], after = trail, blankBefore } }, notes =>
          (notComma, closer, code, unbroken, textNotComma, notes, after)

theorem prefixKindOk ∀ (text: Text) (spelled: PrefixSpells text): KindOk text ∧ isCloserText text = False :=
  match spelled with
    | Inl same | Inr (Inl same) | Inr (Inr same) =>
      rewrite same then ((byComputing, byComputing, byComputing, byComputing), byComputing)

--| A slice 1 expression's bits are its calm words, with bare commas, and each token one the lexer reads back.
--|
--| Proof idea: by induction on the expression, as `joinable`: a name or numeral spells a quiet kind, a bracket is its
--| text, an operator spells a quiet kind or is `-`, `!` or `¬`; `calm` keeps each token as its bit does.
theorem exprBits ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (lexical: expr.lexical = True)
    (plain: expr.unreturned = True):
    bitsWords (expr.bits item False) = (expr.calm item).words ∧ BitsFine lexKind (expr.bits item False) :=
  match expr with
    | Atom kind word =>
      let spells := spellsOfText1 kind word.text (Bool.andRight within)
      let quiet := wordQuiet kind (Bool.andLeft within)
      let (_, notCloser) := spellsQuiet kind word.text spells quiet
      (
        (rewrite notCloser),
        (bitFine word item False (quietKindOk kind word.text spells quiet) sound plain, byComputing)
      )
    | Paren open inner close =>
      let openText: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let closeText: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let (innerWords, innerFine) :=
        exprBits inner False within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight plain))
      let openOk: KindOk open.text := rewrite openText then (byComputing, byComputing, byComputing, byComputing)
      let closeOk: KindOk close.text := rewrite closeText then (byComputing, byComputing, byComputing, byComputing)
      (
        (rewrite bitsWordsAppend [AWord (open.bitK item False), ..inner.bits False False] [
              AWord (close.bitK False False)
            ],
            openText,
            closeText,
            innerWords),
        bitsFineAppend lexKind
          [AWord (open.bitK item False), ..inner.bits False False]
          [AWord (close.bitK False False)]
          (bitFine open item False openOk (Bool.andLeft sound) (Bool.andLeft plain), innerFine)
          (
            bitFine close False False closeOk
              (Bool.andRight (Bool.andRight sound))
              (Bool.andRight (Bool.andRight plain)),
            byComputing
          )
      )
    | Tuple open items comma close =>
      let openText: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let closeText: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let (itemsWordsSame, itemsFine) :=
        itemsBitsFacts True items within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight plain))
      let openOk: KindOk open.text := rewrite openText then (byComputing, byComputing, byComputing, byComputing)
      let closeOk: KindOk close.text := rewrite closeText then (byComputing, byComputing, byComputing, byComputing)
      (
        (rewrite bitsWordsAppend [AWord (open.bitK item False), ..itemsBits True items] [
              AWord (close.bitK False False)
            ],
            openText,
            closeText,
            itemsWordsSame,
            calmAllFrom items),
        bitsFineAppend lexKind
          [AWord (open.bitK item False), ..itemsBits True items]
          [AWord (close.bitK False False)]
          (bitFine open item False openOk (Bool.andLeft sound) (Bool.andLeft plain), itemsFine)
          (
            bitFine close False False closeOk
              (Bool.andRight (Bool.andRight sound))
              (Bool.andRight (Bool.andRight plain)),
            byComputing
          )
      )
    | ListOf open items comma close =>
      let openText: open.text = "[" := DecEq.sound (Bool.andLeft lexical)
      let closeText: close.text = "]" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let (itemsWordsSame, itemsFine) :=
        itemsBitsFacts
          (!items.all Expr.plainItem)
          items
          within
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight plain))
      let openOk: KindOk open.text := rewrite openText then (byComputing, byComputing, byComputing, byComputing)
      let closeOk: KindOk close.text := rewrite closeText then (byComputing, byComputing, byComputing, byComputing)
      (
        (rewrite bitsWordsAppend [AWord (open.bitK item False), ..itemsBits (!items.all Expr.plainItem) items] [
              AWord (close.bitK False False)
            ],
            openText,
            closeText,
            itemsWordsSame,
            calmItemsFrom items),
        bitsFineAppend lexKind
          [AWord (open.bitK item False), ..itemsBits (!items.all Expr.plainItem) items]
          [AWord (close.bitK False False)]
          (bitFine open item False openOk (Bool.andLeft sound) (Bool.andLeft plain), itemsFine)
          (
            bitFine close False False closeOk
              (Bool.andRight (Bool.andRight sound))
              (Bool.andRight (Bool.andRight plain)),
            byComputing
          )
      )
    | App head arguments =>
      let (headWords, headFine) :=
        exprBits head item (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) (Bool.andLeft plain)
      let (argumentsWords, argumentsFine) :=
        argumentsBitsFacts arguments
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight lexical)
          (Bool.andRight plain)
      (
        (rewrite bitsWordsAppend (head.bits item False) (argumentsBits arguments), headWords, argumentsWords),
        bitsFineAppend lexKind (head.bits item False) (argumentsBits arguments) headFine argumentsFine
      )
    | Infix kind left operator right =>
      let (leftWithin, rightWithin) := infixWithin kind left operator right within
      let listed: operatorText1 operator.text = True := infixListed kind left operator right within
      let (operatorKind, spells, quiet) := operatorSpellsOf operator.text listed
      let (_, notCloser) := spellsQuiet operatorKind operator.text spells quiet
      let (leftWords, leftFine) :=
        exprBits left item leftWithin (Bool.andLeft sound) (Bool.andLeft lexical) (Bool.andLeft plain)
      let (rightWords, rightFine) :=
        exprBits right False rightWithin
          (Bool.andRight (Bool.andRight sound))
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andRight (Bool.andRight plain))
      (
        (rewrite bitsWordsAppend (left.bits item False) [AWord (operator.bitK False False), ..right.bits False False],
            leftWords,
            rightWords,
            notCloser),
        bitsFineAppend lexKind
          (left.bits item False)
          [AWord (operator.bitK False False), ..right.bits False False]
          leftFine
          (
            bitFine operator False False
              (quietKindOk operatorKind operator.text spells quiet)
              (Bool.andLeft (Bool.andRight sound))
              (Bool.andLeft (Bool.andRight plain)),
            rightFine
          )
      )
    | Prefix operator operand =>
      let spelled: PrefixSpells operator.text := prefixSpellsOf operator.text (Bool.andRight within)
      let (operandWords, operandFine) :=
        exprBits operand False (Bool.andLeft within) (Bool.andRight sound) (Bool.andRight lexical) (Bool.andRight plain)
      let (ok, notCloser) := prefixKindOk operator.text spelled
      (
        (rewrite notCloser, operandWords),
        (bitFine operator item False ok (Bool.andLeft sound) (Bool.andLeft plain), operandFine)
      )

theorem itemsBitsFacts ∀ (first: Bool) (items: List Expr)
    (within: allWithin1 items = True)
    (sound: allSound items = True)
    (lexical: allLexical items = True)
    (plain: allUnreturned items = True):
    bitsWords (itemsBits first items) = itemsWords (calmFrom first items) ∧ BitsFine lexKind (itemsBits first items) :=
  match items with
    | [] => (byComputing, byComputing)
    | [item] =>
      let (itemWords, itemFine) :=
        exprBits item first (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) (Bool.andLeft plain)
      ((rewrite itemWords, List.appendNil (item.calm first).words), itemFine)
    | [item, next, ..more] =>
      let (itemWords, itemFine) :=
        exprBits item first (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) (Bool.andLeft plain)
      let (restWords, restFine) :=
        itemsBitsFacts True
          [next, ..more]
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight lexical)
          (Bool.andRight plain)
      (
        (rewrite bitsWordsAppend (item.bits first False) ([AComma] ++ itemsBits True [next, ..more]),
            itemWords,
            restWords),
        bitsFineAppend lexKind (item.bits first False) ([AComma] ++ itemsBits True [next, ..more]) itemFine (
          byComputing,
          restFine
        )
      )

theorem argumentsBitsFacts ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (sound: allSound arguments = True)
    (lexical: allLexical arguments = True)
    (plain: allUnreturned arguments = True):
    bitsWords (argumentsBits arguments) = itemsWords (calmAll False arguments)
      ∧ BitsFine lexKind (argumentsBits arguments) :=
  match arguments with
    | [] => (byComputing, byComputing)
    | [argument, ..rest] =>
      let (argumentWords, argumentFine) :=
        exprBits argument False (Bool.andLeft within) (Bool.andLeft sound) (Bool.andLeft lexical) (Bool.andLeft plain)
      let (restWords, restFine) :=
        argumentsBitsFacts rest
          (Bool.andRight within)
          (Bool.andRight sound)
          (Bool.andRight lexical)
          (Bool.andRight plain)
      (
        (rewrite bitsWordsAppend (argument.bits False False) (argumentsBits rest), argumentWords, restWords),
        bitsFineAppend lexKind (argument.bits False False) (argumentsBits rest) argumentFine restFine
      )

--| A slice 1 declaration's bits are the words `stands` reads, with bare commas, and each token one the lexer reads
--| back.
--|
--| Proof idea: `def`, `:` and `:=` are their texts, the name spells `Lower`, and `exprBits` gives the type and value;
--| the first word's comments above are hoisted as `stood` takes them off.
theorem declBits ∀ (decl: Decl)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical = True)
    (plain: decl.unreturned = True):
    bitsWords decl.bits = decl.stood ∧ BitsFine lexKind decl.bits :=
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
          let nameWithin := Bool.andLeft (Bool.andLeft within)
          let (nameKind, spells, quiet, _) := nameKinded name nameWithin
          let (_, nameNotCloser) := spellsQuiet nameKind name.text spells quiet
          let (resultWords, resultFine) :=
            exprBits result False
              (Bool.andRight (Bool.andLeft within))
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight sound))))
              (Bool.andLeft (Bool.andRight lexical))
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight plain))))
          let (valueWords, valueFine) :=
            exprBits value False
              (Bool.andRight within)
              (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
              (Bool.andRight (Bool.andRight lexical))
              (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight plain)))))
          (
            (rewrite bitsWordsAppend (result.bits False False) [
                  AWord ((fixedWord ":=" colonEq).bitK False False),
                  ..value.bits False False
                ],
                resultWords,
                valueWords,
                nameNotCloser),
            (
              bitFine
                (fixedWord "def" keyword)
                False
                True
                (byComputing, byComputing, byComputing, byComputing)
                (Bool.andLeft sound)
                (Bool.andLeft plain),
              bitFine name False False
                (quietKindOk nameKind name.text spells quiet)
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andLeft (Bool.andRight plain)),
              bitFine
                (fixedWord ":" colon)
                False
                False
                (byComputing, byComputing, byComputing, byComputing)
                (Bool.andLeft (Bool.andRight (Bool.andRight sound)))
                (Bool.andLeft (Bool.andRight (Bool.andRight plain))),
              bitsFineAppend lexKind
                (result.bits False False)
                [AWord ((fixedWord ":=" colonEq).bitK False False), ..value.bits False False]
                resultFine
                (
                  bitFine
                    (fixedWord ":=" colonEq)
                    False
                    False
                    (byComputing, byComputing, byComputing, byComputing)
                    (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight sound)))))
                    (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight plain))))),
                  valueFine
                )
            )
          )
        | _ => (Bool.falseNotTrue within).impossible

-- The engine end.

--| A reading no wider than another reads the same events.
theorem refinesReads ∀ (told shape: List Told) (events: List Event)
    (refines: Refines told shape)
    (reads: ReadsAs told events):
    ReadsAs shape events :=
  match told, shape, refines with
    | [], [], _ => reads
    | [Gap, ..more], [Gap, ..rest], (_, tail) =>
      match events, reads with
        | [event, ..later], (blank, readsMore) => (blank, refinesReads more rest later tail readsMore)
    | [Said text starts follows, ..more], [Said other first second, ..rest], (
        (same, startsWider, followsWider),
        tail
      ) =>
      match events, reads with
        | [event, ..later], (word, allowed, readsMore) => (
          rewrite <- same then word,
          widerStarts starts follows first second event.start startsWider followsWider allowed,
          refinesReads more rest later tail readsMore
        )
    | _, _, never => cases

theorem widerStarts ∀ (starts follows first second: Bool) (start: Option Nat)
    (startsWider: starts = True → first = True)
    (followsWider: follows = True → second = True)
    (allowed: startsAs starts follows start = True):
    startsAs first second start = True :=
  match start with
    | Some _ => startsWider allowed
    | None => followsWider allowed

--| The lexer's leaves of a declaration's printed text are the trace's, read by `hearAll`.
theorem leavesHeard ∀ (doc: Doc)
    (ends: CommentsEnd (printedPieces doc width).reverse):
    (Fmt.OutputStatements.laidOf doc).leaves.map Leaf.view
      = (hearAll lexKind (eventsOf (printedPieces doc width).reverse)).views :=
  let texts := printedPieces doc width
  let laid: Fmt.OutputStatements.laidOf doc = Fmt.PrintHangProofs.laidOf lexKind texts.reverse :=
    rewrite pieceFoldLay lexKind texts Laid.start, laidOfFold lexKind texts.reverse, List.reverseReverse texts
  let (views, _) := laidHears lexKind texts.reverse ends
  rewrite laid then views

--| Whether a document lays at all, from the start of an unindented line: `Std.Doc`'s `Lays` with nothing asked of
--| where the words land. It is all `standsOfLays` needs of the columns: `printTold` reads line starts and blank lines
--| from any laying.
def LaysSomehow (doc: Doc): Prop := Std.Doc.Proofs.Lays doc 0 (AtStart 0 Carry.none) [] (place laid => True)

--| `printedStands1` for a declaration and its document, with what the statement adds: no comment ends in a
--| carriage return (`unreturned`), and that the document lays at all (`LaysSomehow`): no fact about columns.
--|
--| Proof idea: the document lays, so `printTold` reads its laid trace as `told`, which refines the
--| tree's shape (`printedTold`), the reading of its bits (`declShapeBits`); the printed events tuck that trace
--| (`Tucks`), and hearing them (`bitsHeard`) gives views that `heardStands` reads as `stands` of the bits' words,
--| `decl.stood` (`declBits`). The lexer's leaves are those views (`leavesHeard`), as the joins end each comment's
--| line (`pairsEnd`).
theorem standsOfLays ∀ (decl: Decl) [doc: Doc]
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (plain: decl.unreturned = True)
    (lays: LaysSomehow doc)
    (shows: decl.doc1 = Some doc):
    stands None decl.stood (Fmt.OutputStatements.laidOf doc).leaves.reverse = True :=
  let spelled := declOperators decl within
  let real := declReal decl within lexical spelled
  let sound := declSoundOfSettled decl within settled real
  let joins := declJoins decl within shaped sound lexical spelled
  let (uniform, _, words) := doc1Spells decl doc within sound shows
  let (_, _, pairs) :=
    printedJoins
      (Follows lexKind)
      (Printable lexKind)
      doc
      width
      uniform
      (doc1Passes lexKind decl doc within joins shows)
      (rewrite words then declPrintable decl within sound lexical spelled)
  let ends := pairsEnd lexKind (printedPieces doc width).reverse pairs
  let (refines, _) := printedTold decl doc within settled real joins shows
  let (bitsStood, fine) := declBits decl within sound lexical plain
  let (place, laid, _, reads, (stretches, (fits, _, laidIs, printedIs))) :=
    printTold (place laid => True) doc width lays
  let shapeReads: ReadsAs (bitsShape decl.bits) ([] ++ laidOf stretches) :=
    rewrite <- declShapeBits decl, <- laidIs then refinesReads (doc.told Spot.lineStart) decl.shape laid refines reads
  let (views, (viewsIs, heard)) :=
    bitsHeard lexKind decl.bits None [] stretches Hearing.start fine fits byComputing shapeReads byComputing byComputing
  let heardViews: (hearAll lexKind (eventsOf (printedPieces doc width).reverse)).views = views :=
    rewrite printedIs then Eq.trans viewsIs (List.appendNil views)
  rewrite <- bitsStood then
    heardStands None decl.bits
      (Fmt.OutputStatements.laidOf doc).leaves.reverse
      (rewrite List.mapReverse (Fmt.OutputStatements.laidOf doc).leaves Leaf.view, leavesHeard doc ends, heardViews then
        heard)

--| `standsOfLays` from the facts `printedHangs` takes (`DeclHangs`), from which the document lays (`doc1Hangs`).
theorem standsOfDoc ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (plain: decl.unreturned = True)
    (facts: DeclHangs lexKind decl)
    (shows: decl.doc1 = Some doc):
    stands None decl.stood (Fmt.OutputStatements.laidOf doc).leaves.reverse = True :=
  standsOfLays decl within shaped settled lexical plain
    (doc1Hangs lexKind decl doc within lexKindFixed facts shows
      (AtStart 0 Carry.none) _
      []
      (place laid => True)
      byComputing
      (byComputing, byComputing)
      (after hang later same holds => byComputing))
    shows

--| `printedStands1`, as proved: the four tree facts, no comment ending in a carriage return, and `DeclHangs`. It is
--| false without `unreturned`.
theorem printedStands1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (plain: decl.unreturned = True)
    (facts: DeclHangs lexKind decl):
    decl.stands = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      standsOfDoc
        (Definition [] header (Assigned colonEq value))
        (defDoc header colonEq value)
        within
        shaped
        settled
        lexical
        plain
        facts
        byComputing
