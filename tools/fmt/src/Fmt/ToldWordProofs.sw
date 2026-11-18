--| What the rules' documents tell of a word (SW-4049, F2 of SW-4042).
namespace Fmt.ToldWordProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Note, Word)
import Fmt (..)
import Fmt.HangProofs (solidSpaces)
import Fmt.SpellProofs (..)

--| Telling twice, then once more, in either grouping.
theorem tellingAssoc ∀ (one two three: Telling): (one.andThen two).andThen three = one.andThen (two.andThen three) :=
  match one, two, three with
    | { said = a, after = x }, { said = b, after = y }, { said = c, after = z } => rewrite List.appendAssoc a b c

--| Nothing said, nothing moved.
theorem tellingQuietLeft ∀ (spot: Spot) (telling: Telling): (Telling.quiet spot).andThen telling = telling :=
  match telling with | { said, after } => byComputing

theorem tellingQuietRight ∀ (telling: Telling): telling.andThen (Telling.quiet telling.after) = telling :=
  match telling with | { said, after } => rewrite List.appendNil said

--| A list of documents told in two parts: the first from the spot, the second from where the first left the printer.
theorem tellAllAppend ∀ (docs more: List Doc) (spot: Spot):
    Doc.tellAll (docs ++ more) spot
      = (Doc.tellAll docs spot).andThen (Doc.tellAll more (Doc.tellAll docs spot).after) :=
  match docs with
    | [] => (tellingQuietLeft spot (Doc.tellAll more spot)).flipped
    | [doc, ..rest] =>
      calc Doc.tellAll [doc, ..rest ++ more] spot
        _ = (doc.tell spot).andThen (Doc.tellAll (rest ++ more) (doc.tell spot).after) := byComputing
        _ = (doc.tell spot).andThen
            ((Doc.tellAll rest (doc.tell spot).after).andThen
              (Doc.tellAll more (Doc.tellAll rest (doc.tell spot).after).after)) :=
          rewrite tellAllAppend rest more (doc.tell spot).after
        _ = ((doc.tell spot).andThen (Doc.tellAll rest (doc.tell spot).after)).andThen
            (Doc.tellAll more (Doc.tellAll rest (doc.tell spot).after).after) := (tellingAssoc _ _ _).flipped

--| Leaving out the empty documents changes nothing told.
theorem filterTell ∀ (docs: List Doc) (spot: Spot):
    Doc.tellAll (docs.filter (doc => not doc.isEmpty)) spot = Doc.tellAll docs spot :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] =>
      match empty: doc.isEmpty with
        | True =>
          match doc, empty with
            | Doc.Nothing, _ => filterTell rest spot
        | False => rewrite filterTell rest (doc.tell spot).after

--| `Doc.concat` tells as the documents one after another.
theorem concatTell ∀ (docs: List Doc) (spot: Spot): (Doc.concat docs).tell spot = Doc.tellAll docs spot :=
  let kept := filterTell docs spot
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] => Eq.trans (tellingQuietRight (only.tell spot)).flipped kept
    | [first, second, ..rest] => kept

--| A word that is not layout is told as one word, starting a line where a line may start and following words where
--| words may be.
theorem chunkTellSolid ∀ (text: Text) (spot: Spot)
    (solid: isLayout text = False):
    chunkTell text spot = { said = [Said text (spot.fresh || spot.held) spot.mid], after = Spot.afterWords } :=
  rewrite wordFilled text solid, solidSpaces text solid

theorem textLineTell ∀ (text: Text)
    (solid: isLayout text = False):
    Doc.tellAll [Doc.text text, HardLine] Spot.lineStart = { said = [Said text True False], after = Spot.lineStart } :=
  rewrite chunkTellSolid text Spot.lineStart solid

-- Own-line comments.

--| What one own-line comment says: a blank line above it if it is flagged, then its text on a line of its own.
def noteTold (note: Note): List Told := (if note.blankBefore then [Gap] else []) ++ [Said note.text True False]

def notesTold: List Note → List Told
  | [] => []
  | [note, ..rest] => noteTold note ++ notesTold rest

--| The notes with the first one's blank-line flag cleared unless `keep`: what `notesAbove keep` and `closerNotes`
--| (`keep` false) write, as `Comments.kept` has it.
def gated (keep: Bool): List Note → List Note
  | [] => []
  | [first, ..rest] => if keep then [first, ..rest] else [{ first | blankBefore = False }, ..rest]

theorem gatedTrue ∀ (notes: List Note): gated True notes = notes := match notes with
  | [] => byComputing
  | [first, ..rest] => byComputing

--| The comments after a closer's first, each on a line of its own after any blank line: told from any spot, since
--| each starts with a `HardLine`.
theorem laterCloserNotesTell ∀ (note: Note) (rest: List Note) (spot: Spot)
    (sound: notesSound [note, ..rest] = True):
    Doc.tellAll (laterCloserNotes [note, ..rest]) spot = { said = notesTold [note, ..rest], after = Spot.afterWords } :=
  let solid := commentNotLayout note.text (Bool.andLeft sound)
  match rest with
    | [] =>
      match note.blankBefore with
        | True => rewrite chunkTellSolid note.text Spot.lineStart solid
        | False => rewrite chunkTellSolid note.text Spot.lineStart solid
    | [next, ..more] =>
      let ih := laterCloserNotesTell next more Spot.afterWords (Bool.andRight sound)
      match note.blankBefore with
        | True => rewrite chunkTellSolid note.text Spot.lineStart solid, ih
        | False => rewrite chunkTellSolid note.text Spot.lineStart solid, ih

--| A closer's own-line comments, from a line start (`LineStartHere`): the first has no blank line above it.
theorem closerNotesTell ∀ (notes: List Note)
    (sound: notesSound notes = True):
    Doc.tellAll (closerNotes notes) Spot.lineStart
      = { said = notesTold (gated False notes), after = if notes.isEmpty then Spot.lineStart else Spot.afterWords } :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      let solid := commentNotLayout note.text (Bool.andLeft sound)
      match rest with
        | [] => rewrite chunkTellSolid note.text Spot.lineStart solid
        | [next, ..more] =>
          rewrite chunkTellSolid note.text Spot.lineStart solid,
              laterCloserNotesTell next more Spot.afterWords (Bool.andRight sound)

--| Own-line comments above a token, from a line start: each on a line, a blank line above one if flagged.
theorem notesAboveTell ∀ (keep: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    Doc.tellAll (notesAbove keep notes) Spot.lineStart
      = { said = notesTold (gated keep notes), after = Spot.lineStart } :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      let solid := commentNotLayout note.text (Bool.andLeft sound)
      let ih := notesAboveTell True rest (Bool.andRight sound)
      match note.blankBefore, keep with
        | True, True => rewrite chunkTellSolid note.text Spot.lineStart solid, ih, gatedTrue rest
        | True, False => rewrite chunkTellSolid note.text Spot.lineStart solid, ih, gatedTrue rest
        | False, True => rewrite chunkTellSolid note.text Spot.lineStart solid, ih, gatedTrue rest
        | False, False => rewrite chunkTellSolid note.text Spot.lineStart solid, ih, gatedTrue rest

-- A word's comments, as the rules keep their blank-line flags.

--| What a word's comments above it say, and the blank line below them, as `Comments.kept` has the flags.
def Comments.toldAbove (comments: Comments): List Told :=
  notesTold comments.above ++ (if comments.blankBefore then [Gap] else [])

--| With no comments above, the blank line is told only above an item.
theorem keptNone ∀ (after: Option Text) (blankBefore item closer: Bool):
    ({ above = [], after, blankBefore }.kept item closer).toldAbove = if item && blankBefore then [Gap] else [] :=
  match item, blankBefore with
    | True, True => byComputing
    | True, False => byComputing
    | False, True => byComputing
    | False, False => byComputing

--| With comments above a token that is no closer: the first one's blank line only above an item, the blank line
--| below the last as written.
theorem keptNoted ∀ (first: Note) (rest: List Note) (after: Option Text) (blankBefore item: Bool):
    ({ above = [first, ..rest], after, blankBefore }.kept item False).toldAbove
      = notesTold (gated item [first, ..rest]) ++ (if blankBefore then [Gap] else []) :=
  match first.blankBefore, item, blankBefore with
    | True, True, True => byComputing
    | True, True, False => byComputing
    | True, False, True => byComputing
    | True, False, False => byComputing
    | False, True, True => byComputing
    | False, True, False => byComputing
    | False, False, True => byComputing
    | False, False, False => byComputing

--| With comments above a closer: the first has no blank line above it and nothing is told below the last.
theorem keptCloser ∀ (first: Note) (rest: List Note) (after: Option Text) (blankBefore item: Bool):
    ({ above = [first, ..rest], after, blankBefore }.kept item True).toldAbove
      = notesTold (gated False [first, ..rest]) :=
  match first.blankBefore, item, blankBefore with
    | True, True, True => rewrite List.appendNil (notesTold rest)
    | True, True, False => rewrite List.appendNil (notesTold rest)
    | True, False, True => rewrite List.appendNil (notesTold rest)
    | True, False, False => rewrite List.appendNil (notesTold rest)
    | False, True, True => rewrite List.appendNil (notesTold rest)
    | False, True, False => rewrite List.appendNil (notesTold rest)
    | False, False, True => rewrite List.appendNil (notesTold rest)
    | False, False, False => rewrite List.appendNil (notesTold rest)

-- What a word writes before its text.

--| The word as the leaf prints it, for the lexer to read: its comments as `Comments.kept` has them, but for the
--| own-line comments and blank line that an enclosing element writes when the word is `hoisted`. This is the
--| tree's `calm` word (`stood` for a declaration's first), where `stands` reads one.
def Word.printed (word: Word) (around: Around): Word :=
  if around.hoisted then { word | comments = { above = [], after = word.comments.after, blankBefore = False } }
  else { word | comments = word.comments.kept around.item (isCloserText word.text) }

--| What `Word.leading` says: the printed word's own-line comments and blank line.
def Word.toldLead (word: Word) (around: Around): List Told := (word.printed around).comments.toldAbove

--| Whether `Word.leading` leaves the printer at a line start: it writes comments or a kept blank line.
def Word.leadsLine (word: Word) (around: Around): Bool :=
  !around.hoisted && (!word.comments.above.isEmpty || (around.item && word.comments.blankBefore))

--| The comments above a token, then its kept blank line, from a line start.
theorem notesAboveBlankTell ∀ (keep: Bool) (notes: List Note) (blankBefore: Bool)
    (sound: notesSound notes = True):
    Doc.tellAll (notesAbove keep notes ++ (if blankBefore then [Blank] else [])) Spot.lineStart
      = { said = notesTold (gated keep notes) ++ (if blankBefore then [Gap] else []), after = Spot.lineStart } :=
  match blankBefore with
    | True => rewrite tellAllAppend (notesAbove keep notes) [Blank] Spot.lineStart, notesAboveTell keep notes sound
    | False => rewrite tellAllAppend (notesAbove keep notes) [] Spot.lineStart, notesAboveTell keep notes sound

--| A closer's own-line comments, written at the indentation of its items, and the line of its own that follows.
theorem closerLeadTell ∀ (first: Note) (rest: List Note) (key: Nat) (spot: Spot)
    (sound: notesSound [first, ..rest] = True):
    Doc.tellAll [BreakParent, Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]), CloserLine key] spot
      = { said = notesTold (gated False [first, ..rest]), after = Spot.lineStart } :=
  calc Doc.tellAll
    [BreakParent, Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]), CloserLine key]
    spot
    _ = ((Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]).tell spot).andThen
        (Telling.quiet Spot.lineStart) := byComputing
    _ = (Doc.tellAll [LineStartHere, ..closerNotes [first, ..rest]] spot).andThen (Telling.quiet Spot.lineStart) :=
      rewrite concatTell [LineStartHere, ..closerNotes [first, ..rest]] spot
    _ = (Telling.quiet Spot.lineStart).andThen
        ((Doc.tellAll (closerNotes [first, ..rest]) Spot.lineStart).andThen (Telling.quiet Spot.lineStart)) :=
      byComputing
    _ = { said = notesTold (gated False [first, ..rest]), after = Spot.lineStart } :=
      rewrite closerNotesTell [first, ..rest] sound, List.appendNil (notesTold (gated False [first, ..rest]))

--| `Word.leading` tells the word's own-line comments and kept blank line, from any spot, and ends at a line start if
--| it wrote any.
--|
--| Proof idea: cases on whether the word is hoisted, has comments above it, and is a closer; each branch's documents
--| are told by the lemmas on notes (`notesAboveTell`, `closerNotesTell`) and by computing, `Comments.kept` read by
--| `keptNone`, `keptNoted` and `keptCloser`.
theorem leadingTell ∀ (word: Word) (around: Around) (key: Nat) (spot: Spot)
    (sound: word.sound = True):
    Doc.tellAll (word.leading around key) spot
      = { said = word.toldLead around, after = if word.leadsLine around then Spot.lineStart else spot } :=
  match word, around.hoisted with
    | { text, comments = { above, after, blankBefore } }, True => byComputing
    | { text, comments = { above = [], after, blankBefore } }, False =>
      match around.item, blankBefore with
        | True, True => rewrite keptNone after True True (isCloserText text)
        | True, False => rewrite keptNone after False True (isCloserText text)
        | False, True => rewrite keptNone after True False (isCloserText text)
        | False, False => rewrite keptNone after False False (isCloserText text)
    | { text, comments = { above = [first, ..rest], after, blankBefore } }, False =>
      match same: isCloserText text with
        | True =>
          rewrite closerLeadTell first rest key spot (Bool.andLeft (Bool.andRight sound)),
              keptCloser first rest after blankBefore around.item
        | False =>
          rewrite notesAboveBlankTell around.item [first, ..rest] blankBefore (Bool.andLeft (Bool.andRight sound)),
              keptNoted first rest after blankBefore around.item

-- A word's text.

--| Whether `piece` writes the text as a `Closing`, which stays on the line of a waiting comment.
def closing (text: Text): Bool := isCloserText text || text == ","

--| What the word `text` says where the printer may be at `spot`, and where it may be after: a closer slips in front of
--| a waiting comment, which still waits; anything else starts a line after a comment and a line start, and follows
--| words after words.
def wordTelling (text: Text) (spot: Spot): Telling :=
  if closing text && spot.held then
    {
      said = [Said text spot.fresh (spot.mid || spot.held)],
      after = { fresh = False, mid = spot.fresh || spot.mid, held = True }
    }
  else { said = [Said text (spot.fresh || spot.held) spot.mid], after = Spot.afterWords }

--| A word's piece tells as `wordTelling`.
theorem pieceTell ∀ (text: Text) (spot: Spot)
    (solid: isLayout text = False):
    (piece text).tell spot = wordTelling text spot :=
  match same: closing text, spot.held with
    | True, True => rewrite wordFilled text solid, solidSpaces text solid
    | True, False => rewrite wordFilled text solid, solidSpaces text solid
    | False, True => rewrite wordFilled text solid, solidSpaces text solid
    | False, False => rewrite wordFilled text solid, solidSpaces text solid

-- A token on its own.

--| What a trailing comment says: the comment, on the line of the word before it.
def Word.toldTrail (word: Word): List Told := match word.comments.after with
  | Some comment => [Said comment False True]
  | None => []

--| Whether the closer takes a line of its own (`ownLine`): code before it ends its line with a comment, and it holds
--| a comment of its own and none above it.
def Word.ownsLine (word: Word) (around: Around): Bool :=
  isCloserText word.text && !word.noted && around.before && word.trails

--| A word's piece, after the line break a closer of its own gets if it does, then its trailing comment.
theorem bodyTell ∀ (word: Word) (own: Bool) (key: Nat) (spot: Spot)
    (solid: isLayout word.text = False):
    Doc.tellAll ((if own then [CloserLine key] else []) ++ [piece word.text] ++ word.trailing) spot
      = {
        said = (wordTelling word.text (if own then Spot.lineStart else spot)).said ++ word.toldTrail,
        after = if word.trails then Spot.afterComment
        else (wordTelling word.text (if own then Spot.lineStart else spot)).after
      } :=
  match word with
    | { text, comments = { above, after, blankBefore } } =>
      match own, after with
        | True, None => rewrite pieceTell text Spot.lineStart solid
        | True, Some comment => rewrite pieceTell text Spot.lineStart solid
        | False, None => rewrite pieceTell text spot solid
        | False, Some comment => rewrite pieceTell text spot solid

--| Where the printer is when a word's own text is reached: at a line start if its comments, a kept blank line or a line
--| of its own for a closer come first, else where it was.
def Word.textSpot (word: Word) (around: Around) (spot: Spot): Spot :=
  if word.leadsLine around || word.ownsLine around then Spot.lineStart else spot

--| What `Word.leaf` tells: the own-line comments and blank lines the rules keep, the text, its trailing comment.
def Word.leafTelling (word: Word) (around: Around) (spot: Spot): Telling := {
  said = word.toldLead around ++ (wordTelling word.text (word.textSpot around spot)).said ++ word.toldTrail,
  after = if word.trails then Spot.afterComment else (wordTelling word.text (word.textSpot around spot)).after
}

--| A token's document tells the word as the rules keep it.
--|
--| Proof idea: the document is the concat of `leading`, an optional `CloserLine`, the piece and the trailing comment;
--| `tellAllAppend` splits it, `leadingTell` tells the first part and ends at a line start if it wrote anything, and
--| `bodyTell` the rest; the four cases of whether it led a line and whether it takes one close the sum.
theorem leafTell ∀ (word: Word) (around: Around) (key: Nat) (spot: Spot)
    (sound: word.sound = True):
    (word.leaf around key).tell spot = word.leafTelling around spot :=
  let solid := Bool.notTrue (isLayout word.text) (Bool.andLeft sound)
  rewrite concatTell
        (word.leading around key
          ++ (if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else [])
          ++ [piece word.text]
          ++ word.trailing)
        spot,
      tellAllAppend
        (word.leading around key)
        ((if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else [])
          ++ [piece word.text]
          ++ word.trailing)
        spot,
      leadingTell word around key spot sound,
      bodyTell word
        (isCloserText word.text && !word.noted && around.before && word.trails)
        key
        (if word.leadsLine around then Spot.lineStart else spot)
        solid then
    match word.leadsLine around, word.ownsLine around with
      | True, True => byComputing
      | True, False => byComputing
      | False, True => byComputing
      | False, False => byComputing
