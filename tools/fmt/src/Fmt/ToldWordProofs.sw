--| What the rules' documents tell of a word (SW-4049, F2 of SW-4042).
namespace Fmt.ToldWordProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Expr, Note, Tok, Word)
import Fmt (..)
import Fmt.SpellProofs (..)
import Syntax.SharedFacts (solidSpaces)

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

-- Own-line comments.

--| What one own-line comment says: a blank line above it if it is flagged, then its text on a line of its own.
def noteTold (note: Note): List Told := (if note.blankBefore then [Gap] else []) ++ [Said note.text True False]

def notesTold: List Note → List Told
  | [] => []
  | [note, ..rest] => noteTold note ++ notesTold rest

--| The comments after a closer's first, each on a line of its own after any blank line: told from any spot, since
--| each starts with a `HardLine`.
theorem laterCloserNotesTell ∀ (note: Note) (rest: List Note) (spot: Spot)
    (sound: notesSound [note, ..rest] = True):
    Doc.tellAll (laterCloserNotes [note, ..rest]) spot = { said = notesTold [note, ..rest], after = Spot.afterWords } :=
  let solid := commentNotLayout note.text (Bool.andLeft sound)
  match rest with
    | [] =>
      match note.blankBefore with
        | True | False => rewrite chunkTellSolid note.text Spot.lineStart solid
    | [next, ..more] =>
      let ih := laterCloserNotesTell next more Spot.afterWords (Bool.andRight sound)
      match note.blankBefore with
        | True | False => rewrite chunkTellSolid note.text Spot.lineStart solid, ih

--| A closer's own-line comments, from a line start (`LineStartHere`): each on a line, a blank line above one if
--| flagged.
theorem closerNotesTell ∀ (notes: List Note)
    (sound: notesSound notes = True):
    Doc.tellAll (closerNotes notes) Spot.lineStart
      = { said = notesTold notes, after = if notes.isEmpty then Spot.lineStart else Spot.afterWords } :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      let solid := commentNotLayout note.text (Bool.andLeft sound)
      match rest with
        | [] =>
          match note.blankBefore with
            | True | False => rewrite chunkTellSolid note.text Spot.lineStart solid
        | [next, ..more] =>
          let ih := laterCloserNotesTell next more Spot.afterWords (Bool.andRight sound)
          match note.blankBefore with
            | True | False => rewrite chunkTellSolid note.text Spot.lineStart solid, ih

--| Own-line comments above a token, from a line start: each on a line, a blank line above one if flagged.
theorem notesAboveTell ∀ (notes: List Note)
    (sound: notesSound notes = True):
    Doc.tellAll (notesAbove notes) Spot.lineStart = { said = notesTold notes, after = Spot.lineStart } :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      let solid := commentNotLayout note.text (Bool.andLeft sound)
      let ih := notesAboveTell rest (Bool.andRight sound)
      match note.blankBefore with
        | True | False => rewrite chunkTellSolid note.text Spot.lineStart solid, ih

-- A word's comments, as the rules keep their blank-line flags.

--| What a word's comments above it say, and the blank line below them, as `Comments.kept` has the flags.
def Comments.toldAbove (comments: Comments): List Told :=
  notesTold comments.above ++ (if comments.blankBefore then [Gap] else [])

--| With no comments above, the blank line is told only above an item.
theorem keptNone ∀ (after: Option Text) (blankBefore item closer: Bool):
    ({ above = [], after, blankBefore }.kept item closer).toldAbove = if item && blankBefore then [Gap] else [] :=
  match item, blankBefore with | True | False, True | False => byComputing

--| With comments above a token that is no closer: the comments' blank lines and the blank line below the last as
--| written.
theorem keptToldAbove ∀ (first: Note) (rest: List Note) (after: Option Text) (blankBefore item: Bool):
    ({ above = [first, ..rest], after, blankBefore }.kept item False).toldAbove
      = notesTold [first, ..rest] ++ (if blankBefore then [Gap] else []) :=
  match blankBefore with | True | False => byComputing

--| With comments above a closer: nothing is told below the last.
theorem keptCloser ∀ (first: Note) (rest: List Note) (after: Option Text) (blankBefore item: Bool):
    ({ above = [first, ..rest], after, blankBefore }.kept item True).toldAbove = notesTold [first, ..rest] :=
  match blankBefore with | True | False => List.appendNil (notesTold [first, ..rest])

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
theorem notesAboveBlankTell ∀ (notes: List Note) (blankBefore: Bool)
    (sound: notesSound notes = True):
    Doc.tellAll (notesAbove notes ++ (if blankBefore then [Blank] else [])) Spot.lineStart
      = { said = notesTold notes ++ (if blankBefore then [Gap] else []), after = Spot.lineStart } :=
  match blankBefore with
    | True => rewrite tellAllAppend (notesAbove notes) [Blank] Spot.lineStart, notesAboveTell notes sound
    | False => rewrite tellAllAppend (notesAbove notes) [] Spot.lineStart, notesAboveTell notes sound

--| A closer's own-line comments, written at the indentation of its items, and the line of its own that follows.
theorem closerLeadTell ∀ (first: Note) (rest: List Note) (key: Nat) (spot: Spot)
    (sound: notesSound [first, ..rest] = True):
    Doc.tellAll [BreakParent, Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]), CloserLine key] spot
      = { said = notesTold [first, ..rest], after = Spot.lineStart } :=
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
    _ = { said = notesTold [first, ..rest], after = Spot.lineStart } :=
      rewrite closerNotesTell [first, ..rest] sound, List.appendNil (notesTold [first, ..rest])

--| `Word.leading` tells the word's own-line comments and kept blank line, from any spot, and ends at a line start if
--| it wrote any.
--|
--| Proof idea: cases on whether the word is hoisted, has comments above it, and is a closer; each branch's documents
--| are told by the lemmas on notes (`notesAboveTell`, `closerNotesTell`) and by computing, `Comments.kept` read by
--| `keptNone`, `keptToldAbove` and `keptCloser`.
theorem leadingTell ∀ [word: Word] (around: Around) (key: Nat) (spot: Spot)
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
          rewrite notesAboveBlankTell [first, ..rest] blankBefore (Bool.andLeft (Bool.andRight sound)),
              keptToldAbove first rest after blankBefore around.item

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
    | True | False, True | False => rewrite wordFilled text solid, solidSpaces text solid

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
      leadingTell around key spot sound,
      bodyTell word
        (isCloserText word.text && !word.noted && around.before && word.trails)
        key
        (if word.leadsLine around then Spot.lineStart else spot)
        solid then
    match word.leadsLine around, word.ownsLine around with | True | False, True | False => byComputing

-- An opening bracket.

--| A mark writes nothing.
theorem markTell ∀ (mark: Bool) (key: Nat) (rest: List Doc) (spot: Spot):
    Doc.tellAll ((if mark then [Mark key] else []) ++ rest) spot = Doc.tellAll rest spot :=
  match mark with | True | False => byComputing

--| An opening bracket tells as any word of the rules: the mark its closer may need writes nothing.
--|
--| Proof idea: as `leafTell`, with the mark in place of the closer's line, and no line of its own since the text is no
--| closer.
theorem openingTell ∀ (word: Word) (around: Around) (closer: Word) (spot: Spot)
    (sound: word.sound = True)
    (open: isCloserText word.text = False):
    (word.opening around closer).tell spot = word.leafTelling around spot :=
  let solid := Bool.notTrue (isLayout word.text) (Bool.andLeft sound)
  rewrite concatTell
        (word.leading around around.at
          ++ (if closer.noted || closer.trails then [Mark around.at] else [])
          ++ [piece word.text]
          ++ word.trailing)
        spot,
      tellAllAppend
        (word.leading around around.at)
        ((if closer.noted || closer.trails then [Mark around.at] else []) ++ [piece word.text] ++ word.trailing)
        spot,
      leadingTell around around.at spot sound,
      markTell
        (closer.noted || closer.trails)
        around.at
        ([piece word.text] ++ word.trailing)
        (if word.leadsLine around then Spot.lineStart else spot),
      bodyTell word False around.at (if word.leadsLine around then Spot.lineStart else spot) solid,
      open then
    match word.leadsLine around with | True | False => byComputing

-- An atom and a framed node.

--| Where the printer is after a word's own-line comments, if it writes any.
def Word.leadSpot (word: Word) (around: Around) (spot: Spot): Spot :=
  if word.leadsLine around then Spot.lineStart else spot

--| Where the printer is before a node's document inside its frame: after the first token's own-line comments, and
--| past the line a waiting comment ends if the node is displaced.
def Word.placedSpot (word: Word) (around: Around) (spot: Spot): Spot :=
  if word.displaces around then (word.leadSpot around spot).displaced else word.leadSpot around spot

--| A node's frame tells its first token's own-line comments, then the node's document from where they leave the
--| printer.
--|
--| Proof idea: the frame is the concat of the token's `leading`, told by `leadingTell`, and the document, displaced
--| or not.
theorem framedTell ∀ (first: Word) (around: Around) (doc: Doc) (spot: Spot)
    (sound: first.sound = True):
    (framedBy first around doc).tell spot
      = {
        said = first.toldLead around ++ (doc.tell (first.placedSpot around spot)).said,
        after = (doc.tell (first.placedSpot around spot)).after
      } :=
  rewrite concatTell
        [Doc.concat (first.leading around around.at), if first.displaces around then Displaced doc else doc]
        spot,
      concatTell (first.leading around around.at) spot,
      leadingTell around around.at spot sound then
    match first.displaces around with
      | True => rewrite List.appendNil (doc.tell (first.leadSpot around spot).displaced).said
      | False => rewrite List.appendNil (doc.tell (first.leadSpot around spot)).said

-- Brackets without commas.

--| Where the printer is when a bracket's inner expression starts: a block starts a line below the bracket.
def Expr.innerSpot (inner: Expr) (spot: Spot): Spot := match inner with
  | Block _ _ _ => Spot.lineStart
  | _ => spot

--| What stands between a bracket's tokens tells as the inner expression's element, from where it starts.
theorem parenInnerTell ∀ (inner: Expr) (around: Around) (spot: Spot):
    (parenInner inner around).tell spot = (inner.el around).tell (inner.innerSpot spot) :=
  match inner with
    | Block first rest result =>
      rewrite concatTell [HardLine, (Block first rest result).el around] spot,
          List.appendNil (((Block first rest result).el around).tell Spot.lineStart).said
    | _ => byComputing

--| A prefix operator's gap tells nothing from after a word.
theorem gapTell ∀ (operator: Word) (operand: Expr) (spot: Spot)
    (word: spot.fresh = False):
    (prefixGap operator operand).tell spot = Telling.quiet spot :=
  match spot with
    | { fresh, mid, held } =>
      match fresh, word with
        | True, never => (Bool.trueNotFalse never).impossible
        | False, _ =>
          match operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication) with
            | True | False => byComputing

--| After a word, the printer is never at a line start.
theorem wordTellingFresh ∀ (text: Text) (spot: Spot): (wordTelling text spot).after.fresh = False :=
  match closing text, spot.held with | True | False, True | False => byComputing

theorem leafTellingFresh ∀ (word: Word) (around: Around) (spot: Spot):
    (word.leafTelling around spot).after.fresh = False :=
  match word.trails with
    | True => byComputing
    | False => wordTellingFresh word.text (word.textSpot around spot)

--| What a bracket's inner expression tells, after the opener.
def parenInside (open: Word) (inner: Expr) (around: Around) (spot: Spot): Telling :=
  (inner.el (around.next open.trails 1)).tell (inner.innerSpot (open.leafTelling around spot).after)

--| `( … )` tells its opener, its inner expression and its closer one after another, each where the one before leaves
--| the printer.
--|
--| Proof idea: the concat of the opening (`openingTell`), the inner (`parenInnerTell`) and the closer's leaf
--| (`leafTell`), with the closing document's `quiet` end dropped.
theorem parenTell ∀ (open: Word) (inner: Expr) (close: Word) (around: Around) (spot: Spot)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (opens: isCloserText open.text = False):
    (parenDoc open inner close around).tell spot
      = (open.leafTelling around spot).andThen
        ((parenInside open inner around spot).andThen
          (close.leafTelling (around.next inner.trails (1 + inner.size)) (parenInside open inner around spot).after)) :=
  let closer := close.leafTelling (around.next inner.trails (1 + inner.size)) (parenInside open inner around spot).after
  calc (parenDoc open inner close around).tell spot
    _ = (open.leafTelling around spot).andThen
        ((parenInside open inner around spot).andThen (closer.andThen (Telling.quiet closer.after))) :=
      rewrite concatTell
            [
              open.opening around close,
              parenInner inner (around.next open.trails 1),
              close.leaf (around.next inner.trails (1 + inner.size)) around.at
            ]
            spot,
          openingTell open around close spot openSound opens,
          parenInnerTell inner (around.next open.trails 1) (open.leafTelling around spot).after,
          leafTell close
            (around.next inner.trails (1 + inner.size))
            around.at
            (parenInside open inner around spot).after
            closeSound
    _ = (open.leafTelling around spot).andThen ((parenInside open inner around spot).andThen closer) :=
      rewrite tellingQuietRight closer

-- Prefix operators.

--| What a prefix operator and its operand tell, the operator's own-line comments being the frame's.
def prefixTelling (operator: Word) (operand: Expr) (around: Around) (spot: Spot): Telling :=
  (operator.leafTelling { around | hoisted = True } spot).andThen
    ((operand.el (around.next operator.trails 1)).tell (operator.leafTelling { around | hoisted = True } spot).after)

--| A prefix operator's document tells the operator's leaf, then the operand's element: the gap between them (`- -x`)
--| says nothing.
--|
--| Proof idea: the concat of the operator's leaf (`leafTell`), the gap, which tells nothing after a word (`gapTell`,
--| `leafTellingFresh`), and the operand.
theorem prefixTell ∀ (operator: Word) (operand: Expr) (around: Around) (spot: Spot)
    (sound: operator.sound = True):
    (Doc.concat [
          operator.leaf { around | hoisted = True } around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ]).tell spot
      = prefixTelling operator operand around spot :=
  let leaf := operator.leafTelling { around | hoisted = True } spot
  let operandTelling := (operand.el (around.next operator.trails 1)).tell leaf.after
  calc (Doc.concat
        [
          operator.leaf { around | hoisted = True } around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ]).tell spot
    _ = leaf.andThen
        ((Telling.quiet leaf.after).andThen (operandTelling.andThen (Telling.quiet operandTelling.after))) :=
      rewrite concatTell
            [
              operator.leaf { around | hoisted = True } around.at,
              prefixGap operator operand,
              operand.el (around.next operator.trails 1)
            ]
            spot,
          leafTell operator { around | hoisted = True } around.at spot sound,
          gapTell operator operand leaf.after (leafTellingFresh operator { around | hoisted = True } spot)
    _ = prefixTelling operator operand around spot := rewrite tellingQuietRight operandTelling

-- A leaf at the spots the rules enter it from.

--| A word at a line start starts its line.
theorem wordTellingLine ∀ (text: Text):
    wordTelling text Spot.lineStart = { said = [Said text True False], after = Spot.afterWords } :=
  match closing text with | True | False => byComputing

--| Whether the word's leaf starts a line whatever precedes it: it writes own-line comments or a kept blank line, or a
--| closer takes a line of its own.
def Word.forced (word: Word) (around: Around): Bool := word.leadsLine around || word.ownsLine around

-- Nothing is left to the layout.

--| An entry says exactly what the events are: a blank line, or a word.
def entryExact: Told → Bool
  | Gap | Said _ _ _ => True
  | MaybeGap | Lost => False

--| Every entry says exactly (no `MaybeGap`, no `Lost`).
def toldExact: List Told → Bool
  | [] => True
  | [told, ..rest] => entryExact told && toldExact rest

theorem toldExactAppend ∀ (one other: List Told)
    (first: toldExact one = True)
    (second: toldExact other = True):
    toldExact (one ++ other) = True :=
  match one with
    | [] => second
    | [told, ..rest] => Bool.andIntro (Bool.andLeft first) (toldExactAppend rest other (Bool.andRight first) second)

theorem noteToldExact ∀ (note: Note): toldExact (noteTold note) = True := match note.blankBefore with
  | True | False => byComputing

theorem notesToldExact ∀ (notes: List Note): toldExact (notesTold notes) = True := match notes with
  | [] => byComputing
  | [note, ..rest] => toldExactAppend (noteTold note) (notesTold rest) (noteToldExact note) (notesToldExact rest)

theorem toldAboveExact ∀ (comments: Comments): toldExact comments.toldAbove = True :=
  toldExactAppend
    (notesTold comments.above)
    (if comments.blankBefore then [Gap] else [])
    (notesToldExact comments.above)
    (match comments.blankBefore with
      | True => byComputing
      | False => byComputing)
