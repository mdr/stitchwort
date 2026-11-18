--| Step 2 of tools/fmt/NOTES.md, "Printed spacing" (SW-4076): slice 1's rules print each code word touching the
--| piece before it as `Expr.spacing1` asks, in the triples of `Fmt.TouchSteps`. A sign's operand comes straight after
--| the sign when `prefixGap` is empty, so it touches it; a call's arguments and an infix's right operand come after a
--| `Line` or a space, so they don't.

namespace Fmt.TouchProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (Along, Awaiting, Begun, Seam, isLayout)
import Syntax (Comments, Expr, Note, Word)
import Fmt (..)
import Fmt.GlueProofs (isComment)
import Fmt.OutputStatements (..)
import Fmt.SpellProofs (..)
import Fmt.TouchSteps (..)
import Fmt.JoinProofs (CloserJoins, Joinable, AllJoinable, OpenerJoins, Token, WordJoins)

-- Comments.

theorem commentFilled ∀ (text: Text) (starts: text.startsWith "--" = True): text.isEmpty = False := match text with
  | MkText [first, ..rest] => byComputing

--| An own-line comment's text, from a line start: a word that is no code word.
theorem stepsComment ∀ (text: Text)
    (comment: commentText text = True):
    Steps (Doc.text text) (seam => seam = Begun) [] (seam => seam = Along True) :=
  let starts: isComment text = True := Bool.andLeft comment
  let filled := commentFilled text starts
  let solid := commentNotLayout text comment
  seam trace next holds after =>
    rewrite holds, filled, solid then
      after (Along True) [{ word = text, touching = False }] byComputing (rewrite starts)

theorem stepsBlankList ∀ (blank: Bool) (pre: Seam → Prop): StepsAll (if blank then [Blank] else []) pre [] pre :=
  match blank with
    | True => stepsLast Blank pre pre [] (stepsBlank pre)
    | False => stepsNil pre pre (seam holds => holds)

--| Own-line comments above a token, each ending its line.
--|
--| Proof idea: induction on the notes; each is an optional blank line, its text from a line start, and a line break.
theorem notesAboveSteps ∀ (keep: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    StepsAll (notesAbove keep notes) (seam => seam = Begun) [] (seam => seam = Begun) :=
  match notes with
    | [] => stepsNil _ _ (seam holds => holds)
    | [note, ..rest] =>
      stepsAppend
        (if note.blankBefore && keep then [Blank] else [])
        ([Doc.text note.text, HardLine] ++ notesAbove True rest)
        (seam => seam = Begun)
        (seam => seam = Begun)
        (seam => seam = Begun)
        []
        []
        (stepsBlankList (note.blankBefore && keep) (seam => seam = Begun))
        (stepsCons
          (Doc.text note.text)
          [HardLine, ..notesAbove True rest]
          (seam => seam = Begun)
          (seam => seam = Along True)
          (seam => seam = Begun)
          []
          []
          (stepsComment note.text (Bool.andLeft sound))
          (stepsCons HardLine
            (notesAbove True rest)
            (seam => seam = Along True)
            (seam => seam = Begun)
            (seam => seam = Begun)
            []
            []
            (stepsHard _ _ (seam along => rewrite along) byComputing)
            (notesAboveSteps True rest (Bool.andRight sound))))

theorem laterCloserNotesSteps ∀ (notes: List Note)
    (sound: notesSound notes = True):
    StepsAll (laterCloserNotes notes) (seam => seam = Along True) [] (seam => seam = Along True) :=
  match notes with
    | [] => stepsNil _ _ (seam holds => holds)
    | [note, ..rest] =>
      stepsCons HardLine
        ((if note.blankBefore then [Blank] else []) ++ [Doc.text note.text] ++ laterCloserNotes rest)
        (seam => seam = Along True)
        (seam => seam = Begun)
        (seam => seam = Along True)
        []
        []
        (stepsHard _ _ (seam along => rewrite along) byComputing)
        (stepsAppend
          (if note.blankBefore then [Blank] else [])
          ([Doc.text note.text] ++ laterCloserNotes rest)
          (seam => seam = Begun)
          (seam => seam = Begun)
          (seam => seam = Along True)
          []
          []
          (stepsBlankList note.blankBefore (seam => seam = Begun))
          (stepsCons
            (Doc.text note.text)
            (laterCloserNotes rest)
            (seam => seam = Begun)
            (seam => seam = Along True)
            (seam => seam = Along True)
            []
            []
            (stepsComment note.text (Bool.andLeft sound))
            (laterCloserNotesSteps rest (Bool.andRight sound))))

theorem closerNotesSteps ∀ (note: Note) (rest: List Note)
    (sound: notesSound [note, ..rest] = True):
    StepsAll (closerNotes [note, ..rest]) (seam => seam = Begun) [] (seam => seam = Along True) :=
  stepsCons
    (Doc.text note.text)
    (laterCloserNotes rest)
    (seam => seam = Begun)
    (seam => seam = Along True)
    (seam => seam = Along True)
    []
    []
    (stepsComment note.text (Bool.andLeft sound))
    (laterCloserNotesSteps rest (Bool.andRight sound))

-- A token's own-line comments.

--| Whether a token is printed with nothing before it on its line from where it stands: no own-line comments, no
--| blank line kept, no comment waiting before it.
def Word.quietAt (word: Word) (around: Around) (key: Nat): Bool :=
  !(word.noted || around.before) && (word.leading around key).isEmpty

--| A spacing that a word starting its line, or after a space, meets.
def Loose (first: Spacing): Prop := first.admits False = True

--| A token's own-line comments and kept blank line leave the printer where the token may stand: they end at a line
--| start, which a loose token may follow.
--|
--| Proof idea: cases on whether the token is hoisted, has own-line comments and is a closer; each branch is line
--| breaks around `closerNotes` or `notesAbove`, ending at a line start.
theorem leadingSteps ∀ (word: Word) (around: Around) (key: Nat) (before: Bool) (first: Spacing)
    (sound: word.sound = True)
    (loose: Loose first ∨ word.quietAt around key = True):
    StepsAll (word.leading around key) (Fits before first) [] (Fits before first) :=
  leadingFresh word around key before first sound (filled =>
    match loose with
      | Inl free => free
      | Inr quiet => (Bool.falseNotTrue (rewrite filled at quiet then Bool.andRight quiet)).impossible)

theorem leadingFresh ∀ (word: Word) (around: Around) (key: Nat) (before: Bool) (first: Spacing)
    (sound: word.sound = True)
    (fresh: (word.leading around key).isEmpty = False → Fits before first Begun):
    StepsAll (word.leading around key) (Fits before first) [] (Fits before first) :=
  match word, around.hoisted with
    | { text, comments = { above, after, blankBefore } }, True => stepsNil _ _ (seam holds => holds)
    | { text, comments = { above = [], after, blankBefore } }, False =>
      match around.item && blankBefore, fresh with
        | True, fresh =>
          stepsCons BreakParent
            [LineStart, Blank]
            (Fits before first)
            (Fits before first)
            (Fits before first)
            []
            []
            (stepsBreakParent _)
            (stepsCons LineStart
              [Blank]
              (Fits before first)
              (Fits before first)
              (Fits before first)
              []
              []
              (stepsLineStart _ _ (seam fits => fitsQuiet before first seam fits) (fresh byComputing))
              (stepsLast Blank _ _ [] (stepsBlank _)))
        | False, _ => stepsNil _ _ (seam holds => holds)
    | { text, comments = { above = [note, ..rest], after, blankBefore } }, False =>
      let notes: notesSound [note, ..rest] = True := Bool.andLeft (Bool.andRight sound)
      match isCloserText text with
        | True =>
          let begun := fresh byComputing
          stepsCons BreakParent
            [Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]), CloserLine key]
            (Fits before first)
            (Fits before first)
            (Fits before first)
            []
            []
            (stepsBreakParent _)
            (stepsCons
              (Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]))
              [CloserLine key]
              (Fits before first)
              (seam => seam = Along True)
              (Fits before first)
              []
              []
              (stepsNest 2 _ _ _ _
                (stepsConcat _ _ _ _
                  (stepsCons LineStartHere
                    (closerNotes [note, ..rest])
                    (Fits before first)
                    (seam => seam = Begun)
                    (seam => seam = Along True)
                    []
                    []
                    (stepsLineStartHere _ _ (seam fits => fitsQuiet before first seam fits) byComputing)
                    (closerNotesSteps note rest notes))))
              (stepsLast (CloserLine key) _ _ [] (stepsCloserLine key _ _ (seam along => rewrite along) begun)))
        | False =>
          let begun := fresh byComputing
          stepsAppend
            [BreakParent, LineStart, ..notesAbove around.item [note, ..rest]]
            (if blankBefore then [Blank] else [])
            (Fits before first)
            (seam => seam = Begun)
            (Fits before first)
            []
            []
            (stepsCons BreakParent
              [LineStart, ..notesAbove around.item [note, ..rest]]
              (Fits before first)
              (Fits before first)
              (seam => seam = Begun)
              []
              []
              (stepsBreakParent _)
              (stepsCons LineStart
                (notesAbove around.item [note, ..rest])
                (Fits before first)
                (seam => seam = Begun)
                (seam => seam = Begun)
                []
                []
                (stepsLineStart _ _ (seam fits => fitsQuiet before first seam fits) byComputing)
                (notesAboveSteps around.item [note, ..rest] notes)))
            (allTo _ _ _ _ _ (stepsBlankList blankBefore (seam => seam = Begun)) (seam begun' =>
              rewrite begun' then begun))

-- Tokens.

theorem solidFilled ∀ (text: Text) (solid: isLayout text = False): text.isEmpty = False := match text, solid with
  | MkText [first, ..rest], _ => byComputing

theorem soundSolid ∀ (word: Word) (sound: word.sound = True): isLayout word.text = False :=
  Bool.notTrue (isLayout word.text) (Bool.andLeft sound)

--| A token's text is code: from what `Joinable` says of it.
theorem wordCode ∀ (word: Word) (sound: word.sound = True) (token: Token word.text): Code word.text :=
  let solid := soundSolid word sound
  (solidFilled word.text solid, solid, token)

--| A token's trailing comment, after it on its line.
theorem trailingSteps ∀ (word: Word)
    (sound: word.sound = True):
    StepsAll word.trailing (seam => seam = Along True) [] (Closed word.trails) :=
  match word with
    | { text, comments = { above, after = None, blankBefore } } => stepsNil _ _ (seam along => rewrite along)
    | { text, comments = { above, after = Some comment, blankBefore } } =>
      let commented: commentText comment = True := Bool.andRight (Bool.andRight sound)
      stepsLast
        (LineSuffix comment) _ _
        []
        (stepsSuffix comment (Bool.andLeft commented) (commentNotLayout comment commented))

--| No closer line before a token that is no closer.
theorem ownLineEmpty ∀ (text: Text) (rest: Bool) (key: Nat)
    (closer: isCloserText text = False):
    (if isCloserText text && rest then [CloserLine key] else []) = [] :=
  rewrite closer

theorem pieceText ∀ (text: Text)
    (closer: isCloserText text = False)
    (comma: (text == ",") = False):
    piece text = Doc.text text :=
  rewrite closer, comma

--| A token that is no closer: from where it may stand, spaced `first`, the printer then stands after it, or after its
--| trailing comment.
theorem wordLeafSteps ∀ (word: Word) (around: Around) (key: Nat) (first: Spacing)
    (joins: WordJoins word)
    (loose: Loose first ∨ word.quietAt around key = True):
    Steps (word.leaf around key) (Fits around.before first) [first] (Closed word.trails) :=
  let (sound, token, comma, closer) := joins
  stepsConcat _ _ _ _
    (rewrite ownLineEmpty word.text (!word.noted && around.before && word.trails) key closer,
        pieceText word.text closer comma then
      stepsAppend
        (word.leading around key)
        ([] ++ [Doc.text word.text] ++ word.trailing)
        (Fits around.before first)
        (Fits around.before first)
        (Closed word.trails)
        []
        [first]
        (leadingSteps word around key around.before first sound loose)
        (stepsCons
          (Doc.text word.text)
          word.trailing
          (Fits around.before first)
          (seam => seam = Along True)
          (Closed word.trails)
          [first]
          []
          (stepsChunk word.text word.text.length around.before first (wordCode word sound token))
          (trailingSteps word sound)))

--| An opening bracket, as a token that is no closer, with a `Mark` before it.
theorem openingSteps ∀ (word: Word) (around: Around) (closer: Word) (first: Spacing)
    (joins: WordJoins word)
    (loose: Loose first ∨ word.quietAt around around.at = True):
    Steps (word.opening around closer) (Fits around.before first) [first] (Closed word.trails) :=
  let (sound, token, comma, notCloser) := joins
  let marked := closer.noted || closer.trails
  stepsConcat _ _ _ _
    (rewrite pieceText word.text notCloser comma then
      stepsAppend
        (word.leading around around.at)
        ((if marked then [Mark around.at] else []) ++ [Doc.text word.text] ++ word.trailing)
        (Fits around.before first)
        (Fits around.before first)
        (Closed word.trails)
        []
        [first]
        (leadingSteps word around around.at around.before first sound loose)
        (stepsAppend
          (if marked then [Mark around.at] else [])
          ([Doc.text word.text] ++ word.trailing)
          (Fits around.before first)
          (Fits around.before first)
          (Closed word.trails)
          []
          [first]
          (markSteps marked around.at (Fits around.before first))
          (stepsCons
            (Doc.text word.text)
            word.trailing
            (Fits around.before first)
            (seam => seam = Along True)
            (Closed word.trails)
            [first]
            []
            (stepsChunk word.text word.text.length around.before first (wordCode word sound token))
            (trailingSteps word sound))))

theorem markSteps ∀ (marked: Bool) (key: Nat) (pre: Seam → Prop):
    StepsAll (if marked then [Mark key] else []) pre [] pre :=
  match marked with
    | True => stepsLast (Mark key) pre pre [] (stepsMark key pre)
    | False => stepsNil pre pre (seam holds => holds)
