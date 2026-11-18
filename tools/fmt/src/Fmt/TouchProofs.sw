--| Step 2 of tools/fmt/NOTES.md, "Printed spacing" (SW-4076): slice 1's rules print each code word touching the
--| piece before it as `Expr.spacing1` asks, in the triples of `Fmt.TouchSteps`. A sign's operand comes straight after
--| the sign when `prefixGap` is empty, so it touches it; a call's arguments and an infix's right operand come after a
--| `Line` or a space, so they don't.

namespace Fmt.TouchProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (Along, Awaiting, Begun, Seam, SepsTouch, Touch, TouchesAll, isLayout, touchesWeaker)
import Syntax (Comments, Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.GlueProofs (codeTouching, codeTouchingAppend, isComment)
import Fmt.OutputStatements (..)
import Fmt.SpellProofs (..)
import Fmt.TouchSteps (..)
import Fmt.JoinProofs (leadJoins)
import Fmt.JoinProofs (
  beforeCloseIs,
  bracketTrails,
  openTrails,
  seenAppend,
  AllJoinable,
  CloserJoins,
  Joinable,
  OpenerJoins,
  Token,
  WordJoins,
  closeTrails,
  trailsBackAppend
)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.CalmProofs (bracketFrom, bracketIs)

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
    (loose: Loose first ∨ (word.leading around key).isEmpty = True):
    StepsAll (word.leading around key) (Fits before first) [] (Fits before first) :=
  leadingFresh word around key before first sound (filled =>
    match loose with
      | Inl free => free
      | Inr empty => (Bool.falseNotTrue (rewrite filled at empty then empty)).impossible)

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
    (loose: Loose first ∨ (word.leading around key).isEmpty = True):
    Steps (word.leaf around key) (Fits True first) [first] (Closed word.trails) :=
  let (sound, token, comma, closer) := joins
  stepsConcat _ _ _ _
    (rewrite ownLineEmpty word.text (!word.noted && around.before && word.trails) key closer,
        pieceText word.text closer comma then
      stepsAppend
        (word.leading around key)
        ([] ++ [Doc.text word.text] ++ word.trailing)
        (Fits True first)
        (Fits True first)
        (Closed word.trails)
        []
        [first]
        (leadingSteps word around key True first sound loose)
        (stepsCons
          (Doc.text word.text)
          word.trailing
          (Fits True first)
          (seam => seam = Along True)
          (Closed word.trails)
          [first]
          []
          (stepsChunk word.text word.text.length True first (wordCode word sound token))
          (trailingSteps word sound)))

--| An opening bracket, as a token that is no closer, with a `Mark` before it.
theorem openingSteps ∀ (word: Word) (around: Around) (closer: Word) (first: Spacing)
    (joins: WordJoins word)
    (loose: Loose first ∨ (word.leading around around.at).isEmpty = True):
    Steps (word.opening around closer) (Fits True first) [first] (Closed word.trails) :=
  let (sound, token, comma, notCloser) := joins
  let marked := closer.noted || closer.trails
  stepsConcat _ _ _ _
    (rewrite pieceText word.text notCloser comma then
      stepsAppend
        (word.leading around around.at)
        ((if marked then [Mark around.at] else []) ++ [Doc.text word.text] ++ word.trailing)
        (Fits True first)
        (Fits True first)
        (Closed word.trails)
        []
        [first]
        (leadingSteps word around around.at True first sound loose)
        (stepsAppend
          (if marked then [Mark around.at] else [])
          ([Doc.text word.text] ++ word.trailing)
          (Fits True first)
          (Fits True first)
          (Closed word.trails)
          []
          [first]
          (markSteps marked around.at (Fits True first))
          (stepsCons
            (Doc.text word.text)
            word.trailing
            (Fits True first)
            (seam => seam = Along True)
            (Closed word.trails)
            [first]
            []
            (stepsChunk word.text word.text.length True first (wordCode word sound token))
            (trailingSteps word sound))))

theorem markSteps ∀ (marked: Bool) (key: Nat) (pre: Seam → Prop):
    StepsAll (if marked then [Mark key] else []) pre [] pre :=
  match marked with
    | True => stepsLast (Mark key) pre pre [] (stepsMark key pre)
    | False => stepsNil pre pre (seam holds => holds)

-- Closers.

theorem closerCode ∀ (text: Text) (closer: isCloserText text = True): Code text := match paren: text == ")" with
  | True => rewrite DecEq.sound paren then (byComputing, byComputing, byComputing)
  | False =>
    match square: text == "]" with
      | True => rewrite DecEq.sound square then (byComputing, byComputing, byComputing)
      | False =>
        match brace: text == "}" with
          | True => rewrite DecEq.sound brace then (byComputing, byComputing, byComputing)

theorem pieceCloser ∀ (text: Text) (closer: isCloserText text = True): piece text = Closing text := rewrite closer

theorem closedWeaker ∀ (held held': Bool)
    (implies: held = True → held' = True) (seam: Seam)
    (closed: Closed held seam):
    Closed held' seam :=
  match seam, closed with
    | Along word, touched => touched
    | Awaiting word comment, (waits, quiet) => (implies waits, quiet)

--| A closer's own-line comments end at a line start, where no comment waits.
theorem closerLeadingSteps ∀ (word: Word) (around: Around) (key: Nat) (before: Bool)
    (sound: word.sound = True)
    (closer: isCloserText word.text = True)
    (unhoisted: around.hoisted = False):
    StepsAll (word.leading around key) (Fits before Free) [] (Fits (if word.noted then False else before) Free) :=
  match word, around.hoisted with
    | { text, comments = { above = [], after, blankBefore } }, False =>
      match around.item && blankBefore with
        | True =>
          stepsCons BreakParent
            [LineStart, Blank]
            (Fits before Free)
            (Fits before Free)
            (Fits before Free)
            []
            []
            (stepsBreakParent _)
            (stepsCons LineStart
              [Blank]
              (Fits before Free)
              (Fits before Free)
              (Fits before Free)
              []
              []
              (stepsLineStart _ _ (seam fits => fitsQuiet before Free seam fits) byComputing)
              (stepsLast Blank _ _ [] (stepsBlank _)))
        | False => stepsNil _ _ (seam holds => holds)
    | { text, comments = { above = [note, ..rest], after, blankBefore } }, False =>
      let notes: notesSound [note, ..rest] = True := Bool.andLeft (Bool.andRight sound)
      rewrite closer then
        stepsCons BreakParent
          [Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]), CloserLine key]
          (Fits before Free)
          (Fits before Free)
          (Fits False Free)
          []
          []
          (stepsBreakParent _)
          (stepsCons
            (Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]))
            [CloserLine key]
            (Fits before Free)
            (seam => seam = Along True)
            (Fits False Free)
            []
            []
            (stepsNest 2 _ _ _ _
              (stepsConcat _ _ _ _
                (stepsCons LineStartHere
                  (closerNotes [note, ..rest])
                  (Fits before Free)
                  (seam => seam = Begun)
                  (seam => seam = Along True)
                  []
                  []
                  (stepsLineStartHere _ _ (seam fits => fitsQuiet before Free seam fits) byComputing)
                  (closerNotesSteps note rest notes))))
            (stepsLast (CloserLine key) _ _ [] (stepsCloserLine key _ _ (seam along => rewrite along) byComputing)))

--| A closer line, where the closer takes a line of its own: after it no comment waits.
theorem ownSteps ∀ (own: Bool) (key: Nat) (held: Bool):
    StepsAll (if own then [CloserLine key] else []) (Fits held Free) [] (Fits (if own then False else held) Free) :=
  match own with
    | True =>
      stepsLast
        (CloserLine key) _ _
        []
        (stepsCloserLine key _ _ (seam fits => fitsQuiet held Free seam fits) byComputing)
    | False => stepsNil _ _ (seam holds => holds)

--| A closer and its trailing comment, from where a comment waits only if `held`; a trailing comment only where none
--| waits.
theorem closingTail ∀ (word: Word) (held ends: Bool)
    (sound: word.sound = True)
    (code: Code word.text)
    (clear: word.trails = True → held = False)
    (weaker: held = True → ends = True)
    (own: word.trails = True → ends = True):
    StepsAll ([Closing word.text] ++ word.trailing) (Fits held Free) [Free] (Closed ends) :=
  match word, code, clear, own with
    | { text, comments = { above, after = None, blankBefore } }, code, _, _ =>
      stepsLast
        (Closing text) _ _
        [Free]
        (stepsTo _ _ _ _ _ (stepsClosing text held code) (seam closed => closedWeaker held ends weaker seam closed))
    | { text, comments = { above, after = Some comment, blankBefore } }, code, clear, own =>
      let cleared: held = False := clear byComputing
      let commented: commentText comment = True := Bool.andRight (Bool.andRight sound)
      stepsCons
        (Closing text)
        [LineSuffix comment]
        (Fits held Free)
        (seam => seam = Along True)
        (Closed ends)
        [Free]
        []
        (stepsTo _ _ _ _ _ (stepsClosing text held code) (seam closed =>
          closedAlong seam (rewrite cleared at closed then closed)))
        (stepsLast
          (LineSuffix comment) _ _
          []
          (stepsTo _ _ _ _ _
            (stepsSuffix comment (Bool.andLeft commented) (commentNotLayout comment commented))
            (seam closed => closedWeaker True ends (_ => own byComputing) seam closed)))

--| Where a closer with a trailing comment comes, nothing waits: a comment before it either gives it a line of its own
--| or its own-line comments end at a line start.
theorem ownClear ∀ (noted before: Bool):
    (if (True && !noted && before && True) then False
     else if noted then False
     else before)
      = False :=
  match noted, before with
    | True, _ => byComputing
    | False, True => byComputing
    | False, False => byComputing

theorem ownWeaker ∀ (noted before trails: Bool)
    (held: (if (True && !noted && before && trails) then False
            else if noted then False
            else before)
      = True):
    (trails || before) = True :=
  match noted, before, trails, held with
    | False, True, False, _ => byComputing
    | False, True, True, never => (Bool.falseNotTrue never).impossible
    | True, _, _, never => (Bool.falseNotTrue never).impossible
    | False, False, _, never => (Bool.falseNotTrue never).impossible

--| A closer, from where it may stand: then the printer stands after it, or a comment waits, its own or one from
--| before it.
--|
--| Proof idea: its own-line comments end at a line start (`closerLeadingSteps`), as does a line of its own
--| (`ownSteps`); with a trailing comment of its own one of the two comes before it whenever a comment waited
--| (`ownClear`), so it stands on its line before its comment (`closingTail`).
theorem closerLeafSteps ∀ (word: Word) (around: Around) (key: Nat)
    (joins: CloserJoins word)
    (unhoisted: around.hoisted = False):
    Steps (word.leaf around key) (Fits around.before Free) [Free] (Closed (word.trails || around.before)) :=
  let (sound, closer) := joins
  let own := isCloserText word.text && !word.noted && around.before && word.trails
  let lead := if word.noted then False else around.before
  let held := if own then False else lead
  let clear: word.trails = True → held = False := trails =>
    rewrite closer, trails then ownClear word.noted around.before
  let weaker: held = True → (word.trails || around.before) = True := holds =>
    ownWeaker word.noted around.before word.trails (rewrite closer at holds then holds)
  let own': word.trails = True → (word.trails || around.before) = True := trails => rewrite trails
  stepsConcat _ _ _ _
    (rewrite pieceCloser word.text closer then
      stepsAppend
        (word.leading around key)
        ((if own then [CloserLine key] else []) ++ [Closing word.text] ++ word.trailing)
        (Fits around.before Free)
        (Fits lead Free)
        (Closed (word.trails || around.before))
        []
        [Free]
        (closerLeadingSteps word around key around.before sound closer unhoisted)
        (stepsAppend
          (if own then [CloserLine key] else [])
          ([Closing word.text] ++ word.trailing)
          (Fits lead Free)
          (Fits held Free)
          (Closed (word.trails || around.before))
          []
          [Free]
          (ownSteps own key lead)
          (closingTail word held (word.trails || around.before) sound (closerCode word.text closer) clear weaker own')))

-- Elements.

--| A displaced element, where a comment comes before it; else the element as it is.
theorem placedSteps ∀ (displaced: Bool) (doc: Doc) (first: Spacing) (spacing: List Spacing) (post: Seam → Prop)
    (inner: Steps doc (Fits True first) spacing post)
    (fresh: displaced = True → Loose first):
    Steps (if displaced then Displaced doc else doc) (Fits True first) spacing post :=
  match displaced, fresh with
    | True, fresh => stepsDisplaced doc _ _ _ inner (fresh byComputing) (seam fits => fitsQuiet True first seam fits)
    | False, _ => inner

--| A node's document after its first token's own-line comments.
theorem framedSteps ∀ (first: Word) (around: Around) (doc: Doc) (spacing: List Spacing)
    (post: Seam → Prop) (start: Spacing)
    (sound: first.sound = True)
    (loose: Loose start ∨ first.quietAt around around.at = True)
    (inner: Steps doc (Fits True start) spacing post):
    Steps (framedBy first around doc) (Fits True start) spacing post :=
  let leadLoose: Loose start ∨ (first.leading around around.at).isEmpty = True := match loose with
    | Inl free => Inl free
    | Inr quiet => Inr (Bool.andRight quiet)
  let fresh: (first.noted || around.before) = True → Loose start := shown =>
    match loose with
      | Inl free => free
      | Inr quiet => (Bool.falseNotTrue (rewrite shown at quiet then quiet)).impossible
  stepsConcat _ _ _ _
    (stepsTwo
      (Doc.concat (first.leading around around.at))
      (if first.noted || around.before then Displaced doc else doc)
      (Fits True start)
      (Fits True start)
      post
      []
      spacing
      (stepsConcat _ _ _ _ (leadingSteps first around around.at True start sound leadLoose))
      (placedSteps (first.noted || around.before) doc start spacing post inner fresh))

--| An expression of the slice spaces its first code word as `Free`.
--|
--| Proof idea: induction on the expression; a sign that is no argument is free, and every other node starts with its
--| first part's spacing or a bracket.
theorem spacingFree ∀ (expr: Expr)
    (within: expr.within1 = True):
    ∃ (rest: List Spacing) => expr.spacing1 False = [Free, ..rest] :=
  match expr with
    | Atom kind word => ([], byComputing)
    | Paren open inner close => (inner.spacing1 False ++ [Free], byComputing)
    | Tuple open items comma close => (commaSpacing1 items ++ [Free], byComputing)
    | ListOf open items comma close => (commaSpacing1 items ++ [Free], byComputing)
    | App head arguments =>
      let (rest, head) := spacingFree head (Bool.andLeft within)
      (rest ++ argumentsSpacing1 arguments, rewrite head)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (rest, left) := spacingFree left (Bool.andLeft within)
          (rest ++ [Free, ..spacedFirst Apart (right.spacing1 False)], rewrite left)
        | InfixArrow =>
          let (rest, left) := spacingFree left (Bool.andLeft within)
          (rest ++ [Free, ..spacedFirst Apart (right.spacing1 False)], rewrite left)
        | _ => cases
    | Prefix operator operand =>
      match operandSpacing False operator operand with
        | Some spacing => (spacedFirst spacing (operand.spacing1 False), byComputing)
        | None => (operand.spacing1 False, byComputing)

--| Spacing an expression's first code word as `Free` leaves its spacing as it is.
theorem freeFirst ∀ (expr: Expr)
    (within: expr.within1 = True):
    spacedFirst Free (expr.spacing1 False) = expr.spacing1 False :=
  let (rest, free) := spacingFree expr within
  rewrite free

--| What the rules' lemmas say of an expression: its element, from where its first code word may stand spaced `first`,
--| adds code words spaced as `Expr.spacing1` says with `first` for the first, and ends where a comment waits only if
--| it ends with one. `argument`: it is a call's argument, as `argument1` shapes them.
def ElSteps (expr: Expr): Prop :=
  expr.within1 = True
    → expr.shaped1 = True
    → expr.lexical1 = True
    → Joinable lexKind expr
    → ∀ (around: Around) (first: Spacing) (argument: Bool) => (argument = True → expr.argument1 = True)
      → (Loose first ∨ expr.firstWord.quietAt around around.at = True)
      → Steps (expr.el around) (Fits True first) (spacedFirst first (expr.spacing1 argument)) (Ends expr.trails)

--| An element that is no call's argument, its first code word free.
theorem elFree ∀ (expr: Expr) (around: Around)
    (steps: ElSteps expr)
    (within: expr.within1 = True)
    (shaped: expr.shaped1 = True)
    (lexical: expr.lexical1 = True)
    (joinable: Joinable lexKind expr):
    Steps (expr.el around) (Fits True Free) (expr.spacing1 False) (Ends expr.trails) :=
  rewrite <- freeFirst expr within then
    steps within shaped lexical joinable around Free False
      (never => (Bool.falseNotTrue never).impossible)
      (Inl byComputing)

--| A name or numeral.
theorem atomSteps ∀ (kind: Tok) (word: Word) (around: Around) (first: Spacing) (argument: Bool)
    (joins: WordJoins word)
    (loose: Loose first ∨ word.quietAt around around.at = True):
    Steps
      ((Atom kind word).el around)
      (Fits True first)
      (spacedFirst first ((Atom kind word).spacing1 argument))
      (Ends (Atom kind word).trails) :=
  let (_, _, _, closer) := joins
  let leadLoose: Loose first ∨ (word.leading around around.at).isEmpty = True := match loose with
    | Inl free => Inl free
    | Inr quiet => Inr (Bool.andRight quiet)
  stepsTo _ _ _ _ _ (wordLeafSteps word around around.at first joins leadLoose) (seam closed =>
    endsWeaker word.trails (Atom kind word).trails (trails => rewrite trails) seam (closedEnds word.trails seam closed))

-- Signs.

--| No name or numeral is spelled `-`.
theorem atomNotMinus ∀ (kind: Tok) (word: Word) (within: (Atom kind word).within1 = True): (word.text == "-") = False :=
  match minus: word.text == "-" with
    | False => byComputing
    | True =>
      let spells: textSpells1 kind word.text = True := Bool.andRight within
      let wordKind: kind.wordWithin1 = True := Bool.andLeft within
      let bad: textSpells1 kind "-" = True := rewrite DecEq.sound minus at spells then spells
      match kind, wordKind, bad with
        | Float, _, never => (Bool.falseNotTrue never).impossible

--| An atom or bracket starts with no `-` and is no numeral's call: `prefixGap` writes nothing before it.
theorem atomicTight ∀ (operand: Expr)
    (atomic: operand.atomic1 = True)
    (within: operand.within1 = True)
    (lexical: operand.lexical1 = True):
    (operand.firstWord.text == "-" || operand.numeralApplication) = False :=
  match operand with
    | Atom kind word => rewrite atomNotMinus kind word within
    | Paren open inner close => rewrite DecEq.sound (Bool.andLeft lexical)
    | Tuple open items comma close => rewrite DecEq.sound (Bool.andLeft lexical)
    | ListOf open items comma close => rewrite DecEq.sound (Bool.andLeft lexical)

theorem numeralAtomic ∀ (operand: Expr) (numeral: operand.numeral1 = True): operand.atomic1 = True := match operand with
  | Atom kind word => byComputing

theorem gapSpaced ∀ (operator: Word) (operand: Expr)
    (spaced: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = True):
    prefixGap operator operand = Doc.text " " :=
  rewrite spaced

theorem gapTight ∀ (operator: Word) (operand: Expr)
    (tight: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = False):
    prefixGap operator operand = Nothing :=
  rewrite tight

--| Whatever a sign writes before its operand, the operand may start there free.
theorem gapFree ∀ (operator: Word) (operand: Expr) (trails: Bool):
    Steps (prefixGap operator operand) (Closed trails) [] (Fits True Free) :=
  match spaced: operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication) with
    | True =>
      stepsFrom _ _ _ _ _
        (stepsTo _ _ _ _ _ (stepsSpace trails) (seam gapped =>
          fitsWeaker trails True (_ => byComputing) Free seam (gappedFits trails Free seam byComputing gapped)))
        (seam closed => closedEnds trails seam closed)
    | False => stepsTo _ _ _ _ _ (stepsNothing (Closed trails)) (seam closed =>
      fitsWeaker trails True (_ => byComputing) Free seam (endsFits trails seam (closedEnds trails seam closed)))

--| `-` and a numeral's call, a space between them.
theorem gapApart ∀ (operator: Word) (operand: Expr) (trails: Bool)
    (spaced: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = True):
    Steps (prefixGap operator operand) (Closed trails) [] (Fits True Apart) :=
  rewrite gapSpaced operator operand spaced then
    stepsFrom _ _ _ _ _
      (stepsTo _ _ _ _ _ (stepsSpace trails) (seam gapped =>
        fitsWeaker trails True (_ => byComputing) Apart seam (gappedFits trails Apart seam byComputing gapped)))
      (seam closed => closedEnds trails seam closed)

--| A sign with no trailing comment and nothing written after it: its operand stands glued to it.
theorem gapGlued ∀ (operator: Word) (operand: Expr)
    (tight: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = False):
    Steps (prefixGap operator operand) (Closed False) [] (Fits True Glued) :=
  rewrite gapTight operator operand tight then
    stepsTo _ _ _ _ _ (stepsNothing (Closed False)) (seam closed => rewrite closedAlong seam closed)

theorem signQuietAfter ∀ (operator: Word) (operand: Expr)
    (quiet: signQuiet operator operand = True):
    operator.trails = False :=
  match after: operator.comments.after with | None => byComputing

theorem signQuietAbove ∀ (operator: Word) (operand: Expr)
    (quiet: signQuiet operator operand = True):
    operand.lead.comments.above = [] :=
  match after: operator.comments.after with
    | None =>
      match above: operand.lead.comments.above with
        | [] => byComputing

--| A token with no own-line comment, after no trailing comment, outside a list's items: nothing comes before it.
theorem quietFresh ∀ (word: Word) (around: Around) (key: Nat)
    (above: word.comments.above = [])
    (before: around.before = False)
    (hoisted: around.hoisted = False)
    (item: around.item = False):
    word.quietAt around key = True :=
  match word, above with | { text, comments = { above = [], after, blankBefore } }, _ => rewrite before, hoisted, item

theorem closedFalse ∀ (trails: Bool)
    (none: trails = False) (seam: Seam)
    (closed: Closed trails seam):
    Closed False seam :=
  closedWeaker trails False (shown => (Bool.trueNotFalse (rewrite shown at none then none)).impossible) seam closed

--| A sign and its operand, from where the sign may stand spaced `first`.
--|
--| Proof idea: the sign is a token (`wordLeafSteps`); its operand starts where `operandSpacing` says: apart after the
--| space `prefixGap` writes before a numeral's call, glued where nothing comes between them (no comment, by
--| `signQuiet`, and no space: a call's argument's sign is on an atom or bracket, by `argument1`), else free.
theorem prefixSteps ∀ (operator: Word) (operand: Expr) (around: Around) (first: Spacing) (argument: Bool)
    (within: (Prefix operator operand).within1 = True)
    (shaped: (Prefix operator operand).shaped1 = True)
    (lexical: (Prefix operator operand).lexical1 = True)
    (joinable: Joinable lexKind (Prefix operator operand))
    (isArgument: argument = True → (Prefix operator operand).argument1 = True)
    (loose: Loose first ∨ operator.quietAt around around.at = True)
    (operandSteps: ElSteps operand):
    Steps
      ((Prefix operator operand).el around)
      (Fits True first)
      (spacedFirst first ((Prefix operator operand).spacing1 argument))
      (Ends (Prefix operator operand).trails) :=
  let (joins, operandJoins, _) := joinable
  let (sound, _, _, _) := joins
  let operandWithin: operand.within1 = True := Bool.andLeft within
  let operandShaped: operand.shaped1 = True := Bool.andLeft shaped
  let operandLexical: operand.lexical1 = True := Bool.andRight lexical
  let place := around.next operator.trails 1
  let inside := { around | hoisted = True }
  let ends: ∀ (seam: Seam) => Ends operand.trails seam → Ends (Prefix operator operand).trails seam := seam ended =>
    endsWeaker operand.trails
      (Prefix operator operand).trails
      (trails =>
        rewrite List.reverseCons operator operand.words then trailsBackAppend operand.words.reverse [operator] trails)
      seam
      ended
  let leaf := wordLeafSteps operator inside around.at first joins (Inr byComputing)
  let whole: ∀ (rest: List Spacing) (middle: Seam → Prop) (gap: Steps
    (prefixGap operator operand)
    (Closed operator.trails)
    []
    middle) (inner: Steps (operand.el place) middle rest (Ends operand.trails)) => Steps
    ((Prefix operator operand).el around)
    (Fits True first)
    [first, ..rest]
    (Ends (Prefix operator operand).trails) :=
    rest middle gap inner =>
      framedSteps operator around _
        [first, ..rest] _
        first
        sound
        loose
        (stepsConcat _ _ _ _
          (stepsCons
            (operator.leaf inside around.at)
            [prefixGap operator operand, operand.el place]
            (Fits True first)
            (Closed operator.trails)
            (Ends (Prefix operator operand).trails)
            [first]
            rest
            leaf
            (stepsTwo
              (prefixGap operator operand)
              (operand.el place) _
              middle _
              []
              rest
              gap
              (stepsTo _ _ _ _ _ inner ends))))
  let free: Steps (operand.el place) (Fits True Free) (operand.spacing1 False) (Ends operand.trails) :=
    elFree operand place operandSteps operandWithin operandShaped operandLexical operandJoins
  let glued: signQuiet operator operand = True
    → Steps (operand.el place) (Fits True Glued) (spacedFirst Glued (operand.spacing1 False)) (Ends operand.trails) :=
    quiet =>
      let noTrail := signQuietAfter operator operand quiet
      let fresh: operand.firstWord.quietAt place place.at = True :=
        rewrite firstWordLead operand operandWithin then
          quietFresh operand.lead place place.at
            (signQuietAbove operator operand quiet)
            (rewrite noTrail)
            byComputing
            byComputing
      operandSteps operandWithin operandShaped operandLexical operandJoins place Glued False
        (never => (Bool.falseNotTrue never).impossible)
        (Inr fresh)
  let gluedWhole: signQuiet operator operand = True
    → (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = False
    → Steps
      ((Prefix operator operand).el around)
      (Fits True first)
      [first, ..spacedFirst Glued (operand.spacing1 False)]
      (Ends (Prefix operator operand).trails) :=
    quiet tight =>
      whole _ _
        (stepsFrom _ _ _ _ _ (gapGlued operator operand tight) (seam closed =>
          closedFalse operator.trails (signQuietAfter operator operand quiet) seam closed))
        (glued quiet)
  match app: operator.text == "-" && operand.numeralApplication with
    | True =>
      let spaced: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = True :=
        Bool.andIntro (Bool.andLeft app) (Bool.orRight (Bool.andRight app))
      stepsSpacing _ _ _ _ _ byComputing
        (whole _ _
          (gapApart operator operand operator.trails spaced)
          (operandSteps operandWithin operandShaped operandLexical operandJoins place Apart False
            (never => (Bool.falseNotTrue never).impossible)
            (Inl byComputing)))
    | False =>
      match quiet: signQuiet operator operand with
        | False => stepsSpacing _ _ _ _ _ byComputing (whole _ _ (gapFree operator operand operator.trails) free)
        | True =>
          match argument with
            | True =>
              let atomic: operand.atomic1 = True := isArgument byComputing
              let tight: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication))
                = False :=
                Bool.andFalseRight _ _ (atomicTight operand atomic operandWithin operandLexical)
              stepsSpacing _ _ _ _ _ byComputing (gluedWhole quiet tight)
            | False =>
              match numeral: operator.text == "-" && operand.numeral1 with
                | True =>
                  let atomic := numeralAtomic operand (Bool.andRight numeral)
                  let tight: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication))
                    = False :=
                    Bool.andFalseRight _ _ (atomicTight operand atomic operandWithin operandLexical)
                  stepsSpacing _ _ _ _ _ byComputing (gluedWhole quiet tight)
                | False =>
                  stepsSpacing _ _ _ _ _ byComputing (whole _ _ (gapFree operator operand operator.trails) free)

-- Brackets.

theorem parenInnerSteps ∀ (inner: Expr) (place: Around) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop)
    (within: inner.within1 = True)
    (steps: Steps (inner.el place) pre spacing post):
    Steps (parenInner inner place) pre spacing post :=
  match inner with
    | Block _ _ _ => cases
    | If _ _ _ _ _ _ _ => cases
    | _ => steps

theorem closedFree ∀ (trails: Bool) (seam: Seam) (closed: Closed trails seam): Fits True Free seam :=
  fitsWeaker trails True (_ => byComputing) Free seam (endsFits trails seam (closedEnds trails seam closed))

--| A closer ending a bracket around `middle`: the bracket ends with a comment where the closer, or the code before
--| it, does.
theorem closerEnds ∀ (open close: Word) (middle: List Word) (seam: Seam)
    (closer: isCloserText close.text = True)
    (closed: Closed (close.trails || trailsBack middle.reverse) seam):
    Ends (trailsBack ([open, ..middle] ++ [close]).reverse) seam :=
  endsWeaker
    (close.trails || trailsBack middle.reverse)
    (trailsBack ([open, ..middle] ++ [close]).reverse)
    (trails => closeTrails open close middle closer (rewrite closer then trails))
    seam
    (closedEnds (close.trails || trailsBack middle.reverse) seam closed)

--| `( … )`: the opener, spaced `first`, the element inside, free, and the closer.
theorem parenSteps ∀ (open: Word) (inner: Expr) (close: Word) (around: Around) (first: Spacing) (argument: Bool)
    (within: (Paren open inner close).within1 = True)
    (shaped: (Paren open inner close).shaped1 = True)
    (lexical: (Paren open inner close).lexical1 = True)
    (joinable: Joinable lexKind (Paren open inner close))
    (loose: Loose first ∨ open.quietAt around around.at = True)
    (innerSteps: ElSteps inner):
    Steps
      ((Paren open inner close).el around)
      (Fits True first)
      (spacedFirst first ((Paren open inner close).spacing1 argument))
      (Ends (Paren open inner close).trails) :=
  let (opener, closer, innerJoins) := joinable
  let (closeSound, isCloser) := closer
  let inside := { around | hoisted = True }
  let innerAround := inside.next open.trails 1
  let closeAround := inside.next inner.trails (1 + inner.size)
  framedSteps open around _
    [first, ..inner.spacing1 False ++ [Free]] _
    first
    opener.left.left
    loose
    (stepsConcat _ _ _ _
      (stepsCons
        (open.opening inside close)
        [parenInner inner innerAround, close.leaf closeAround inside.at]
        (Fits True first)
        (Closed open.trails)
        (Ends (Paren open inner close).trails)
        [first]
        (inner.spacing1 False ++ [Free])
        (openingSteps open inside close first opener.left (Inr byComputing))
        (stepsTwo
          (parenInner inner innerAround)
          (close.leaf closeAround inside.at)
          (Closed open.trails)
          (Ends inner.trails)
          (Ends (Paren open inner close).trails)
          (inner.spacing1 False)
          [Free]
          (stepsFrom _ _ _ _ _
            (parenInnerSteps inner innerAround _ _ _ within
              (elFree inner innerAround innerSteps within shaped (Bool.andRight (Bool.andRight lexical)) innerJoins))
            (seam closed => closedFree open.trails seam closed))
          (stepsFrom _ _ _ _ _
            (stepsTo _ _ _ _ _ (closerLeafSteps close closeAround inside.at closer byComputing) (seam closed =>
              closerEnds open close inner.words seam isCloser closed))
            (seam ended => endsFits inner.trails seam ended)))))

-- Open goals: the other nodes of the slice.

--| Each item's element meets `ElSteps`.
def EachElSteps: List Expr → Prop
  | [] => True
  | [item, ..rest] => ElSteps item ∧ EachElSteps rest

-- Comma brackets.

--| Each item's element, wherever it stands, from where it may start free.
def EachFree: List Expr → Prop
  | [] => True
  | [item, ..rest] =>
    (∀ (place: Around) => Steps (item.el place) (Fits True Free) (item.spacing1 False) (Ends item.trails))
      ∧ EachFree rest

theorem eachFree ∀ (items: List Expr)
    (each: EachElSteps items)
    (within: allWithin1 items = True)
    (shaped: allShaped1 items = True)
    (lexical: allLexical1 items = True)
    (joinable: AllJoinable lexKind items):
    EachFree items :=
  match items, each, joinable with
    | [], _, _ => byComputing
    | [item, ..rest], (steps, others), (joins, restJoins) => (
      place => elFree item place steps (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft lexical) joins,
      eachFree rest others (Bool.andRight within) (Bool.andRight shaped) (Bool.andRight lexical) restJoins
    )

--| A comma after an item: it stands on the item's line, before a comment the item ends with.
theorem commaStep ∀ (trails: Bool): Steps (Closing ",") (Ends trails) [Free] (Ends trails) :=
  stepsFrom _ _ _ _ _
    (stepsTo _ _ _ _ _ (stepsClosing "," trails (byComputing, byComputing, byComputing)) (seam closed =>
      closedEnds trails seam closed))
    (seam ended => endsFits trails seam ended)

--| A line break or space between items: the next starts free.
theorem sepFree ∀ (first trails: Bool): Steps (if first then SoftLine else Line) (Ends trails) [] (Fits True Free) :=
  match first with
    | True =>
      stepsSoft _ _
        (seam ended => endsQuiet trails seam ended)
        (seam ended => fitsWeaker trails True (_ => byComputing) Free seam (endsFits trails seam ended))
        byComputing
    | False => stepsTo _ _ _ _ _ (stepsLine trails) (seam gapped =>
      fitsWeaker trails True (_ => byComputing) Free seam (gappedFits trails Free seam byComputing gapped))

theorem itemEnds ∀ (seen: List Word) (item: Expr) (seam: Seam)
    (ended: Ends item.trails seam):
    Ends (trailsBack (seen ++ item.words).reverse) seam :=
  endsWeaker item.trails (trailsBack (seen ++ item.words).reverse) (seenAppend seen item.words) seam ended

--| A broken bracket's items, each on a line after the one before and its comma.
--|
--| Proof idea: Induction on the items, as `Fmt.JoinProofs.brokenRestPasses`: each separator leaves the next item
--| free, and the words seen so far end with a comment exactly when the last item does (`seenAppend`).
theorem brokenSteps ∀ (seen: List Word) (items: List Expr) (bare arm first before: Bool) (at: Nat)
    (each: EachFree items):
    StepsAll
      (brokenItems bare arm first before at items)
      (Ends (trailsBack seen.reverse))
      (commaSpacing1 items)
      (Ends (trailsBack (seen ++ itemsWords items).reverse)) :=
  match items, each with
    | [], _ => stepsNil _ _ (seam ended => rewrite List.appendNil seen then ended)
    | [item], (steps, _) =>
      stepsTwo
        (if first then SoftLine else Line)
        (item.el (firstAround bare arm before at)) _
        (Fits True Free) _
        []
        (item.spacing1 False)
        (sepFree first (trailsBack seen.reverse))
        (stepsTo _ _ _ _ _ (steps (firstAround bare arm before at)) (seam ended =>
          rewrite List.appendNil item.words then itemEnds seen item seam ended))
    | [item, second, ..more], (steps, rest) =>
      stepsCons
        (if first then SoftLine else Line) _ _
        (Fits True Free) _
        []
        (item.spacing1 False ++ [Free] ++ commaSpacing1 [second, ..more])
        (sepFree first (trailsBack seen.reverse))
        (stepsCons
          (item.el (firstAround bare arm before at)) _ _
          (Ends (trailsBack (seen ++ item.words).reverse)) _
          (item.spacing1 False)
          ([Free] ++ commaSpacing1 [second, ..more])
          (stepsTo _ _ _ _ _ (steps (firstAround bare arm before at)) (seam ended => itemEnds seen item seam ended))
          (stepsCons
            (Closing ",") _ _
            (Ends (trailsBack (seen ++ item.words).reverse)) _
            [Free]
            (commaSpacing1 [second, ..more])
            (commaStep (trailsBack (seen ++ item.words).reverse))
            (rewrite <- List.appendAssoc seen item.words (itemsWords [second, ..more]) then
              brokenSteps (seen ++ item.words) [second, ..more] False arm False item.trails (at + item.size) rest)))

--| The steps of a fill's cells after the first, each after a separator.
def SepsSteps (docs: List Doc) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop): Prop :=
  ∀ (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop) => pre seam
    → (∀ (after: Seam) (added: List Touch) => post after
      → admitsGlue spacing (codeTouching added) = True
      → next after (trace ++ added))
    → SepsTouch docs seam trace next

theorem sepsNil ∀ (pre post: Seam → Prop) (implies: ∀ (seam: Seam) => pre seam → post seam): SepsSteps [] pre [] post :=
  seam trace next holds after => stay post [] seam trace next byComputing after (implies seam holds)

--| A cell after a separator, which touches as a `Line` does, then the cells after it.
theorem sepsCons ∀ (doc: Doc) (docs: List Doc) (pre middle post: Seam → Prop) (front back: List Spacing)
    (first: StepsAll [Line, doc] pre front middle)
    (rest: SepsSteps docs middle back post):
    SepsSteps [doc, ..docs] pre (front ++ back) post :=
  seam trace next holds after =>
    first seam trace (between later => SepsTouch docs between later next) holds (between added reached admits =>
      rest between (trace ++ added) next reached (left more ended admitsMore =>
        rewrite List.appendAssoc trace added more then
          after left
            (added ++ more)
            ended
            (rewrite codeTouchingAppend added more then
              admitsAppend front back (codeTouching added) (codeTouching more) admits admitsMore)))

--| A fill: its first cell, then the others each after a separator.
theorem stepsFill ∀ (doc: Doc) (docs: List Doc) (pre middle post: Seam → Prop) (front back: List Spacing)
    (first: Steps doc pre front middle)
    (rest: SepsSteps docs middle back post):
    Steps (Fill [doc, ..docs]) pre (front ++ back) post :=
  seam trace next holds after =>
    first seam trace (between later => SepsTouch docs between later next) holds (between added reached admits =>
      rest between (trace ++ added) next reached (left more ended admitsMore =>
        rewrite List.appendAssoc trace added more then
          after left
            (added ++ more)
            ended
            (rewrite codeTouchingAppend added more then
              admitsAppend front back (codeTouching added) (codeTouching more) admits admitsMore)))

--| A filled list's cells after the first.
theorem cellsRestSteps ∀ (seen: List Word) (items: List Expr) (arm before: Bool) (at: Nat)
    (each: EachFree items):
    SepsSteps
      (cells False arm before at items)
      (Ends (trailsBack seen.reverse))
      (commaSpacing1 items)
      (Ends (trailsBack (seen ++ itemsWords items).reverse)) :=
  match items, each with
    | [], _ => sepsNil _ _ (seam ended => rewrite List.appendNil seen then ended)
    | [item], (steps, _) =>
      rewrite <- List.appendNil (item.spacing1 False) then
        sepsCons
          (item.el (firstAround False arm before at))
          [] _ _ _
          (item.spacing1 False)
          []
          (stepsTwo Line
            (item.el (firstAround False arm before at)) _
            (Fits True Free) _
            []
            (item.spacing1 False)
            (sepFree False (trailsBack seen.reverse))
            (stepsTo _ _ _ _ _ (steps (firstAround False arm before at)) (seam ended =>
              rewrite List.appendNil item.words then itemEnds seen item seam ended)))
          (sepsNil _ _ (seam ended => ended))
    | [item, second, ..more], (steps, rest) =>
      rewrite <- List.appendAssoc (item.spacing1 False) [Free] (commaSpacing1 [second, ..more]) then
        sepsCons
          (Doc.concat [item.el (firstAround False arm before at), Closing ","]) _ _
          (Ends (trailsBack (seen ++ item.words).reverse)) _
          (item.spacing1 False ++ [Free])
          (commaSpacing1 [second, ..more])
          (stepsTwo Line
            (Doc.concat [item.el (firstAround False arm before at), Closing ","]) _
            (Fits True Free) _
            []
            (item.spacing1 False ++ [Free])
            (sepFree False (trailsBack seen.reverse))
            (stepsConcat _ _ _ _
              (stepsTwo
                (item.el (firstAround False arm before at))
                (Closing ",") _ _ _
                (item.spacing1 False)
                [Free]
                (stepsTo _ _ _ _ _ (steps (firstAround False arm before at)) (seam ended =>
                  itemEnds seen item seam ended))
                (commaStep (trailsBack (seen ++ item.words).reverse)))))
          (rewrite <- List.appendAssoc seen item.words (itemsWords [second, ..more]) then
            cellsRestSteps (seen ++ item.words) [second, ..more] arm item.trails (at + item.size) rest)

--| A filled list's cells: the first after the opener, the others each after a separator.
theorem cellsSteps ∀ (open: Word) (item: Expr) (others: List Expr) (bare arm before: Bool) (at: Nat)
    (each: EachFree [item, ..others]):
    Steps
      (Fill (cells bare arm before at [item, ..others]))
      (Ends (trailsBack [open].reverse))
      (commaSpacing1 [item, ..others])
      (Ends (trailsBack ([open] ++ itemsWords [item, ..others]).reverse)) :=
  let start: ∀ (seam: Seam) => Ends (trailsBack [open].reverse) seam → Fits True Free seam := seam ended =>
    fitsWeaker
      (trailsBack [open].reverse)
      True
      (_ => byComputing)
      Free
      seam
      (endsFits (trailsBack [open].reverse) seam ended)
  match others, each with
    | [], (steps, _) =>
      rewrite <- List.appendNil (item.spacing1 False) then
        stepsFill
          (item.el (firstAround bare arm before at))
          [] _ _ _
          (item.spacing1 False)
          []
          (stepsFrom _ _ _ _ _
            (stepsTo _ _ _ _ _ (steps (firstAround bare arm before at)) (seam ended =>
              rewrite List.appendNil item.words then itemEnds [open] item seam ended))
            start)
          (sepsNil _ _ (seam ended => ended))
    | [second, ..more], (steps, rest) =>
      rewrite <- List.appendAssoc (item.spacing1 False) [Free] (commaSpacing1 [second, ..more]) then
        stepsFill
          (Doc.concat [item.el (firstAround bare arm before at), Closing ","]) _ _
          (Ends (trailsBack ([open] ++ item.words).reverse)) _
          (item.spacing1 False ++ [Free])
          (commaSpacing1 [second, ..more])
          (stepsFrom _ _ _ _ _
            (stepsConcat _ _ _ _
              (stepsTwo
                (item.el (firstAround bare arm before at))
                (Closing ",") _ _ _
                (item.spacing1 False)
                [Free]
                (stepsTo _ _ _ _ _ (steps (firstAround bare arm before at)) (seam ended =>
                  itemEnds [open] item seam ended))
                (commaStep (trailsBack ([open] ++ item.words).reverse))))
            start)
          (rewrite <- List.appendAssoc [open] item.words (itemsWords [second, ..more]) then
            cellsRestSteps ([open] ++ item.words) [second, ..more] arm item.trails (at + item.size) rest)

--| A bracket's closer, after the code seen inside it: the bracket ends with a comment where the closer or that code
--| does.
theorem closerEndsSeen ∀ (open close: Word) (middle: List Word) (seam: Seam)
    (closer: isCloserText close.text = True)
    (closed: Closed (close.trails || trailsBack ([open] ++ middle).reverse) seam):
    Ends (trailsBack ([open, ..middle] ++ [close]).reverse) seam :=
  rewrite bracketTrails open close middle closer then
    (rewrite List.reverseCons open middle at closed then closedEnds _ seam closed)

--| A tuple's or list's parts (`bracketContent`), the opener spaced `first` and the rest free.
--|
--| Proof idea: `bracketIs` names the three layouts: empty, filled (`cellsSteps`) and broken (`brokenSteps`). In each
--| the items end with a comment as their words do, which is where the closer stands (`beforeCloseIs`).
theorem bracketSteps ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around) (first: Spacing)
    (unhoisted: around.hoisted = True)
    (opener: WordJoins open)
    (closer: CloserJoins close)
    (each: EachFree items):
    Steps
      (bracketContent list open items close around)
      (Fits True first)
      ([first, ..commaSpacing1 items] ++ [Free])
      (Ends (ListOf open items False close).trails) :=
  let (closeSound, isCloser) := closer
  let notCloser := opener.right.right.right
  let whole := ListOf open items False close
  let closeAround := around.next whole.trailsBeforeClose (whole.size - 1)
  let seen := trailsBack ([open] ++ itemsWords items).reverse
  let prefixSteps: Steps (open.opening around close) (Fits True first) [first] (Ends (trailsBack [open].reverse)) :=
    stepsTo _ _ _ _ _ (openingSteps open around close first opener (Inr (rewrite unhoisted))) (seam closed =>
      rewrite openTrails open notCloser then closedEnds open.trails seam closed)
  let closerSteps: Steps (close.leaf closeAround around.at) (Ends seen) [Free] (Ends whole.trails) :=
    stepsFrom _ _ _ _ _
      (stepsTo _ _ _ _ _ (closerLeafSteps close closeAround around.at closer byComputing) (seam closed =>
        closerEndsSeen open close
          (itemsWords items)
          seam
          isCloser
          (rewrite beforeCloseIs open items close at closed then closed)))
      (seam ended => rewrite beforeCloseIs open items close then endsFits seen seam ended)
  let bare := list && items.all Expr.plainItem
  let broken := brokenItems bare around.inArm True open.trails (around.at + 1) items
  let brokenSteps': StepsAll
    [open.opening around close, Nest 2 (Doc.concat broken), SoftLine, close.leaf closeAround around.at]
    (Fits True first)
    ([first] ++ (commaSpacing1 items ++ ([] ++ [Free])))
    (Ends whole.trails) :=
    stepsCons
      (open.opening around close) _ _ _ _
      [first] _
      prefixSteps
      (stepsCons
        (Nest 2 (Doc.concat broken)) _ _
        (Ends seen) _
        (commaSpacing1 items) _
        (stepsNest 2 _ _ _ _
          (stepsConcat _ _ _ _ (brokenSteps [open] items bare around.inArm True open.trails (around.at + 1) each)))
        (stepsTwo SoftLine
          (close.leaf closeAround around.at) _
          (Ends seen) _
          []
          [Free]
          (stepsSoft _ _ (seam ended => endsQuiet seen seam ended) (seam ended => ended) byComputing)
          closerSteps))
  rewrite bracketIs list open items close around then
    match items, each with
      | [], _ =>
        stepsConcat
          [open.opening around close, close.leaf closeAround around.at] _ _ _
          (stepsTwo
            (open.opening around close)
            (close.leaf closeAround around.at) _
            (Ends seen) _
            [first]
            [Free]
            (stepsTo _ _ _ _ _ prefixSteps (seam ended => ended))
            closerSteps)
      | [item, ..others], each =>
        match filled: list && !whole.holdsTrailingComment && [item, ..others].all Expr.plainItem with
          | True =>
            stepsConcat
              [
                open.opening around close,
                Nest 2 (Fill (cells bare around.inArm open.trails (around.at + 1) [item, ..others])),
                close.leaf closeAround around.at
              ] _ _ _
              (stepsCons
                (open.opening around close)
                [
                  Nest 2 (Fill (cells bare around.inArm open.trails (around.at + 1) [item, ..others])),
                  close.leaf closeAround around.at
                ] _ _ _
                [first] _
                prefixSteps
                (stepsTwo
                  (Nest 2 (Fill (cells bare around.inArm open.trails (around.at + 1) [item, ..others])))
                  (close.leaf closeAround around.at) _
                  (Ends seen) _
                  (commaSpacing1 [item, ..others])
                  [Free]
                  (stepsNest 2 _ _ _ _ (cellsSteps open item others bare around.inArm open.trails (around.at + 1) each))
                  closerSteps))
          | False =>
            match holds: whole.holdsTrailingComment with
              | True =>
                stepsConcat
                  ([open.opening around close, Nest 2 (Doc.concat broken), SoftLine, close.leaf closeAround around.at]
                    ++ [BreakParent]) _ _ _
                  (allSpacing _ _ _ _ _
                    (List.appendNil _)
                    (stepsAppend
                      [
                        open.opening around close,
                        Nest 2 (Doc.concat broken),
                        SoftLine,
                        close.leaf closeAround around.at
                      ]
                      [BreakParent] _ _ _ _
                      []
                      brokenSteps'
                      (stepsLast BreakParent _ _ [] (stepsBreakParent _))))
              | False =>
                stepsConcat
                  [
                    open.opening around close,
                    Nest 2 (Doc.concat broken),
                    SoftLine,
                    close.leaf closeAround around.at
                  ] _ _ _
                  brokenSteps'

--| A tuple or list, `(a, b)` or `[a, b]`, filled or broken: the opener spaced `first`, then each item and comma free.
theorem commaSteps ∀ (list: Bool) (open: Word) (items: List Expr) (comma: Bool) (close: Word) (around: Around)
    (first: Spacing) (argument: Bool)
    (within: (if list then ListOf open items comma close else Tuple open items comma close).within1 = True)
    (shaped: (if list then ListOf open items comma close else Tuple open items comma close).shaped1 = True)
    (lexical: (if list then ListOf open items comma close else Tuple open items comma close).lexical1 = True)
    (joinable: Joinable lexKind (if list then ListOf open items comma close else Tuple open items comma close))
    (loose: Loose first ∨ open.quietAt around around.at = True)
    (each: EachElSteps items):
    Steps
      ((if list then ListOf open items comma close else Tuple open items comma close).el around)
      (Fits True first)
      (spacedFirst first
        ((if list then ListOf open items comma close else Tuple open items comma close).spacing1 argument))
      (Ends (if list then ListOf open items comma close else Tuple open items comma close).trails) :=
  match list with
    | True =>
      let (opener, closer, joins) := joinable
      framedSteps open around
        (commaBracket True open items close { around | hoisted = True }) _ _
        first
        opener.left.left
        loose
        (stepsGroup
          (bracketContent True open items close { around | hoisted = True })
          (bracketContent True open items close { around | hoisted = True }).forcesBreak _ _ _
          (bracketSteps True open items close
            { around | hoisted = True }
            first
            byComputing
            opener.left
            closer
            (eachFree items each within shaped (Bool.andRight (Bool.andRight lexical)) joins)))
    | False =>
      let (opener, closer, joins) := joinable
      framedSteps open around
        (commaBracket False open items close { around | hoisted = True }) _ _
        first
        opener.left.left
        loose
        (stepsGroup
          (bracketContent False open items close { around | hoisted = True })
          (bracketContent False open items close { around | hoisted = True }).forcesBreak _ _ _
          (bracketSteps False open items close
            { around | hoisted = True }
            first
            byComputing
            opener.left
            closer
            (eachFree items each within (Bool.andRight shaped) (Bool.andRight (Bool.andRight lexical)) joins)))

--| `appSteps` (open): a call, its head spaced `first` and each argument as `argumentsSpacing1` says (`spacing1 True`:
--| free, or apart for a sign), every argument after a space, a fill separator or a `HardLine`. Its route follows
--| `Fmt.JoinProofs.appFromPasses`: a sequence of documents each but the first starting from `Fits True Apart` (which
--| gives `Fits True Free`), split at `keep` with its spacing, through `spaced`, `Fill`, the `Choice` options (`Flatten`,
--| the hug, front and rest) and `IfBroken`; each argument from `elSteps` with `argument1` from `shaped1`.
theorem appSteps ∀ (head: Expr) (arguments: List Expr) (around: Around) (first: Spacing) (argument: Bool)
    (within: (App head arguments).within1 = True)
    (shaped: (App head arguments).shaped1 = True)
    (lexical: (App head arguments).lexical1 = True)
    (joinable: Joinable lexKind (App head arguments))
    (loose: Loose first ∨ (App head arguments).firstWord.quietAt around around.at = True)
    (headSteps: ElSteps head)
    (each: EachElSteps arguments):
    Steps
      ((App head arguments).el around)
      (Fits True first)
      (spacedFirst first ((App head arguments).spacing1 argument))
      (Ends (App head arguments).trails) :=
  ?

-- Chains.

--| A chain's first link and the rest, the rest nested.
theorem headTailSteps ∀ (head: Doc) (tail: List Doc) (indent: Nat) (pre: Seam → Prop)
    (spacing: List Spacing) (post: Seam → Prop)
    (all: StepsAll [head, ..tail] pre spacing post):
    Steps (Doc.concat [head, Nest indent (Doc.concat tail)]) pre spacing post :=
  stepsConcat [head, Nest indent (Doc.concat tail)] pre spacing post (seam trace next holds after =>
    touchesWeaker head seam trace _ _
      (between later touches => concatTouches tail between later next touches)
      (all seam trace next holds after))

theorem chainOfSteps ∀ (arms: Bool) (links: List Doc) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop)
    (all: StepsAll links pre spacing post)
    (filled: links ≠ []):
    Steps (chainOf arms links) pre spacing post :=
  match links, all with
    | [], _ => (filled byComputing).impossible
    | [head, ..tail], all =>
      let joined := Doc.concat [head, Nest (if arms then 0 else 2) (Doc.concat tail)]
      stepsGroup joined joined.forcesBreak pre spacing post
        (headTailSteps head tail (if arms then 0 else 2) pre spacing post all)

--| A chain ends with a comment where its right operand does.
theorem rightEnds ∀ (left: Expr) (operator: Word) (right: Expr) (seam: Seam)
    (ended: Ends right.trails seam):
    Ends (trailsBack (left.words ++ [operator, ..right.words]).reverse) seam :=
  endsWeaker right.trails
    (trailsBack (left.words ++ [operator, ..right.words]).reverse)
    (trails =>
      seenAppend left.words
        [operator, ..right.words]
        (rewrite List.reverseCons operator right.words then trailsBackAppend right.words.reverse [operator] trails))
    seam
    ended

--| What follows a chain's operator: a space, then the right operand apart.
theorem chainRightSteps ∀ (level: Option Nat) (right: Expr) (place: Around) (trails: Bool) (post: Seam → Prop)
    (within: right.within1 = True)
    (shaped: right.shaped1 = True)
    (lexical: right.lexical1 = True)
    (joinable: Joinable lexKind right) (ends: ∀ (seam: Seam) => Ends right.trails seam → post seam):
    StepsAll (chainRight level right place) (Ends trails) (spacedFirst Apart (right.spacing1 False)) post :=
  let rest := linkSteps level False right place Apart within shaped lexical joinable (Inl byComputing)
  match right with
    | Block _ _ _ => cases
    | _ =>
      stepsCons
        (Doc.text " ") _
        (Ends trails)
        (Fits True Apart)
        post
        []
        (spacedFirst Apart (right.spacing1 False))
        (stepsTo _ _ _ _ _ (stepsSpace trails) (seam gapped =>
          fitsWeaker trails True (_ => byComputing) Apart seam (gappedFits trails Apart seam byComputing gapped)))
        (allTo _ _ _ _ _ rest ends)

--| A chain's links: its first operand's, then each operator after a line break and its operand after a space.
theorem chainLinksSteps ∀ (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (start: Spacing)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftShaped: left.shaped1 = True)
    (rightShaped: right.shaped1 = True)
    (leftLexical: left.lexical1 = True)
    (rightLexical: right.lexical1 = True)
    (leftJoins: Joinable lexKind left)
    (operatorJoins: WordJoins operator)
    (rightJoins: Joinable lexKind right)
    (loose: Loose start ∨ left.firstWord.quietAt around around.at = True):
    StepsAll
      (chainLinks level first left operator right around)
      (Fits True start)
      (spacedFirst start (left.spacing1 False) ++ [Free, ..spacedFirst Apart (right.spacing1 False)])
      (Ends (trailsBack (left.words ++ [operator, ..right.words]).reverse)) :=
  let operatorAround := around.next left.trails left.size
  let rightAround := around.next operator.trails (left.size + 1)
  stepsAppend
    (linkDocs level first left around)
    [Line, operator.leaf operatorAround operatorAround.at, ..chainRight level right rightAround] _
    (Ends left.trails) _
    (spacedFirst start (left.spacing1 False))
    [Free, ..spacedFirst Apart (right.spacing1 False)]
    (linkSteps level first left around start leftWithin leftShaped leftLexical leftJoins loose)
    (stepsCons Line _ _
      (Fits True Free) _
      []
      [Free, ..spacedFirst Apart (right.spacing1 False)]
      (stepsTo _ _ _ _ _ (stepsLine left.trails) (seam gapped =>
        fitsWeaker left.trails True (_ => byComputing) Free seam (gappedFits left.trails Free seam byComputing gapped)))
      (stepsCons
        (operator.leaf operatorAround operatorAround.at) _ _
        (Ends operator.trails) _
        [Free]
        (spacedFirst Apart (right.spacing1 False))
        (stepsTo _ _ _ _ _
          (wordLeafSteps operator operatorAround operatorAround.at Free operatorJoins (Inl byComputing))
          (seam closed => closedEnds operator.trails seam closed))
        (chainRightSteps level right rightAround operator.trails _ rightWithin rightShaped rightLexical rightJoins
          (seam ended => rightEnds left operator right seam ended))))

theorem infixFirstWord ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix kind left operator right).within1 = True)
    (leftWithin: left.within1 = True):
    (Infix kind left operator right).firstWord = left.firstWord :=
  rewrite firstWordLead (Infix kind left operator right) within, firstWordLead left leftWithin

--| A chain's operand of the same level in its links, as a chain's links; another operand as its element.
theorem chainedSteps ∀ (level: Option Nat) (first: Bool) (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (start: Spacing)
    (within: (Infix kind left operator right).within1 = True)
    (shaped: (Infix kind left operator right).shaped1 = True)
    (lexical: (Infix kind left operator right).lexical1 = True)
    (joinable: Joinable lexKind (Infix kind left operator right))
    (loose: Loose start ∨ (Infix kind left operator right).firstWord.quietAt around around.at = True)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True):
    StepsAll
      (chainLinks level first left operator right around)
      (Fits True start)
      (spacedFirst start ((Infix kind left operator right).spacing1 False))
      (Ends (Infix kind left operator right).trails) :=
  let (leftJoins, operatorJoins, rightJoins) := joinable
  let (rest, free) := spacingFree left leftWithin
  allSpacing _ _ _ _ _
    (rewrite free)
    (chainLinksSteps level first left operator right around start leftWithin rightWithin
      (Bool.andLeft shaped)
      (Bool.andLeft (Bool.andRight shaped))
      (Bool.andLeft lexical)
      (Bool.andRight (Bool.andRight lexical))
      leftJoins
      operatorJoins
      rightJoins
      (rewrite <- infixFirstWord kind left operator right within leftWithin then loose))

--| An operand of a chain: its links if it is a chain of the same level, else its element.
theorem linkSteps ∀ (level: Option Nat) (first: Bool) (expr: Expr) (around: Around) (start: Spacing)
    (within: expr.within1 = True)
    (shaped: expr.shaped1 = True)
    (lexical: expr.lexical1 = True)
    (joinable: Joinable lexKind expr)
    (loose: Loose start ∨ expr.firstWord.quietAt around around.at = True):
    StepsAll
      (linkDocs level first expr around)
      (Fits True start)
      (spacedFirst start (expr.spacing1 False))
      (Ends expr.trails) :=
  let element: StepsAll
    [expr.el around]
    (Fits True start)
    (spacedFirst start (expr.spacing1 False))
    (Ends expr.trails) :=
    stepsLast
      (expr.el around) _ _ _
      (elSteps expr within shaped lexical joinable around start False
        (never => (Bool.falseNotTrue never).impossible)
        loose)
  match expr with
    | Infix InfixBinary left operator right =>
      match chained: (Infix InfixBinary left operator right).inChain level with
        | True =>
          chainedSteps level first InfixBinary left operator right around start within shaped lexical joinable loose
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
        | False => element
    | Infix InfixArrow left operator right =>
      match chained: (Infix InfixArrow left operator right).inChain level with
        | True =>
          chainedSteps level first InfixArrow left operator right around start within shaped lexical joinable loose
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
        | False => element
    | Match _ _ _ _ => cases
    | _ => element

--| A chain's element, its first word's own-line comments before it.
theorem chainElSteps ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr) (around: Around)
    (first: Spacing) (argument: Bool)
    (within: (Infix kind left operator right).within1 = True)
    (shaped: (Infix kind left operator right).shaped1 = True)
    (lexical: (Infix kind left operator right).lexical1 = True)
    (joinable: Joinable lexKind (Infix kind left operator right))
    (loose: Loose first ∨ (Infix kind left operator right).firstWord.quietAt around around.at = True)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True):
    Steps
      (framedBy
        (Infix kind left operator right).firstWord
        around
        (chain (Infix kind left operator right).chainLevel left operator right { around | hoisted = True }))
      (Fits True first)
      (spacedFirst first ((Infix kind left operator right).spacing1 argument))
      (Ends (Infix kind left operator right).trails) :=
  let inside := { around | hoisted = True }
  let lead := leadJoins lexKind (Infix kind left operator right) joinable
  let sound: (Infix kind left operator right).firstWord.sound = True :=
    rewrite firstWordLead (Infix kind left operator right) within then lead.left
  let level := (Infix kind left operator right).chainLevel
  let links := chainLinks level True left operator right inside
  let filled: links ≠ [] := List.appendNotNilRight (linkDocs level True left inside) _ (List.consNotNil Line _)
  let insideLoose: Loose first ∨ (Infix kind left operator right).firstWord.quietAt inside inside.at = True :=
    match loose with
      | Inl free => Inl free
      | Inr quiet => Inr (Bool.andIntro (Bool.andLeft quiet) byComputing)
  framedSteps
    (Infix kind left operator right).firstWord
    around
    (chain level left operator right inside) _ _
    first
    sound
    loose
    (chainOfSteps
      (left.opensArms level)
      links _ _ _
      (chainedSteps level True kind left operator right inside first within shaped lexical joinable insideLoose
          leftWithin rightWithin)
      filled)

--| An infix chain: its first operand spaced `first`, each operator free after a line break and each right operand
--| apart, after a space.
--|
--| Proof idea: `chainOf` groups the links (`chainOfSteps`), which `chainedSteps` gives by induction through
--| `linkSteps`, each operand not of the chain's level by `elSteps`.
theorem infixSteps ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr) (around: Around)
    (first: Spacing) (argument: Bool)
    (within: (Infix kind left operator right).within1 = True)
    (shaped: (Infix kind left operator right).shaped1 = True)
    (lexical: (Infix kind left operator right).lexical1 = True)
    (joinable: Joinable lexKind (Infix kind left operator right))
    (loose: Loose first ∨ (Infix kind left operator right).firstWord.quietAt around around.at = True):
    Steps
      ((Infix kind left operator right).el around)
      (Fits True first)
      (spacedFirst first ((Infix kind left operator right).spacing1 argument))
      (Ends (Infix kind left operator right).trails) :=
  match kind with
    | InfixBinary =>
      chainElSteps InfixBinary left operator right around first argument within shaped lexical joinable loose
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight within))
    | InfixArrow =>
      chainElSteps InfixArrow left operator right around first argument within shaped lexical joinable loose
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight within))

-- Every element.

--| Every expression's element touches as its spacing says.
theorem elSteps ∀ (expr: Expr): ElSteps expr := match expr with
  | Atom kind word => within shaped lexical joinable around first argument isArgument loose =>
    atomSteps kind word around first argument joinable loose
  | Paren open inner close => within shaped lexical joinable around first argument isArgument loose =>
    parenSteps open inner close around first argument within shaped lexical joinable loose (elSteps inner)
  | Tuple open items comma close => within shaped lexical joinable around first argument isArgument loose =>
    commaSteps False open items comma close around first argument within shaped lexical joinable loose
      (allElSteps items)
  | ListOf open items comma close => within shaped lexical joinable around first argument isArgument loose =>
    commaSteps True open items comma close around first argument within shaped lexical joinable loose (allElSteps items)
  | App head arguments => within shaped lexical joinable around first argument isArgument loose =>
    appSteps head arguments around first argument within shaped lexical joinable loose
      (elSteps head)
      (allElSteps arguments)
  | Infix kind left operator right => within shaped lexical joinable around first argument isArgument loose =>
    infixSteps kind left operator right around first argument within shaped lexical joinable loose
  | Prefix operator operand => within shaped lexical joinable around first argument isArgument loose =>
    prefixSteps operator operand around first argument within shaped lexical joinable isArgument loose (elSteps operand)
  | _ => within => cases

theorem allElSteps ∀ (items: List Expr): EachElSteps items := match items with
  | [] => byComputing
  | [item, ..rest] => (elSteps item, allElSteps rest)
