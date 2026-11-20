--| Step 2 of tools/fmt/NOTES.md, "Printed spacing" (SW-4076): slice 1's rules print each code word touching the
--| piece before it as `Expr.spacing` asks, in the triples of `Fmt.TouchSteps`. A sign's operand comes straight after
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
import Fmt.TouchSeq (..)
import Fmt.JoinProofs (keptShort, leadJoins, ownEmpty)
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
    | True => stepsLast pre pre (stepsBlank pre)
    | False => stepsNil pre pre (seam holds => holds)

--| Own-line comments above a token, each ending its line.
--|
--| Proof idea: induction on the notes; each is an optional blank line, its text from a line start, and a line break.
theorem notesAboveSteps ∀ (notes: List Note)
    (sound: notesSound notes = True):
    StepsAll (notesAbove notes) (seam => seam = Begun) [] (seam => seam = Begun) :=
  match notes with
    | [] => stepsNil _ _ (seam holds => holds)
    | [note, ..rest] =>
      stepsAppend
        (if note.blankBefore then [Blank] else [])
        (seam => seam = Begun)
        (seam => seam = Begun)
        (seam => seam = Begun)
        (stepsBlankList note.blankBefore (seam => seam = Begun))
        (stepsCons
          (Doc.text note.text)
          [HardLine, ..notesAbove rest]
          (seam => seam = Begun)
          (seam => seam = Along True)
          (seam => seam = Begun)
          (stepsComment note.text (Bool.andLeft sound))
          (stepsCons HardLine
            (notesAbove rest)
            (seam => seam = Along True)
            (seam => seam = Begun)
            (seam => seam = Begun)
            (stepsHard _ _ (seam along => rewrite along) byComputing)
            (notesAboveSteps rest (Bool.andRight sound))))

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
        (stepsHard _ _ (seam along => rewrite along) byComputing)
        (stepsAppend
          (if note.blankBefore then [Blank] else [])
          (seam => seam = Begun)
          (seam => seam = Begun)
          (seam => seam = Along True)
          (stepsBlankList note.blankBefore (seam => seam = Begun))
          (stepsCons
            (Doc.text note.text)
            (laterCloserNotes rest)
            (seam => seam = Begun)
            (seam => seam = Along True)
            (seam => seam = Along True)
            (stepsComment note.text (Bool.andLeft sound))
            (laterCloserNotesSteps rest (Bool.andRight sound))))

theorem closerNotesSteps ∀ (note: Note) (rest: List Note)
    (sound: notesSound [note, ..rest] = True):
    StepsAll (closerNotes [note, ..rest]) (seam => seam = Begun) [] (seam => seam = Along True) :=
  stepsAppend
    (if note.blankBefore then [Blank] else [])
    (seam => seam = Begun)
    (seam => seam = Begun)
    (seam => seam = Along True)
    (stepsBlankList note.blankBefore (seam => seam = Begun))
    (stepsCons
      (Doc.text note.text)
      (laterCloserNotes rest)
      (seam => seam = Begun)
      (seam => seam = Along True)
      (seam => seam = Along True)
      (stepsComment note.text (Bool.andLeft sound))
      (laterCloserNotesSteps rest (Bool.andRight sound)))

-- A token's own-line comments.

--| Whether a token is printed with nothing before it on its line from where it stands: no own-line comments, no
--| blank line kept, no comment waiting before it.
def Word.quietAt (word: Word) (around: Around) (key: Nat): Bool :=
  !(word.displaces around) && (word.leading around key).isEmpty

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
            (stepsBreakParent _)
            (stepsCons LineStart
              [Blank]
              (Fits before first)
              (Fits before first)
              (Fits before first)
              (stepsLineStart _ _ (seam fits => fitsQuiet before first seam fits) (fresh byComputing))
              (stepsLast _ _ (stepsBlank _)))
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
            (stepsBreakParent _)
            (stepsCons
              (Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]))
              [CloserLine key]
              (Fits before first)
              (seam => seam = Along True)
              (Fits before first)
              (stepsNest 2 _ _
                (stepsConcat _ _ _
                  (stepsCons LineStartHere
                    (closerNotes [note, ..rest])
                    (Fits before first)
                    (seam => seam = Begun)
                    (seam => seam = Along True)
                    (stepsLineStartHere _ _ (seam fits => fitsQuiet before first seam fits) byComputing)
                    (closerNotesSteps note rest notes))))
              (stepsLast _ _ (stepsCloserLine key _ _ (seam along => rewrite along) begun)))
        | False =>
          let begun := fresh byComputing
          stepsAppend
            [BreakParent, LineStart, ..notesAbove [note, ..rest]]
            (Fits before first)
            (seam => seam = Begun)
            (Fits before first)
            (stepsCons BreakParent
              [LineStart, ..notesAbove [note, ..rest]]
              (Fits before first)
              (Fits before first)
              (seam => seam = Begun)
              (stepsBreakParent _)
              (stepsCons LineStart
                (notesAbove [note, ..rest])
                (Fits before first)
                (seam => seam = Begun)
                (seam => seam = Begun)
                (stepsLineStart _ _ (seam fits => fitsQuiet before first seam fits) byComputing)
                (notesAboveSteps [note, ..rest] notes)))
            (allTo _ _ _ _ (stepsBlankList blankBefore (seam => seam = Begun)) (seam begun' =>
              rewrite begun' then begun))

-- Tokens.

theorem soundSolid ∀ (word: Word) (sound: word.sound = True): isLayout word.text = False :=
  Bool.notTrue (isLayout word.text) (Bool.andLeft sound)

--| A token's text is code: from what `Joinable` says of it.
theorem wordCode ∀ (word: Word) (sound: word.sound = True) (token: Token word.text): Code word.text :=
  let solid := soundSolid word sound
  (Doc.Proofs.wordFilled word.text solid, solid, token)

--| A token's trailing comment, after it on its line.
theorem trailingSteps ∀ (word: Word)
    (sound: word.sound = True):
    StepsAll word.trailing (seam => seam = Along True) [] (Closed word.trails) :=
  match word with
    | { text, comments = { above, after = None, blankBefore } } => stepsNil _ _ (seam along => rewrite along)
    | { text, comments = { above, after = Some comment, blankBefore } } =>
      let commented: commentText comment = True := Bool.andRight (Bool.andRight sound)
      stepsLast _ _ (stepsSuffix comment (Bool.andLeft commented) (commentNotLayout comment commented))

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
  stepsConcat _ _ _
    (rewrite ownEmpty word.text (!word.noted && around.before && word.trails) key closer,
        pieceText word.text closer comma then
      stepsAppend
        (word.leading around key)
        (Fits True first)
        (Fits True first)
        (Closed word.trails)
        (leadingSteps word around key True first sound loose)
        (stepsCons
          (Doc.text word.text)
          word.trailing
          (Fits True first)
          (seam => seam = Along True)
          (Closed word.trails)
          (stepsChunk word.text.length True first (wordCode word sound token))
          (trailingSteps word sound)))

--| An opening bracket, as a token that is no closer, with a `Mark` before it.
theorem openingSteps ∀ (word: Word) (around: Around) (closer: Word) (first: Spacing)
    (joins: WordJoins word)
    (loose: Loose first ∨ (word.leading around around.at).isEmpty = True):
    Steps (word.opening around closer) (Fits True first) [first] (Closed word.trails) :=
  let (sound, token, comma, notCloser) := joins
  let marked := closer.noted || closer.trails
  stepsConcat _ _ _
    (rewrite pieceText word.text notCloser comma then
      stepsAppend
        (word.leading around around.at)
        (Fits True first)
        (Fits True first)
        (Closed word.trails)
        (leadingSteps word around around.at True first sound loose)
        (stepsAppend
          (if marked then [Mark around.at] else [])
          (Fits True first)
          (Fits True first)
          (Closed word.trails)
          (markSteps marked around.at (Fits True first))
          (stepsCons
            (Doc.text word.text)
            word.trailing
            (Fits True first)
            (seam => seam = Along True)
            (Closed word.trails)
            (stepsChunk word.text.length True first (wordCode word sound token))
            (trailingSteps word sound))))

theorem markSteps ∀ (marked: Bool) (key: Nat) (pre: Seam → Prop):
    StepsAll (if marked then [Mark key] else []) pre [] pre :=
  match marked with
    | True => stepsLast pre pre (stepsMark key pre)
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
            (stepsBreakParent _)
            (stepsCons LineStart
              [Blank]
              (Fits before Free)
              (Fits before Free)
              (Fits before Free)
              (stepsLineStart _ _ (seam fits => fitsQuiet before Free seam fits) byComputing)
              (stepsLast _ _ (stepsBlank _)))
        | False => stepsNil _ _ (seam holds => holds)
    | { text, comments = { above = [note, ..rest], after, blankBefore } }, False =>
      let notes: notesSound [note, ..rest] = True := Bool.andLeft (Bool.andRight sound)
      rewrite closer then
        stepsCons BreakParent
          [Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]), CloserLine key]
          (Fits before Free)
          (Fits before Free)
          (Fits False Free)
          (stepsBreakParent _)
          (stepsCons
            (Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]))
            [CloserLine key]
            (Fits before Free)
            (seam => seam = Along True)
            (Fits False Free)
            (stepsNest 2 _ _
              (stepsConcat _ _ _
                (stepsCons LineStartHere
                  (closerNotes [note, ..rest])
                  (Fits before Free)
                  (seam => seam = Begun)
                  (seam => seam = Along True)
                  (stepsLineStartHere _ _ (seam fits => fitsQuiet before Free seam fits) byComputing)
                  (closerNotesSteps note rest notes))))
            (stepsLast _ _ (stepsCloserLine key _ _ (seam along => rewrite along) byComputing)))

--| A closer line, where the closer takes a line of its own: after it no comment waits.
theorem ownSteps ∀ (own: Bool) (key: Nat) (held: Bool):
    StepsAll (if own then [CloserLine key] else []) (Fits held Free) [] (Fits (if own then False else held) Free) :=
  match own with
    | True => stepsLast _ _ (stepsCloserLine key _ _ (seam fits => fitsQuiet held Free seam fits) byComputing)
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
      stepsLast _ _
        (stepsTo _ _ _ _ (stepsClosing held code) (seam closed => closedWeaker held ends weaker seam closed))
    | { text, comments = { above, after = Some comment, blankBefore } }, code, clear, own =>
      let cleared: held = False := clear byComputing
      let commented: commentText comment = True := Bool.andRight (Bool.andRight sound)
      stepsCons
        (Closing text)
        [LineSuffix comment]
        (Fits held Free)
        (seam => seam = Along True)
        (Closed ends)
        (stepsTo _ _ _ _ (stepsClosing held code) (seam closed =>
          closedAlong seam (rewrite cleared at closed then closed)))
        (stepsLast _ _
          (stepsTo _ _ _ _
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
    | False, True | False => byComputing

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
  stepsConcat _ _ _
    (rewrite pieceCloser word.text closer then
      stepsAppend
        (word.leading around key)
        (Fits around.before Free)
        (Fits lead Free)
        (Closed (word.trails || around.before))
        (closerLeadingSteps word around key around.before sound closer unhoisted)
        (stepsAppend
          (if own then [CloserLine key] else [])
          (Fits lead Free)
          (Fits held Free)
          (Closed (word.trails || around.before))
          (ownSteps own key lead)
          (closingTail word held (word.trails || around.before) sound (closerCode word.text closer) clear weaker own')))

-- Elements.

--| A displaced element, where a comment comes before it; else the element as it is.
theorem placedSteps ∀ (displaced: Bool) (doc: Doc) (first: Spacing) (spacing: List Spacing) (post: Seam → Prop)
    (inner: Steps doc (Fits True first) spacing post)
    (fresh: displaced = True → Loose first):
    Steps (if displaced then Displaced doc else doc) (Fits True first) spacing post :=
  match displaced, fresh with
    | True, fresh => stepsDisplaced _ _ inner (fresh byComputing) (seam fits => fitsQuiet True first seam fits)
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
  let fresh: (first.displaces around) = True → Loose start := shown =>
    match loose with
      | Inl free => free
      | Inr quiet => (Bool.falseNotTrue (rewrite shown at quiet then quiet)).impossible
  stepsConcat _ _ _
    (stepsTwo
      (Doc.concat (first.leading around around.at))
      (Fits True start)
      (Fits True start)
      post
      (stepsConcat _ _ _ (leadingSteps first around around.at True start sound leadLoose))
      (placedSteps (first.displaces around) doc start spacing post inner fresh))

--| An expression of the slice spaces its first code word as `Free`.
--|
--| Proof idea: induction on the expression; a sign that is no argument is free, and every other node starts with its
--| first part's spacing or a bracket.
theorem spacingFree ∀ (expr: Expr)
    (within: expr.within1 = True):
    ∃ (rest: List Spacing) => expr.spacing False = [Free, ..rest] :=
  match expr with
    | Atom kind word => ([], byComputing)
    | Paren open inner close => (inner.spacing False ++ [Free], byComputing)
    | Tuple _ items _ _ | ListOf _ items _ _ => (commaSpacing items ++ [Free], byComputing)
    | App head arguments =>
      let (rest, head) := spacingFree head (Bool.andLeft within)
      (rest ++ argumentsSpacing arguments, rewrite head)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (rest, left) := spacingFree left (Bool.andLeft within)
          (rest ++ [Free, ..spacedFirst Apart (right.spacing False)], rewrite left)
        | InfixArrow =>
          let (rest, left) := spacingFree left (Bool.andLeft within)
          (rest ++ [Free, ..spacedFirst Apart (right.spacing False)], rewrite left)
        | _ => cases
    | Prefix operator operand =>
      match operandSpacing False operator operand with
        | Some spacing => (spacedFirst spacing (operand.spacing False), byComputing)
        | None => (operand.spacing False, byComputing)

--| Spacing an expression's first code word as `Free` leaves its spacing as it is.
theorem freeFirst ∀ (expr: Expr)
    (within: expr.within1 = True):
    spacedFirst Free (expr.spacing False) = expr.spacing False :=
  let (rest, free) := spacingFree expr within
  rewrite free

--| What the rules' lemmas say of an expression: its element, from where its first code word may stand spaced `first`,
--| adds code words spaced as `Expr.spacing` says with `first` for the first, and ends where a comment waits only if
--| it ends with one. `argument`: it is a call's argument, as `callArgument` shapes them.
def ElSteps (expr: Expr): Prop :=
  expr.within1 = True
    → expr.shaped = True
    → expr.lexical = True
    → Joinable lexKind expr
    → ∀ (around: Around) (first: Spacing) (argument: Bool) => (argument = True → expr.callArgument = True)
      → (Loose first ∨ expr.firstWord.quietAt around around.at = True)
      → Steps (expr.el around) (Fits True first) (spacedFirst first (expr.spacing argument)) (Ends expr.trails)

--| An element that is no call's argument, its first code word free.
theorem elFree ∀ (expr: Expr) (around: Around)
    (steps: ElSteps expr)
    (within: expr.within1 = True)
    (shaped: expr.shaped = True)
    (lexical: expr.lexical = True)
    (joinable: Joinable lexKind expr):
    Steps (expr.el around) (Fits True Free) (expr.spacing False) (Ends expr.trails) :=
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
      (spacedFirst first ((Atom kind word).spacing argument))
      (Ends (Atom kind word).trails) :=
  let (_, _, _, closer) := joins
  let leadLoose: Loose first ∨ (word.leading around around.at).isEmpty = True := match loose with
    | Inl free => Inl free
    | Inr quiet => Inr (Bool.andRight quiet)
  stepsTo _ _ _ _ (wordLeafSteps word around around.at first joins leadLoose) (seam closed =>
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
    (atomic: operand.primary = True)
    (within: operand.within1 = True)
    (lexical: operand.lexical = True):
    (operand.firstWord.text == "-" || operand.numeralApplication) = False :=
  match operand with
    | Atom kind word => rewrite atomNotMinus kind word within
    | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ => rewrite DecEq.sound (Bool.andLeft lexical)

theorem numeralAtomic ∀ (operand: Expr) (numeral: operand.numeral1 = True): operand.primary = True := match operand with
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
      stepsFrom _ _ _
        (stepsTo _ _ _ _ (stepsSpace trails) (seam gapped =>
          fitsWeaker trails True (_ => byComputing) Free seam (gappedFits trails Free seam byComputing gapped)))
        (seam closed => closedEnds trails seam closed)
    | False => stepsTo _ _ _ _ (stepsNothing (Closed trails)) (seam closed =>
      fitsWeaker trails True (_ => byComputing) Free seam (endsFits trails seam (closedEnds trails seam closed)))

--| `-` and a numeral's call, a space between them.
theorem gapApart ∀ (operator: Word) (operand: Expr) (trails: Bool)
    (spaced: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = True):
    Steps (prefixGap operator operand) (Closed trails) [] (Fits True Apart) :=
  rewrite gapSpaced operator operand spaced then
    stepsFrom _ _ _
      (stepsTo _ _ _ _ (stepsSpace trails) (seam gapped =>
        fitsWeaker trails True (_ => byComputing) Apart seam (gappedFits trails Apart seam byComputing gapped)))
      (seam closed => closedEnds trails seam closed)

--| A sign with no trailing comment and nothing written after it: its operand stands glued to it.
theorem gapGlued ∀ (operator: Word) (operand: Expr)
    (tight: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = False):
    Steps (prefixGap operator operand) (Closed False) [] (Fits True Glued) :=
  rewrite gapTight operator operand tight then
    stepsTo _ _ _ _ (stepsNothing (Closed False)) (seam closed => rewrite closedAlong seam closed)

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
--| `signQuiet`, and no space: a call's argument's sign is on an atom or bracket, by `callArgument`), else free.
theorem prefixSteps ∀ (operator: Word) (operand: Expr) (around: Around) (first: Spacing) (argument: Bool)
    (within: (Prefix operator operand).within1 = True)
    (shaped: (Prefix operator operand).shaped = True)
    (lexical: (Prefix operator operand).lexical = True)
    (joinable: Joinable lexKind (Prefix operator operand))
    (isArgument: argument = True → (Prefix operator operand).callArgument = True)
    (loose: Loose first ∨ operator.quietAt around around.at = True)
    (operandSteps: ElSteps operand):
    Steps
      ((Prefix operator operand).el around)
      (Fits True first)
      (spacedFirst first ((Prefix operator operand).spacing argument))
      (Ends (Prefix operator operand).trails) :=
  let (joins, operandJoins, _) := joinable
  let (sound, _, _, _) := joins
  let operandWithin: operand.within1 = True := Bool.andLeft within
  let operandShaped: operand.shaped = True := Bool.andLeft shaped
  let operandLexical: operand.lexical = True := Bool.andRight lexical
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
        (stepsConcat _ _ _
          (stepsCons
            (operator.leaf inside around.at)
            [prefixGap operator operand, operand.el place]
            (Fits True first)
            (Closed operator.trails)
            (Ends (Prefix operator operand).trails)
            leaf
            (stepsTwo (prefixGap operator operand) _ middle _ gap (stepsTo _ _ _ _ inner ends))))
  let free: Steps (operand.el place) (Fits True Free) (operand.spacing False) (Ends operand.trails) :=
    elFree operand place operandSteps operandWithin operandShaped operandLexical operandJoins
  let glued: signQuiet operator operand = True
    → Steps (operand.el place) (Fits True Glued) (spacedFirst Glued (operand.spacing False)) (Ends operand.trails) :=
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
      [first, ..spacedFirst Glued (operand.spacing False)]
      (Ends (Prefix operator operand).trails) :=
    quiet tight =>
      whole _ _
        (stepsFrom _ _ _ (gapGlued operator operand tight) (seam closed =>
          closedFalse operator.trails (signQuietAfter operator operand quiet) seam closed))
        (glued quiet)
  match app: operator.text == "-" && operand.numeralApplication with
    | True =>
      let spaced: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication)) = True :=
        Bool.andIntro (Bool.andLeft app) (Bool.orRight (Bool.andRight app))
      stepsSpacing _ _ _ byComputing
        (whole _ _
          (gapApart operator operand operator.trails spaced)
          (operandSteps operandWithin operandShaped operandLexical operandJoins place Apart False
            (never => (Bool.falseNotTrue never).impossible)
            (Inl byComputing)))
    | False =>
      match quiet: signQuiet operator operand with
        | False => stepsSpacing _ _ _ byComputing (whole _ _ (gapFree operator operand operator.trails) free)
        | True =>
          match argument with
            | True =>
              let atomic: operand.primary = True := Bool.andLeft (isArgument byComputing)
              let tight: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication))
                = False :=
                Bool.andFalseRight _ _ (atomicTight operand atomic operandWithin operandLexical)
              stepsSpacing _ _ _ byComputing (gluedWhole quiet tight)
            | False =>
              match numeral: operator.text == "-" && operand.numeral1 with
                | True =>
                  let atomic := numeralAtomic operand (Bool.andRight numeral)
                  let tight: (operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication))
                    = False :=
                    Bool.andFalseRight _ _ (atomicTight operand atomic operandWithin operandLexical)
                  stepsSpacing _ _ _ byComputing (gluedWhole quiet tight)
                | False => stepsSpacing _ _ _ byComputing (whole _ _ (gapFree operator operand operator.trails) free)

-- Brackets.

theorem parenInnerSteps ∀ (inner: Expr) (place: Around) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop)
    (within: inner.within1 = True)
    (steps: Steps (inner.el place) pre spacing post):
    Steps (parenInner inner place) pre spacing post :=
  match inner with
    | Block _ _ _ | If _ _ _ _ _ _ _ => cases
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
    (shaped: (Paren open inner close).shaped = True)
    (lexical: (Paren open inner close).lexical = True)
    (joinable: Joinable lexKind (Paren open inner close))
    (loose: Loose first ∨ open.quietAt around around.at = True)
    (innerSteps: ElSteps inner):
    Steps
      ((Paren open inner close).el around)
      (Fits True first)
      (spacedFirst first ((Paren open inner close).spacing argument))
      (Ends (Paren open inner close).trails) :=
  let (opener, closer, innerJoins) := joinable
  let (closeSound, isCloser) := closer
  let inside := { around | hoisted = True }
  let innerAround := inside.next open.trails 1
  let closeAround := inside.next inner.trails (1 + inner.size)
  framedSteps open around _
    [first, ..inner.spacing False ++ [Free]] _
    first
    opener.left.left
    loose
    (stepsConcat _ _ _
      (stepsCons
        (open.opening inside close)
        [parenInner inner innerAround, close.leaf closeAround inside.at]
        (Fits True first)
        (Closed open.trails)
        (Ends (Paren open inner close).trails)
        (openingSteps open inside close first opener.left (Inr byComputing))
        (stepsTwo
          (parenInner inner innerAround)
          (Closed open.trails)
          (Ends inner.trails)
          (Ends (Paren open inner close).trails)
          (stepsFrom _ _ _
            (parenInnerSteps inner innerAround _ _ _ within
              (elFree inner innerAround innerSteps within shaped (Bool.andRight (Bool.andRight lexical)) innerJoins))
            (seam closed => closedFree open.trails seam closed))
          (stepsFrom _ _ _
            (stepsTo _ _ _ _ (closerLeafSteps close closeAround inside.at closer byComputing) (seam closed =>
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
    (∀ (place: Around) => Steps (item.el place) (Fits True Free) (item.spacing False) (Ends item.trails))
      ∧ EachFree rest

theorem eachFree ∀ (items: List Expr)
    (each: EachElSteps items)
    (within: allWithin1 items = True)
    (shaped: allShaped items = True)
    (lexical: allLexical items = True)
    (joinable: AllJoinable lexKind items):
    EachFree items :=
  match items, each, joinable with
    | [], _, _ => byComputing
    | [item, ..rest], (steps, others), (joins, restJoins) => (
      place => elFree item place steps (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft lexical) joins,
      eachFree rest others (Bool.andRight within) (Bool.andRight shaped) (Bool.andRight lexical) restJoins
    )

--| A comma after an item: it stands on the item's line, before a comment the item ends with.
theorem closingCommaSteps ∀ (trails: Bool): Steps (Closing ",") (Ends trails) [Free] (Ends trails) :=
  stepsFrom _ _ _
    (stepsTo _ _ _ _ (stepsClosing trails (byComputing, byComputing, byComputing)) (seam closed =>
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
    | False => stepsTo _ _ _ _ (stepsLine trails) (seam gapped =>
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
      (commaSpacing items)
      (Ends (trailsBack (seen ++ itemsWords items).reverse)) :=
  match items, each with
    | [], _ => stepsNil _ _ (seam ended => rewrite List.appendNil seen then ended)
    | [item], (steps, _) =>
      stepsTwo
        (if first then SoftLine else Line) _
        (Fits True Free) _
        (sepFree first (trailsBack seen.reverse))
        (stepsTo _ _ _ _ (steps (firstAround bare arm before at)) (seam ended =>
          rewrite List.appendNil item.words then itemEnds seen item seam ended))
    | [item, second, ..more], (steps, rest) =>
      stepsCons
        (if first then SoftLine else Line) _ _
        (Fits True Free) _
        (sepFree first (trailsBack seen.reverse))
        (stepsCons
          (item.el (firstAround bare arm before at)) _ _
          (Ends (trailsBack (seen ++ item.words).reverse)) _
          (stepsTo _ _ _ _ (steps (firstAround bare arm before at)) (seam ended => itemEnds seen item seam ended))
          (stepsCons
            (Closing ",") _ _
            (Ends (trailsBack (seen ++ item.words).reverse)) _
            (closingCommaSteps (trailsBack (seen ++ item.words).reverse))
            (rewrite <- List.appendAssoc seen item.words (itemsWords [second, ..more]) then
              brokenSteps (seen ++ item.words) [second, ..more] False arm False item.trails (at + item.size) rest)))

--| A filled list's cells after the first.
theorem cellsRestSteps ∀ (seen: List Word) (items: List Expr) (arm before: Bool) (at: Nat)
    (each: EachFree items):
    SepsSteps
      (cells False arm before at items)
      (Ends (trailsBack seen.reverse))
      (commaSpacing items)
      (Ends (trailsBack (seen ++ itemsWords items).reverse)) :=
  match items, each with
    | [], _ => sepsNil _ _ (seam ended => rewrite List.appendNil seen then ended)
    | [item], (steps, _) =>
      rewrite <- List.appendNil (item.spacing False) then
        sepsCons
          (item.el (firstAround False arm before at))
          [] _ _ _
          (item.spacing False)
          []
          (stepsTwo Line _
            (Fits True Free) _
            (sepFree False (trailsBack seen.reverse))
            (stepsTo _ _ _ _ (steps (firstAround False arm before at)) (seam ended =>
              rewrite List.appendNil item.words then itemEnds seen item seam ended)))
          (sepsNil _ _ (seam ended => ended))
    | [item, second, ..more], (steps, rest) =>
      rewrite <- List.appendAssoc (item.spacing False) [Free] (commaSpacing [second, ..more]) then
        sepsCons
          (Doc.concat [item.el (firstAround False arm before at), Closing ","]) _ _
          (Ends (trailsBack (seen ++ item.words).reverse)) _
          (item.spacing False ++ [Free])
          (commaSpacing [second, ..more])
          (stepsTwo Line _
            (Fits True Free) _
            (sepFree False (trailsBack seen.reverse))
            (stepsConcat _ _ _
              (stepsTwo
                (item.el (firstAround False arm before at)) _ _ _
                (stepsTo _ _ _ _ (steps (firstAround False arm before at)) (seam ended =>
                  itemEnds seen item seam ended))
                (closingCommaSteps (trailsBack (seen ++ item.words).reverse)))))
          (rewrite <- List.appendAssoc seen item.words (itemsWords [second, ..more]) then
            cellsRestSteps (seen ++ item.words) [second, ..more] arm item.trails (at + item.size) rest)

--| A filled list's cells: the first after the opener, the others each after a separator.
theorem cellsSteps ∀ (open: Word) (item: Expr) (others: List Expr) (bare arm before: Bool) (at: Nat)
    (each: EachFree [item, ..others]):
    Steps
      (Fill (cells bare arm before at [item, ..others]))
      (Ends (trailsBack [open].reverse))
      (commaSpacing [item, ..others])
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
      rewrite <- List.appendNil (item.spacing False) then
        stepsFill _ _ _
          (stepsFrom _ _ _
            (stepsTo _ _ _ _ (steps (firstAround bare arm before at)) (seam ended =>
              rewrite List.appendNil item.words then itemEnds [open] item seam ended))
            start)
          (sepsNil _ _ (seam ended => ended))
    | [second, ..more], (steps, rest) =>
      rewrite <- List.appendAssoc (item.spacing False) [Free] (commaSpacing [second, ..more]) then
        stepsFill _
          (Ends (trailsBack ([open] ++ item.words).reverse)) _
          (stepsFrom _ _ _
            (stepsConcat _ _ _
              (stepsTwo
                (item.el (firstAround bare arm before at)) _ _ _
                (stepsTo _ _ _ _ (steps (firstAround bare arm before at)) (seam ended =>
                  itemEnds [open] item seam ended))
                (closingCommaSteps (trailsBack ([open] ++ item.words).reverse))))
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
      ([first, ..commaSpacing items] ++ [Free])
      (Ends (ListOf open items False close).trails) :=
  let (closeSound, isCloser) := closer
  let notCloser := opener.right.right.right
  let whole := ListOf open items False close
  let closeAround := around.next whole.trailsBeforeClose (whole.size - 1)
  let seen := trailsBack ([open] ++ itemsWords items).reverse
  let prefixSteps: Steps (open.opening around close) (Fits True first) [first] (Ends (trailsBack [open].reverse)) :=
    stepsTo _ _ _ _ (openingSteps open around close first opener (Inr (rewrite unhoisted))) (seam closed =>
      rewrite openTrails open notCloser then closedEnds open.trails seam closed)
  let closerSteps: Steps (close.leaf closeAround around.at) (Ends seen) [Free] (Ends whole.trails) :=
    stepsFrom _ _ _
      (stepsTo _ _ _ _ (closerLeafSteps close closeAround around.at closer byComputing) (seam closed =>
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
    ([first] ++ (commaSpacing items ++ ([] ++ [Free])))
    (Ends whole.trails) :=
    stepsCons
      (open.opening around close) _ _ _ _
      prefixSteps
      (stepsCons
        (Nest 2 (Doc.concat broken)) _ _
        (Ends seen) _
        (stepsNest 2 _ _
          (stepsConcat _ _ _ (brokenSteps [open] items bare around.inArm True open.trails (around.at + 1) each)))
        (stepsTwo SoftLine _
          (Ends seen) _
          (stepsSoft _ _ (seam ended => endsQuiet seen seam ended) (seam ended => ended) byComputing)
          closerSteps))
  rewrite bracketIs list open items close around then
    match items, each with
      | [], _ =>
        stepsConcat
          [open.opening around close, close.leaf closeAround around.at] _ _
          (stepsTwo
            (open.opening around close) _
            (Ends seen) _
            (stepsTo _ _ _ _ prefixSteps (seam ended => ended))
            closerSteps)
      | [item, ..others], each =>
        match filled: list && !whole.holdsTrailingComment && [item, ..others].all Expr.plainItem with
          | True =>
            stepsConcat
              [
                open.opening around close,
                Nest 2 (Fill (cells bare around.inArm open.trails (around.at + 1) [item, ..others])),
                close.leaf closeAround around.at
              ] _ _
              (stepsCons
                (open.opening around close)
                [
                  Nest 2 (Fill (cells bare around.inArm open.trails (around.at + 1) [item, ..others])),
                  close.leaf closeAround around.at
                ] _ _ _
                prefixSteps
                (stepsTwo
                  (Nest 2 (Fill (cells bare around.inArm open.trails (around.at + 1) [item, ..others]))) _
                  (Ends seen) _
                  (stepsNest 2 _ _ (cellsSteps open item others bare around.inArm open.trails (around.at + 1) each))
                  closerSteps))
          | False =>
            match holds: whole.holdsTrailingComment with
              | True =>
                stepsConcat
                  ([open.opening around close, Nest 2 (Doc.concat broken), SoftLine, close.leaf closeAround around.at]
                    ++ [BreakParent]) _ _
                  (allSpacing _ _ _
                    (List.appendNil _)
                    (stepsAppend
                      [
                        open.opening around close,
                        Nest 2 (Doc.concat broken),
                        SoftLine,
                        close.leaf closeAround around.at
                      ] _ _ _
                      brokenSteps'
                      (stepsLast _ _ (stepsBreakParent _))))
              | False =>
                stepsConcat
                  [
                    open.opening around close,
                    Nest 2 (Doc.concat broken),
                    SoftLine,
                    close.leaf closeAround around.at
                  ] _ _
                  brokenSteps'

--| A tuple or list, `(a, b)` or `[a, b]`, filled or broken: the opener spaced `first`, then each item and comma free.
theorem commaSteps ∀ (list: Bool) (open: Word) (items: List Expr) (comma: Bool) (close: Word) (around: Around)
    (first: Spacing) (argument: Bool)
    (within: (if list then ListOf open items comma close else Tuple open items comma close).within1 = True)
    (shaped: (if list then ListOf open items comma close else Tuple open items comma close).shaped = True)
    (lexical: (if list then ListOf open items comma close else Tuple open items comma close).lexical = True)
    (joinable: Joinable lexKind (if list then ListOf open items comma close else Tuple open items comma close))
    (loose: Loose first ∨ open.quietAt around around.at = True)
    (each: EachElSteps items):
    Steps
      ((if list then ListOf open items comma close else Tuple open items comma close).el around)
      (Fits True first)
      (spacedFirst first
        ((if list then ListOf open items comma close else Tuple open items comma close).spacing argument))
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
          (bracketContent True open items close { around | hoisted = True }).forcesBreak _ _
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
          (bracketContent False open items close { around | hoisted = True }).forcesBreak _ _
          (bracketSteps False open items close
            { around | hoisted = True }
            first
            byComputing
            opener.left
            closer
            (eachFree items each within (Bool.andRight shaped) (Bool.andRight (Bool.andRight lexical)) joins)))

-- Calls.

--| A call's arguments' spacings before the last, as `argumentDocs` splits their documents.
def initSpacings: List Expr → List (List Spacing)
  | [] | [_] => []
  | [argument, ..rest] => [argument.spacing True, ..initSpacings rest]

--| A call's last argument's spacing.
def lastSpacing: List Expr → List Spacing
  | [] => []
  | [argument] => argument.spacing True
  | [_, ..rest] => lastSpacing rest

theorem argumentsJoin ∀ (arguments: List Expr)
    (filled: arguments ≠ []):
    joinSpacing (initSpacings arguments ++ [lastSpacing arguments]) = argumentsSpacing arguments :=
  match arguments with
    | [] => (filled byComputing).impossible
    | [argument] => byComputing
    | [argument, next, ..more] => rewrite argumentsJoin [next, ..more] (List.consNotNil next more)

theorem callJoin ∀ (headSpacing: List Spacing) (arguments: List Expr)
    (filled: arguments ≠ []):
    joinSpacing ([headSpacing, ..initSpacings arguments] ++ [lastSpacing arguments])
      = headSpacing ++ argumentsSpacing arguments :=
  rewrite <- argumentsJoin arguments filled

--| A call's argument starts with a sign apart from what precedes it, or with a free word.
theorem argumentStarts ∀ (argument: Expr)
    (isArgument: argument.callArgument = True):
    ∃ (start: Spacing) => Loose start ∧ spacedFirst start (argument.spacing True) = argument.spacing True :=
  match argument with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ => (Free, byComputing, byComputing)
    | Prefix operator operand =>
      match operandSpacing True operator operand with
        | Some spacing => (Apart, byComputing, byComputing)
        | None => (Apart, byComputing, byComputing)

--| A call's argument, after a space or a line break.
theorem argumentSteps ∀ (argument: Expr) (place: Around)
    (within: argument.within1 = True)
    (shaped: argument.shaped = True)
    (lexical: argument.lexical = True)
    (isArgument: argument.callArgument = True)
    (joinable: Joinable lexKind argument)
    (steps: ElSteps argument):
    Steps (argument.el place) (Gapped True) (argument.spacing True) (Ends argument.trails) :=
  let (start, loose, same) := argumentStarts argument isArgument
  stepsFrom _ _ _
    (stepsSpacing _ _ _ same (steps within shaped lexical joinable place start True (_ => isArgument) (Inl loose)))
    (seam gapped => gappedFits True start seam loose gapped)

--| A bracket as a call's last argument, as it stands and opened, after a space or a line break.
theorem huggedSteps ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around) (hard: Bool)
    (opener: WordJoins open)
    (closer: CloserJoins close)
    (each: EachFree items):
    Steps
      (framedBy open around (Group (bracketContent list open items close { around | hoisted = True }) hard))
      (Gapped True)
      ([Free, ..commaSpacing items] ++ [Free])
      (Ends (ListOf open items False close).trails) :=
  stepsFrom _ _ _
    (framedSteps open around
      (Group (bracketContent list open items close { around | hoisted = True }) hard) _ _
      Free
      opener.left
      (Inl byComputing)
      (stepsGroup hard _ _
        (bracketSteps list open items close { around | hoisted = True } Free byComputing opener closer each)))
    (seam gapped => gappedFits True Free seam byComputing gapped)

--| A call's last argument, as it stands and opened, after a space or a line break.
theorem lastArgumentSteps ∀ (argument: Expr) (place: Around)
    (within: argument.within1 = True)
    (shaped: argument.shaped = True)
    (lexical: argument.lexical = True)
    (isArgument: argument.callArgument = True)
    (joinable: Joinable lexKind argument)
    (steps: ElSteps argument):
    Steps (lastArgument argument place).fst (Gapped True) (argument.spacing True) (Ends argument.trails)
      ∧ HugSteps (lastArgument argument place).snd (Gapped True) (argument.spacing True) (Ends argument.trails) :=
  let plain := argumentSteps argument place within shaped lexical isArgument joinable steps
  match argument, joinable with
    | Tuple open items comma close, (opener, closer, joins) =>
      let each :=
        eachFree items (allElSteps items) within (Bool.andRight shaped) (Bool.andRight (Bool.andRight lexical)) joins
      let content := bracketContent False open items close { place | hoisted = True }
      (
        huggedSteps False open items close place content.forcesBreak opener.left closer each,
        huggedSteps False open items close place True opener.left closer each
      )
    | ListOf open items comma close, (opener, closer, joins) =>
      let each := eachFree items (allElSteps items) within shaped (Bool.andRight (Bool.andRight lexical)) joins
      let content := bracketContent True open items close { place | hoisted = True }
      (
        huggedSteps True open items close place content.forcesBreak opener.left closer each,
        huggedSteps True open items close place True opener.left closer each
      )
    | Atom _ _ |
        Prefix _ _ |
        Paren _ (Atom _ _) _ |
        Paren _ (Paren _ _ _) _ |
        Paren _ (Tuple _ _ _ _) _ |
        Paren _ (ListOf _ _ _ _) _ |
        Paren _ (App _ _) _ |
        Paren _ (Infix _ _ _ _) _ |
        Paren _ (Prefix _ _) _, _ => (plain, byComputing)

--| A call's arguments after its function: in order, each after a space or a line break, spaced as its own
--| `spacing True` says; the same without the last, ending where a comment may wait; the last's hug; and one
--| document before the last for each argument but one.
--|
--| Proof idea: induction on the arguments, as `Fmt.JoinProofs.argumentsSeq`, the words seen so far growing by each
--| argument's; each from `argumentSteps`, the last from `lastArgumentSteps`.
theorem argumentsSteps ∀ (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr) (seen: List Word)
    (pre: Seam → Prop) (doc: Doc) (spacing: List Spacing)
    (filled: arguments ≠ [])
    (within: allWithin1 arguments = True)
    (shaped: allShaped arguments = True)
    (lexical: allLexical arguments = True)
    (isArguments: arguments.all Expr.callArgument = True)
    (joinable: AllJoinable lexKind arguments)
    (each: EachElSteps arguments)
    (first: Steps doc pre spacing (Ends True)):
    SeqFrom pre
      (Ends (trailsBack (seen ++ itemsWords arguments).reverse))
      doc
      spacing
      ((argumentDocs arm previous at arguments).fst
        ++ [((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).fst])
      (initSpacings arguments ++ [lastSpacing arguments])
      ∧ SeqFrom pre (Ends True) doc spacing (argumentDocs arm previous at arguments).fst (initSpacings arguments)
      ∧ HugSteps
        ((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).snd
        (Gapped True)
        (lastSpacing arguments)
        (Ends (trailsBack (seen ++ itemsWords arguments).reverse))
      ∧ (argumentDocs arm previous at arguments).fst.length + 1 = arguments.length :=
  match arguments, joinable, each with
    | [], _, _ => (filled byComputing).impossible
    | [argument], (joins, _), (steps, _) =>
      let place: Around := { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
      let (last, hug) :=
        lastArgumentSteps argument place
          (Bool.andLeft within)
          (Bool.andLeft shaped)
          (Bool.andLeft lexical)
          (Bool.andLeft isArguments)
          joins
          steps
      let ends: ∀ (seam: Seam) => Ends argument.trails seam
        → Ends (trailsBack (seen ++ itemsWords [argument]).reverse) seam :=
        seam ended => rewrite List.appendNil argument.words then itemEnds seen argument seam ended
      ((first, stepsTo _ _ _ _ last ends), first, hugTo (lastArgument argument place).snd _ _ _ _ hug ends, byComputing)
    | [argument, next, ..more], (joins, rest), (steps, others) =>
      let place: Around := { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
      let element: Steps (argument.el place) (Gapped True) (argument.spacing True) (Ends True) :=
        stepsTo _ _ _ _
          (argumentSteps argument place
            (Bool.andLeft within)
            (Bool.andLeft shaped)
            (Bool.andLeft lexical)
            (Bool.andLeft isArguments)
            joins
            steps)
          (seam ended => endsWeaker argument.trails True (_ => byComputing) seam ended)
      let (seq, frontSeq, hugs, length) :=
        argumentsSteps arm argument
          (at + argument.size)
          [next, ..more]
          (seen ++ argument.words)
          (Gapped True)
          (argument.el place)
          (argument.spacing True)
          (List.consNotNil next more)
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight lexical)
          (Bool.andRight isArguments)
          rest
          others
          element
      (
        (first, rewrite List.appendAssoc seen argument.words (itemsWords [next, ..more]) at seq then seq),
        (first, frontSeq),
        rewrite List.appendAssoc seen argument.words (itemsWords [next, ..more]) at hugs then hugs,
        arithmetic [length]
      )

theorem appFirstWord ∀ (head: Expr) (arguments: List Expr)
    (within: (App head arguments).within1 = True)
    (headWithin: head.within1 = True):
    (App head arguments).firstWord = head.firstWord :=
  rewrite firstWordLead (App head arguments) within, firstWordLead head headWithin

--| A call, its head spaced `first` and each argument as `argumentsSpacing` says (`spacing True`: free, or apart
--| for a sign), every argument after a space, a fill separator or a `HardLine`.
--|
--| Proof idea: `appFromSteps` (`Fmt.TouchSeq`), as `Fmt.JoinProofs.appPasses`: the head from `elSteps`, then the
--| arguments in order (`argumentsSteps`), each from `elSteps` with `callArgument` from `shaped`; the hug as the last
--| argument opened.
theorem appSteps ∀ (head: Expr) (arguments: List Expr) (around: Around) (first: Spacing) (argument: Bool)
    (within: (App head arguments).within1 = True)
    (shaped: (App head arguments).shaped = True)
    (lexical: (App head arguments).lexical = True)
    (joinable: Joinable lexKind (App head arguments))
    (loose: Loose first ∨ (App head arguments).firstWord.quietAt around around.at = True)
    (headSteps: ElSteps head)
    (each: EachElSteps arguments):
    Steps
      ((App head arguments).el around)
      (Fits True first)
      (spacedFirst first ((App head arguments).spacing argument))
      (Ends (App head arguments).trails) :=
  let (headJoins, joins, filled) := joinable
  let headWithin: head.within1 = True := Bool.andLeft within
  let headShaped: head.shaped = True := Bool.andLeft (Bool.andRight shaped)
  let isArguments: arguments.all Expr.callArgument = True :=
    Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight shaped)))
  let argumentsShaped: allShaped arguments = True :=
    Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight shaped)))
  let inside := { around | hoisted = True }
  let lead := leadJoins lexKind (App head arguments) joinable
  let sound: (App head arguments).firstWord.sound = True :=
    rewrite firstWordLead (App head arguments) within then lead.left
  let headLoose: Loose first ∨ head.firstWord.quietAt inside inside.at = True := match loose with
    | Inl free => Inl free
    | Inr quiet =>
      let headQuiet := rewrite appFirstWord head arguments within headWithin at quiet then quiet
      Inr (Bool.andIntro (Bool.andLeft headQuiet) byComputing)
  let headSpacing := spacedFirst first (head.spacing False)
  let headEl: Steps (head.el inside) (Fits True first) headSpacing (Ends True) :=
    stepsTo _ _ _ _
      (headSteps headWithin headShaped
        (Bool.andLeft lexical)
        headJoins
        inside
        first
        False
        (never => (Bool.falseNotTrue never).impossible)
        headLoose)
      (seam ended => endsWeaker head.trails True (_ => byComputing) seam ended)
  let results := argumentDocs inside.inArm head (inside.at + head.size) arguments
  let front := results.fst
  let lastDoc := (results.snd.getOrElse (Nothing, None)).fst
  let (seq, frontSeq, hugs, length) :=
    argumentsSteps inside.inArm head
      (inside.at + head.size)
      arguments
      head.words
      (Fits True first)
      (head.el inside)
      headSpacing
      filled
      (Bool.andRight within)
      argumentsShaped
      (Bool.andRight lexical)
      isArguments
      joins
      each
      headEl
  let short: 1 + keptFront head arguments ≤ ([head.el inside, ..front] ++ [lastDoc]).length :=
    rewrite List.lengthAppend front [lastDoc] then arithmetic [keptShort head arguments, length]
  let (rest, free) := spacingFree head headWithin
  let same: joinSpacing ([headSpacing, ..initSpacings arguments] ++ [lastSpacing arguments])
    = spacedFirst first ((App head arguments).spacing argument) :=
    rewrite callJoin headSpacing arguments filled, free
  framedSteps
    (App head arguments).firstWord
    around
    (appDocs head arguments inside).doc
    (spacedFirst first ((App head arguments).spacing argument))
    (Ends (App head arguments).trails)
    first
    sound
    loose
    (rewrite appDocsIsOneFirst head arguments inside then
      stepsSpacing _ _ _ same
        (appFromSteps
          (inside.at + 1)
          (1 + keptFront head arguments)
          (commentBetween head arguments)
          (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
          (head.el inside)
          lastDoc
          front
          (results.snd.getOrElse (Nothing, None)).snd
          headSpacing
          (lastSpacing arguments)
          (initSpacings arguments)
          (Fits True first)
          (Ends (App head arguments).trails)
          seq
          frontSeq
          hugs
          (arithmetic)
          short))

-- Chains.

--| A chain's first link and the rest, the rest nested.
theorem headTailSteps ∀ (head: Doc) (tail: List Doc) (indent: Nat) (pre: Seam → Prop)
    (spacing: List Spacing) (post: Seam → Prop)
    (all: StepsAll [head, ..tail] pre spacing post):
    Steps (Doc.concat [head, Nest indent (Doc.concat tail)]) pre spacing post :=
  stepsConcat [head, Nest indent (Doc.concat tail)] pre post (seam trace next holds after =>
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
      stepsGroup joined.forcesBreak pre post (headTailSteps head tail (if arms then 0 else 2) pre spacing post all)

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
    (shaped: right.shaped = True)
    (lexical: right.lexical = True)
    (joinable: Joinable lexKind right) (ends: ∀ (seam: Seam) => Ends right.trails seam → post seam):
    StepsAll (chainRight level right place) (Ends trails) (spacedFirst Apart (right.spacing False)) post :=
  let rest := linkSteps level False right place Apart within shaped lexical joinable (Inl byComputing)
  match right with
    | Block _ _ _ => cases
    | _ =>
      stepsCons
        (Doc.text " ") _
        (Ends trails)
        (Fits True Apart)
        post
        (stepsTo _ _ _ _ (stepsSpace trails) (seam gapped =>
          fitsWeaker trails True (_ => byComputing) Apart seam (gappedFits trails Apart seam byComputing gapped)))
        (allTo _ _ _ _ rest ends)

--| A chain's links: its first operand's, then each operator after a line break and its operand after a space.
theorem chainLinksSteps ∀ (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (start: Spacing)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftShaped: left.shaped = True)
    (rightShaped: right.shaped = True)
    (leftLexical: left.lexical = True)
    (rightLexical: right.lexical = True)
    (leftJoins: Joinable lexKind left)
    (operatorJoins: WordJoins operator)
    (rightJoins: Joinable lexKind right)
    (loose: Loose start ∨ left.firstWord.quietAt around around.at = True):
    StepsAll
      (chainLinks level first left operator right around)
      (Fits True start)
      (spacedFirst start (left.spacing False) ++ [Free, ..spacedFirst Apart (right.spacing False)])
      (Ends (trailsBack (left.words ++ [operator, ..right.words]).reverse)) :=
  let operatorAround := around.next left.trails left.size
  let rightAround := around.next operator.trails (left.size + 1)
  stepsAppend
    (linkDocs level first left around) _
    (Ends left.trails) _
    (linkSteps level first left around start leftWithin leftShaped leftLexical leftJoins loose)
    (stepsCons Line _ _
      (Fits True Free) _
      (stepsTo _ _ _ _ (stepsLine left.trails) (seam gapped =>
        fitsWeaker left.trails True (_ => byComputing) Free seam (gappedFits left.trails Free seam byComputing gapped)))
      (stepsCons
        (operator.leaf operatorAround operatorAround.at) _ _
        (Ends operator.trails) _
        (stepsTo _ _ _ _
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
    (shaped: (Infix kind left operator right).shaped = True)
    (lexical: (Infix kind left operator right).lexical = True)
    (joinable: Joinable lexKind (Infix kind left operator right))
    (loose: Loose start ∨ (Infix kind left operator right).firstWord.quietAt around around.at = True)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True):
    StepsAll
      (chainLinks level first left operator right around)
      (Fits True start)
      (spacedFirst start ((Infix kind left operator right).spacing False))
      (Ends (Infix kind left operator right).trails) :=
  let (leftJoins, operatorJoins, rightJoins) := joinable
  let (rest, free) := spacingFree left leftWithin
  allSpacing _ _ _
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
    (shaped: expr.shaped = True)
    (lexical: expr.lexical = True)
    (joinable: Joinable lexKind expr)
    (loose: Loose start ∨ expr.firstWord.quietAt around around.at = True):
    StepsAll
      (linkDocs level first expr around)
      (Fits True start)
      (spacedFirst start (expr.spacing False))
      (Ends expr.trails) :=
  let element: StepsAll
    [expr.el around]
    (Fits True start)
    (spacedFirst start (expr.spacing False))
    (Ends expr.trails) :=
    stepsLast _ _
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
    (shaped: (Infix kind left operator right).shaped = True)
    (lexical: (Infix kind left operator right).lexical = True)
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
      (spacedFirst first ((Infix kind left operator right).spacing argument))
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
    (shaped: (Infix kind left operator right).shaped = True)
    (lexical: (Infix kind left operator right).lexical = True)
    (joinable: Joinable lexKind (Infix kind left operator right))
    (loose: Loose first ∨ (Infix kind left operator right).firstWord.quietAt around around.at = True):
    Steps
      ((Infix kind left operator right).el around)
      (Fits True first)
      (spacedFirst first ((Infix kind left operator right).spacing argument))
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

-- A call's hug on a `:=` line.

--| A value's hug, if it is a call that hugs: its function free, then its arguments as `argumentsSpacing` says.
theorem callHugSteps ∀ (value: Expr) (inside: Around)
    (within: value.within1 = True)
    (shaped: value.shaped = True)
    (lexical: value.lexical = True)
    (joinable: Joinable lexKind value):
    HugSteps (value.callHug inside) (Fits True Free) (value.spacing False) (Ends value.trails) :=
  match value, joinable with
    | App head arguments, (headJoins, joins, filled) =>
      let headWithin: head.within1 = True := Bool.andLeft within
      let headShaped: head.shaped = True := Bool.andLeft (Bool.andRight shaped)
      let isArguments: arguments.all Expr.callArgument = True :=
        Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight shaped)))
      let argumentsShaped: allShaped arguments = True :=
        Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight shaped)))
      let headSpacing := spacedFirst Free (head.spacing False)
      let headEl: Steps (head.el inside) (Fits True Free) headSpacing (Ends True) :=
        stepsTo _ _ _ _
          (elSteps head headWithin headShaped
            (Bool.andLeft lexical)
            headJoins
            inside
            Free
            False
            (never => (Bool.falseNotTrue never).impossible)
            (Inl byComputing))
          (seam ended => endsWeaker head.trails True (_ => byComputing) seam ended)
      let results := argumentDocs inside.inArm head (inside.at + head.size) arguments
      let (_, frontSeq, hugs, _) :=
        argumentsSteps inside.inArm head
          (inside.at + head.size)
          arguments
          head.words
          (Fits True Free)
          (head.el inside)
          headSpacing
          filled
          (Bool.andRight within)
          argumentsShaped
          (Bool.andRight lexical)
          isArguments
          joins
          (allElSteps arguments)
          headEl
      let same: joinSpacing ([headSpacing, ..initSpacings arguments] ++ [lastSpacing arguments])
        = (App head arguments).spacing False :=
        rewrite callJoin headSpacing arguments filled, freeFirst head headWithin
      rewrite appDocsIsOneFirst head arguments inside, <- same then
        appFromHugSteps
          (inside.at + 1)
          (1 + keptFront head arguments)
          (commentBetween head arguments)
          (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
          (head.el inside)
          (results.snd.getOrElse (Nothing, None)).fst
          results.fst
          (results.snd.getOrElse (Nothing, None)).snd
          headSpacing
          (lastSpacing arguments)
          (initSpacings arguments) _ _
          frontSeq
          hugs
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | Infix _ _ _ _ | Prefix _ _, _ => byComputing
