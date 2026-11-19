--| What the rules' documents do to `laysKinds` (SW-4109, `doc1Checks`' walk): from a place that has words on its line, or
--| a comment waiting only where the code before ends its line with one, each element's document passes the check and
--| leaves a place with words on its line.
namespace Fmt.LaysRules
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Expr, Note, Word)
import Fmt (..)
import Fmt.LaysKinds (..)
import Fmt.DeclFactsProofs (commentIs)
import Fmt.SpellProofs (afterSound, notesSound)
import Fmt.HangProofs (solidLine, solidSpaces)

--| Where an element may start: not at the start of the output, and with a comment waiting only if the code before
--| ends its line with one (`before`).
def Calm (kinds: Kinds) (before: Bool): Bool := !kinds.start && (!kinds.held || before)

--| Where an element leaves the printer: words on its line, and a comment waiting only if the element ends its line
--| with one (`trails`).
def Ends (kinds: Kinds) (trails: Bool): Bool := !kinds.start && !kinds.broken && (!kinds.held || trails)

--| `doc` passes the check from every place `pre` holds of, leaving one `post` holds of.
def Step (doc: Doc) (pre post: Kinds → Bool): Prop :=
  ∀ (kinds: Kinds) => pre kinds = True → ∃ (after: Kinds) => laysKinds doc kinds = Some after ∧ post after = True

def StepAll (docs: List Doc) (pre post: Kinds → Bool): Prop :=
  ∀ (kinds: Kinds) => pre kinds = True → ∃ (after: Kinds) => laysAllKinds docs kinds = Some after ∧ post after = True

theorem stepAllNil ∀ (pre: Kinds → Bool): StepAll [] pre pre := kinds holds => (kinds, byComputing, holds)

theorem stepAllCons ∀ (doc: Doc) (docs: List Doc) (pre middle post: Kinds → Bool)
    (first: Step doc pre middle)
    (rest: StepAll docs middle post):
    StepAll [doc, ..docs] pre post :=
  kinds holds =>
    match first kinds holds with
      | (between, found, good) =>
        match rest between good with
          | (after, foundRest, goodRest) => (after, rewrite found then foundRest, goodRest)

--| The check on two lists of documents, the second from where the first leaves.
theorem laysAllAppend ∀ (front back: List Doc) (kinds after: Kinds)
    (found: laysAllKinds front kinds = Some after):
    laysAllKinds (front ++ back) kinds = laysAllKinds back after :=
  match front, found with
    | [], found => rewrite <- Option.someInjective found
    | [doc, ..rest], found =>
      match one: laysKinds doc kinds, found with
        | None, never => cases
        | Some between, found => laysAllAppend rest back between after found

theorem stepAllAppend ∀ (front back: List Doc) (pre middle post: Kinds → Bool)
    (first: StepAll front pre middle)
    (second: StepAll back middle post):
    StepAll (front ++ back) pre post :=
  kinds holds =>
    match first kinds holds with
      | (between, found, good) =>
        match second between good with
          | (after, foundBack, goodBack) =>
            (after, rewrite laysAllAppend front back kinds between found then foundBack, goodBack)

theorem stepConcat ∀ (docs: List Doc) (pre post: Kinds → Bool)
    (all: StepAll docs pre post):
    Step (Concat docs) pre post :=
  kinds holds => all kinds holds

theorem stepWeaken ∀ (doc: Doc) (pre pre' post post': Kinds → Bool)
    (step: Step doc pre post)
    (before: ∀ (kinds: Kinds) => pre' kinds = True → pre kinds = True)
    (after: ∀ (kinds: Kinds) => post kinds = True → post' kinds = True):
    Step doc pre' post' :=
  kinds holds => match step kinds (before kinds holds) with | (left, found, good) => (left, found, after left good)

--| The wrappers that only pass the check on.
theorem stepNest ∀ (indent: Nat) (doc: Doc) (pre post: Kinds → Bool)
    (step: Step doc pre post):
    Step (Nest indent doc) pre post :=
  step

theorem stepGroup ∀ (doc: Doc) (hard: Bool) (pre post: Kinds → Bool)
    (step: Step doc pre post):
    Step (Group doc hard) pre post :=
  step

theorem stepFlatten ∀ (doc: Doc) (pre post: Kinds → Bool) (step: Step doc pre post): Step (Flatten doc) pre post := step

-- Places.

def Anything (kinds: Kinds): Bool := True

def NotStart (kinds: Kinds): Bool := !kinds.start

def NoHeld (kinds: Kinds): Bool := !kinds.held

--| A line start, with no comment waiting.
def Fresh (kinds: Kinds): Bool := !kinds.start && !kinds.held

--| Words on the line, no comment waiting.
def Plain (kinds: Kinds): Bool := !kinds.start && !kinds.broken && !kinds.held

theorem plainEnds ∀ (kinds: Kinds) (trails: Bool) (plain: Plain kinds = True): Ends kinds trails = True :=
  match kinds with | { start = False, broken = False, mid, held = False } => byComputing

-- Pieces.

--| A word that is no layout writes `{ mid }` from any place.
theorem textKinds ∀ (text: Text)
    (solid: isLayout text = False) (kinds: Kinds):
    laysKinds (Doc.text text) kinds = Some { Kinds.none | mid = True } :=
  rewrite wordFilled text solid, solidSpaces text solid, solidLine text solid

theorem stepText ∀ (text: Text) (solid: isLayout text = False): Step (Doc.text text) Anything Plain := kinds holds =>
  ({ Kinds.none | mid = True }, textKinds text solid kinds, byComputing)

theorem stepBreakParent ∀ (pre: Kinds → Bool): Step BreakParent pre pre := kinds holds => (kinds, byComputing, holds)

theorem stepHardLine: Step HardLine (kinds => kinds.midLine) Fresh := kinds holds =>
  match kinds, holds with
    | { start = False, broken = False, mid, held }, _ => ({ Kinds.none | broken = True }, byComputing, byComputing)

theorem stepBlank: Step Blank Fresh NoHeld := kinds holds =>
  match kinds, holds with
    | { start = False, broken, mid, held = False }, _ =>
      ({ start = broken, broken = False, mid, held = False }, byComputing, byComputing)

theorem stepLineStart: Step LineStart NotStart Fresh := kinds holds =>
  match kinds, holds with
    | { start = False, broken, mid, held }, _ =>
      ({ start = False, broken = broken || mid || held, mid = False, held = False }, byComputing, byComputing)

theorem stepLineStartHere: Step LineStartHere NotStart Fresh := kinds holds =>
  match kinds, holds with
    | { start = False, broken, mid, held }, _ =>
      ({ start = False, broken = broken || mid || held, mid = False, held = False }, byComputing, byComputing)

theorem stepCloserLine ∀ (key: Nat): Step (CloserLine key) NotStart Fresh := kinds holds =>
  match kinds, holds with
    | { start = False, broken, mid, held }, _ =>
      ({ start = False, broken = broken || mid || held, mid = False, held = False }, byComputing, byComputing)

theorem stepAllOne ∀ (doc: Doc) (pre post: Kinds → Bool) (step: Step doc pre post): StepAll [doc] pre post :=
  stepAllCons doc [] pre post post step (stepAllNil post)

theorem stepAllWeaken ∀ (docs: List Doc) (pre pre' post post': Kinds → Bool)
    (step: StepAll docs pre post)
    (before: ∀ (kinds: Kinds) => pre' kinds = True → pre kinds = True)
    (after: ∀ (kinds: Kinds) => post kinds = True → post' kinds = True):
    StepAll docs pre' post' :=
  kinds holds => match step kinds (before kinds holds) with | (left, found, good) => (left, found, after left good)

theorem plainMid ∀ (kinds: Kinds) (plain: Plain kinds = True): kinds.midLine = True := match kinds, plain with
  | { start = False, broken = False, mid, held = False }, _ => byComputing

theorem plainFresh ∀ (kinds: Kinds) (plain: Plain kinds = True): Fresh kinds = True := match kinds, plain with
  | { start = False, broken = False, mid, held = False }, _ => byComputing

theorem freshNotStart ∀ (kinds: Kinds) (fresh: Fresh kinds = True): NotStart kinds = True := match kinds, fresh with
  | { start = False, broken, mid, held = False }, _ => byComputing

theorem freshNoHeld ∀ (kinds: Kinds) (fresh: Fresh kinds = True): NoHeld kinds = True := match kinds, fresh with
  | { start = False, broken, mid, held = False }, _ => byComputing

theorem anything ∀ (kinds: Kinds): Anything kinds = True := byComputing

-- Own-line comments.

--| An optional blank line, from a line start with no comment waiting.
theorem blankOpt ∀ (flag: Bool): StepAll (if flag then [Blank] else []) Fresh NoHeld := match flag with
  | True => stepAllOne Blank Fresh NoHeld stepBlank
  | False => kinds holds =>
    match kinds, holds with
      | { start = False, broken, mid, held = False }, _ =>
        ({ start = False, broken, mid, held = False }, byComputing, byComputing)

--| A comment and its line break, from words on the line.
theorem stepNoteLine ∀ (text: Text) (solid: isLayout text = False): StepAll [Doc.text text, HardLine] Anything Fresh :=
  stepAllCons
    (Doc.text text)
    [HardLine]
    Anything
    Plain
    Fresh
    (stepText text solid)
    (stepAllOne HardLine Plain Fresh
      (stepWeaken HardLine (kinds => kinds.midLine) Plain Fresh Fresh stepHardLine plainMid (kinds good => good)))

--| `notesAbove`: each comment on a line of its own, from a line start with no comment waiting.
theorem notesAboveStep ∀ (keep: Bool) (notes: List Note)
    (sound: notesSound notes = True):
    StepAll (notesAbove keep notes) Fresh Fresh :=
  match notes with
    | [] => stepAllNil Fresh
    | [note, ..rest] =>
      stepAllAppend
        (if note.blankBefore && keep then [Blank] else [])
        ([Doc.text note.text, HardLine] ++ notesAbove True rest)
        Fresh
        NoHeld
        Fresh
        (blankOpt (note.blankBefore && keep))
        (stepAllAppend
          [Doc.text note.text, HardLine]
          (notesAbove True rest)
          NoHeld
          Fresh
          Fresh
          (stepAllWeaken
            [Doc.text note.text, HardLine]
            Anything
            NoHeld
            Fresh
            Fresh
            (stepNoteLine note.text (commentIs note.text (Bool.andLeft sound)).right)
            (kinds good => anything kinds)
            (kinds good => good))
          (notesAboveStep True rest (Bool.andRight sound)))

--| `laterCloserNotes`: the comments after the first, each below the one before.
theorem laterNotesStep ∀ (notes: List Note)
    (sound: notesSound notes = True):
    StepAll (laterCloserNotes notes) Plain Plain :=
  match notes with
    | [] => stepAllNil Plain
    | [note, ..rest] =>
      stepAllAppend
        [HardLine]
        ((if note.blankBefore then [Blank] else []) ++ [Doc.text note.text] ++ laterCloserNotes rest)
        Plain
        Fresh
        Plain
        (stepAllOne HardLine Plain Fresh
          (stepWeaken HardLine (kinds => kinds.midLine) Plain Fresh Fresh stepHardLine plainMid (kinds good => good)))
        (stepAllAppend
          (if note.blankBefore then [Blank] else [])
          ([Doc.text note.text] ++ laterCloserNotes rest)
          Fresh
          NoHeld
          Plain
          (blankOpt note.blankBefore)
          (stepAllAppend
            [Doc.text note.text]
            (laterCloserNotes rest)
            NoHeld
            Plain
            Plain
            (stepAllWeaken
              [Doc.text note.text]
              Anything
              NoHeld
              Plain
              Plain
              (stepAllOne
                (Doc.text note.text)
                Anything
                Plain
                (stepText note.text (commentIs note.text (Bool.andLeft sound)).right))
              (kinds good => anything kinds)
              (kinds good => good))
            (laterNotesStep rest (Bool.andRight sound))))

--| `closerNotes`: the comments before a closer, ending on the last one's line.
theorem closerNotesStep ∀ (first: Note) (rest: List Note)
    (sound: notesSound [first, ..rest] = True):
    StepAll (closerNotes [first, ..rest]) Anything Plain :=
  stepAllCons
    (Doc.text first.text)
    (laterCloserNotes rest)
    Anything
    Plain
    Plain
    (stepText first.text (commentIs first.text (Bool.andLeft sound)).right)
    (laterNotesStep rest (Bool.andRight sound))

-- A token's leading documents.

--| After a token's own-line comments, a comment is waiting only if the code before ends its line with one, and the
--| token is no closer that holds own-line comments (`flag`: those start a line of their own).
def LeadHeld (flag before: Bool) (kinds: Kinds): Bool := !kinds.held || (before && !flag)

theorem noHeldLead ∀ (flag before: Bool) (kinds: Kinds)
    (clear: NoHeld kinds = True):
    LeadHeld flag before kinds = True :=
  match kinds, clear with | { start, broken, mid, held = False }, _ => byComputing

theorem leadBool ∀ (held before flag: Bool)
    (calm: (!held || before) = True)
    (unnoted: flag = False):
    (!held || (before && !flag)) = True :=
  match held, before, flag, calm, unnoted with
    | False, _, False, _, _ => byComputing
    | True, True, False, _, _ => byComputing

theorem calmLead ∀ (flag before: Bool) (kinds: Kinds)
    (calm: Calm kinds before = True)
    (unnoted: flag = False):
    LeadHeld flag before kinds = True :=
  match kinds, calm with | { start = False, broken, mid, held }, calm => leadBool held before flag calm unnoted

theorem calmNotStart ∀ (kinds: Kinds) (before: Bool) (calm: Calm kinds before = True): NotStart kinds = True :=
  match kinds, calm with | { start = False, broken, mid, held }, _ => byComputing

theorem plainNotStart ∀ (kinds: Kinds) (plain: Plain kinds = True): NotStart kinds = True :=
  freshNotStart kinds (plainFresh kinds plain)

-- `Doc.concat` is the check on its documents one after another.

theorem filterKinds ∀ (docs: List Doc) (kinds: Kinds):
    laysAllKinds (docs.filter (doc => not doc.isEmpty)) kinds = laysAllKinds docs kinds :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] =>
      match empty: doc.isEmpty with
        | True =>
          match doc, empty with
            | Doc.Nothing, _ => filterKinds rest kinds
        | False =>
          match found: laysKinds doc kinds with
            | None => byComputing
            | Some after => filterKinds rest after

theorem allSingle ∀ (doc: Doc) (kinds: Kinds): laysAllKinds [doc] kinds = laysKinds doc kinds :=
  match found: laysKinds doc kinds with
    | None => byComputing
    | Some after => byComputing

theorem concatKinds ∀ (docs: List Doc) (kinds: Kinds): laysKinds (Doc.concat docs) kinds = laysAllKinds docs kinds :=
  let kept := filterKinds docs kinds
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] => Eq.trans (allSingle only kinds).flipped kept
    | [first, second, ..rest] => kept

theorem stepDocConcat ∀ (docs: List Doc) (pre post: Kinds → Bool)
    (all: StepAll docs pre post):
    Step (Doc.concat docs) pre post :=
  kinds holds =>
    match all kinds holds with | (after, found, good) => (after, Eq.trans (concatKinds docs kinds) found, good)

--| A closer's own-line comments, then its line.
theorem closerLeadStep ∀ (first: Note) (rest: List Note) (key: Nat) (before: Bool)
    (sound: notesSound [first, ..rest] = True):
    StepAll
      [BreakParent, Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]), CloserLine key]
      (kinds => Calm kinds before)
      (LeadHeld True before) :=
  stepAllCons BreakParent
    [Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]), CloserLine key]
    (kinds => Calm kinds before)
    (kinds => Calm kinds before)
    (LeadHeld True before)
    (stepBreakParent _)
    (stepAllCons
      (Nest 2 (Doc.concat [LineStartHere, ..closerNotes [first, ..rest]]))
      [CloserLine key]
      (kinds => Calm kinds before)
      Plain
      (LeadHeld True before)
      (stepNest 2 _ _ _
        (stepDocConcat _ _ _
          (stepAllCons LineStartHere
            (closerNotes [first, ..rest])
            (kinds => Calm kinds before)
            Fresh
            Plain
            (stepWeaken LineStartHere NotStart
              (kinds => Calm kinds before)
              Fresh
              Fresh
              stepLineStartHere
              (kinds good => calmNotStart kinds before good)
              (kinds good => good))
            (stepAllWeaken
              (closerNotes [first, ..rest])
              Anything
              Fresh
              Plain
              Plain
              (closerNotesStep first rest sound)
              (kinds good => anything kinds)
              (kinds good => good)))))
      (stepAllOne
        (CloserLine key)
        Plain
        (LeadHeld True before)
        (stepWeaken
          (CloserLine key)
          NotStart
          Plain
          Fresh
          (LeadHeld True before)
          (stepCloserLine key)
          (kinds good => plainNotStart kinds good)
          (kinds good => noHeldLead _ _ kinds (freshNoHeld kinds good)))))

--| A token's own-line comments, each on its line, then a kept blank line below them.
theorem notedLeadStep ∀ (item blankBefore: Bool) (first: Note) (rest: List Note) (before: Bool)
    (sound: notesSound [first, ..rest] = True):
    StepAll
      ([BreakParent, LineStart, ..notesAbove item [first, ..rest]] ++ (if blankBefore then [Blank] else []))
      (kinds => Calm kinds before)
      (LeadHeld False before) :=
  stepAllCons BreakParent
    ([LineStart, ..notesAbove item [first, ..rest]] ++ (if blankBefore then [Blank] else []))
    (kinds => Calm kinds before)
    (kinds => Calm kinds before)
    (LeadHeld False before)
    (stepBreakParent _)
    (stepAllCons LineStart
      (notesAbove item [first, ..rest] ++ (if blankBefore then [Blank] else []))
      (kinds => Calm kinds before)
      Fresh
      (LeadHeld False before)
      (stepWeaken LineStart NotStart
        (kinds => Calm kinds before)
        Fresh
        Fresh
        stepLineStart
        (kinds good => calmNotStart kinds before good)
        (kinds good => good))
      (stepAllAppend
        (notesAbove item [first, ..rest])
        (if blankBefore then [Blank] else [])
        Fresh
        Fresh
        (LeadHeld False before)
        (notesAboveStep item [first, ..rest] sound)
        (stepAllWeaken
          (if blankBefore then [Blank] else [])
          Fresh
          Fresh
          NoHeld
          (LeadHeld False before)
          (blankOpt blankBefore)
          (kinds good => good)
          (kinds good => noHeldLead _ _ kinds good))))

--| What a token writes before its text leaves a place where a comment waits only as `LeadHeld` says.
--|
--| Proof idea: by cases on whether an enclosing element wrote the own-line comments, whether there are any, and
--| whether the token is a closer: a kept blank line or own-line comments start a line (`LineStart`, `CloserLine`),
--| which clears the waiting comment; otherwise nothing is written.
theorem leadingStep ∀ (text: Text) (above: List Note) (after: Option Text) (blankBefore: Bool)
    (around: Around) (key: Nat)
    (sound: notesSound above = True)
    (home: isCloserText text = True → around.hoisted = False):
    StepAll
      (Word.leading ({ text, comments = { above, after, blankBefore } }) around key)
      (kinds => Calm kinds around.before)
      (LeadHeld (!above.isEmpty && isCloserText text) around.before) :=
  match above, around.hoisted, home with
    | above, True, home =>
      match above, isCloserText text, home with
        | _, True, home => (Bool.falseNotTrue (home byComputing).flipped).impossible
        | [], False, _ => kinds holds => (kinds, byComputing, calmLead _ around.before kinds holds byComputing)
        | [first, ..rest], False, _ => kinds holds =>
          (kinds, byComputing, calmLead _ around.before kinds holds byComputing)
    | [], False, _ =>
      match around.item && blankBefore with
        | True =>
          stepAllCons BreakParent
            [LineStart, Blank]
            (kinds => Calm kinds around.before)
            (kinds => Calm kinds around.before)
            (LeadHeld (!([]: List Note).isEmpty && isCloserText text) around.before)
            (stepBreakParent _)
            (stepAllCons LineStart
              [Blank]
              (kinds => Calm kinds around.before)
              Fresh
              (LeadHeld (!([]: List Note).isEmpty && isCloserText text) around.before)
              (stepWeaken LineStart NotStart
                (kinds => Calm kinds around.before)
                Fresh
                Fresh
                stepLineStart
                (kinds good => calmNotStart kinds around.before good)
                (kinds good => good))
              (stepAllWeaken
                [Blank]
                Fresh
                Fresh
                NoHeld
                (LeadHeld (!([]: List Note).isEmpty && isCloserText text) around.before)
                (stepAllOne Blank Fresh NoHeld stepBlank)
                (kinds good => good)
                (kinds good => noHeldLead _ _ kinds good)))
        | False => kinds holds => (kinds, byComputing, calmLead _ around.before kinds holds byComputing)
    | [first, ..rest], False, _ =>
      match isCloserText text with
        | True => closerLeadStep first rest key around.before sound
        | False => notedLeadStep around.item blankBefore first rest around.before sound

-- A token's text and trailing comment.

--| A closer or comma written from any place leaves words on the line, and the waiting comment where it was.
theorem closingKinds ∀ (text: Text)
    (solid: isLayout text = False)
    (closes: closesText text = True) (kinds: Kinds):
    laysKinds (Closing text) kinds = Some { start = False, broken = False, mid = True, held = kinds.held } :=
  match kinds with
    | { start, broken, mid, held = True } =>
      rewrite closes, wordFilled text solid, solidSpaces text solid, solidLine text solid
    | { start, broken, mid, held = False } =>
      rewrite closes, wordFilled text solid, solidSpaces text solid, solidLine text solid

--| A trailing comment, written after words with no comment waiting, waits.
theorem suffixKinds ∀ (comment: Text)
    (is: commentText comment = True) (kinds: Kinds)
    (plain: Plain kinds = True):
    laysKinds (LineSuffix comment) kinds = Some { Kinds.none | held = True } :=
  match kinds, plain with | { start = False, broken = False, mid, held = False }, _ => rewrite is

--| What a token writes after its own-line comments: a line of its own for a closer that holds a comment after code
--| that ends its line with one, its text and its trailing comment.
def leafRest (text: Text) (noted: Bool) (after: Option Text) (before: Bool) (key: Nat): List Doc :=
  (if isCloserText text && !noted && before && after.isSome then [CloserLine key] else [])
    ++ [piece text]
    ++ (match after with
      | Some comment => [LineSuffix comment]
      | None => [])

theorem plainTailNone ∀ (text: Text) (noted before: Bool) (key: Nat) (kinds: Kinds)
    (solid: isLayout text = False)
    (comma: (text == ",") = False)
    (open: isCloserText text = False):
    laysAllKinds (leafRest text noted None before key) kinds = Some { Kinds.none | mid = True } :=
  rewrite open, comma, textKinds text solid kinds

theorem plainTailSome ∀ (text: Text) (noted: Bool) (comment: Text) (before: Bool) (key: Nat) (kinds: Kinds)
    (solid: isLayout text = False)
    (comma: (text == ",") = False)
    (open: isCloserText text = False)
    (is: commentText comment = True):
    laysAllKinds (leafRest text noted (Some comment) before key) kinds = Some { Kinds.none | held = True } :=
  rewrite open, comma, textKinds text solid kinds, suffixKinds comment is { Kinds.none | mid = True } byComputing

--| A token that is no closer leaves words on its line, with its trailing comment waiting if it has one.
theorem plainTail ∀ (text: Text) (noted: Bool) (after: Option Text) (before: Bool) (key: Nat) (kinds: Kinds)
    (solid: isLayout text = False)
    (comma: (text == ",") = False)
    (open: isCloserText text = False)
    (comment: afterSound after = True):
    ∃ (done: Kinds) => laysAllKinds (leafRest text noted after before key) kinds = Some done
      ∧ Ends done after.isSome = True :=
  match after with
    | None => ({ Kinds.none | mid = True }, plainTailNone text noted before key kinds solid comma open, byComputing)
    | Some c =>
      ({ Kinds.none | held = True }, plainTailSome text noted c before key kinds solid comma open comment, byComputing)

theorem heldBefore ∀ (held before noted: Bool) (ok: (!held || (before && !noted)) = True): (!held || before) = True :=
  match held, before, noted, ok with
    | False, _, _, _ => byComputing
    | True, True, False, _ => byComputing

theorem closerTailNone ∀ (text: Text) (noted before: Bool) (key: Nat) (kinds: Kinds)
    (solid: isLayout text = False)
    (closes: closesText text = True)
    (shut: isCloserText text = True):
    laysAllKinds (leafRest text noted None before key) kinds
      = Some { start = False, broken = False, mid = True, held = kinds.held } :=
  rewrite shut,
      Bool.andFalse before,
      Bool.andFalse (!noted),
      allSingle (Closing text) kinds,
      closingKinds text solid closes kinds

--| The closer on a line of its own, then its comment.
theorem closerTailOwn ∀ (text comment: Text) (key: Nat) (kinds: Kinds)
    (solid: isLayout text = False)
    (closes: closesText text = True)
    (shut: isCloserText text = True)
    (is: commentText comment = True):
    laysAllKinds (leafRest text False (Some comment) True key) kinds = Some { Kinds.none | held = True } :=
  rewrite shut,
      closingKinds text solid closes (Kinds.started kinds),
      suffixKinds comment is { start = False, broken = False, mid = True, held = False } byComputing

theorem closerTailSome ∀ (text: Text) (noted: Bool) (comment: Text) (before: Bool) (key: Nat) (kinds: Kinds)
    (solid: isLayout text = False)
    (closes: closesText text = True)
    (shut: isCloserText text = True)
    (is: commentText comment = True)
    (unheld: kinds.held = False)
    (apart: (!noted && before) = False):
    laysAllKinds (leafRest text noted (Some comment) before key) kinds = Some { Kinds.none | held = True } :=
  rewrite shut,
      Bool.andTrue before,
      apart,
      closingKinds text solid closes kinds,
      unheld,
      suffixKinds comment is { start = False, broken = False, mid = True, held = False } byComputing

theorem heldNo ∀ (held before noted: Bool)
    (ok: (!held || (before && !noted)) = True)
    (apart: (!noted && before) = False):
    held = False :=
  match held, before, noted, ok, apart with
    | False, _, _, _, _ => byComputing
    | True, True, False, _, ap => cases
    | True, True, True, ok, _ => cases
    | True, False, b, ok, _ => cases

--| A closer leaves words on its line; a comment waits only if it has one, or if one waited and none was written
--| (`before` ends the line with one, and the closer holds no own-line comments).
theorem closerTail ∀ (text: Text) (noted: Bool) (after: Option Text) (before: Bool) (key: Nat) (kinds: Kinds)
    (solid: isLayout text = False)
    (closes: closesText text = True)
    (shut: isCloserText text = True)
    (comment: afterSound after = True)
    (held: (!kinds.held || (before && !noted)) = True):
    ∃ (done: Kinds) => laysAllKinds (leafRest text noted after before key) kinds = Some done
      ∧ Ends done (after.isSome || before) = True :=
  match after with
    | None => (
      { start = False, broken = False, mid = True, held = kinds.held },
      closerTailNone text noted before key kinds solid closes shut,
      heldBefore kinds.held before noted held
    )
    | Some c =>
      match noted, before with
        | False, True =>
          ({ Kinds.none | held = True }, closerTailOwn text c key kinds solid closes shut comment, byComputing)
        | False, False => (
          { Kinds.none | held = True },
          closerTailSome text False c False key kinds solid closes shut comment
            (heldNo kinds.held False False held byComputing)
            byComputing,
          byComputing
        )
        | True, before => (
          { Kinds.none | held = True },
          closerTailSome text True c before key kinds solid closes shut comment
            (heldNo kinds.held before True held byComputing)
            byComputing,
          byComputing
        )

-- A token.

theorem endsOrLeft ∀ (kinds: Kinds) (trails extra: Bool)
    (ends: Ends kinds trails = True):
    Ends kinds (trails || extra) = True :=
  match kinds, trails, ends with
    | { start = False, broken = False, mid, held = False }, _, _ => byComputing
    | { start = False, broken = False, mid, held = True }, True, _ => byComputing

theorem endsSame ∀ (kinds: Kinds) (trails trails': Bool)
    (same: trails = trails')
    (ends: Ends kinds trails = True):
    Ends kinds trails' = True :=
  rewrite <- same then ends

--| What a token writes after its own-line comments.
theorem restStep ∀ (text: Text) (above: List Note) (after: Option Text) (before: Bool) (key: Nat)
    (solid: isLayout text = False)
    (comma: (text == ",") = False)
    (closes: isCloserText text = True → closesText text = True)
    (comment: afterSound after = True):
    StepAll
      (leafRest text (!above.isEmpty) after before key)
      (LeadHeld (!above.isEmpty && isCloserText text) before)
      (kinds => Ends kinds (after.isSome || (isCloserText text && before))) :=
  kinds held =>
    match shut: isCloserText text with
      | True =>
        let (done, found, ends) :=
          closerTail text
            (!above.isEmpty)
            after
            before
            key
            kinds
            solid
            (closes shut)
            shut
            comment
            (rewrite Bool.andTrue (!above.isEmpty) at held)
        (done, found, ends)
      | False =>
        let (done, found, ends) := plainTail text (!above.isEmpty) after before key kinds solid comma shut comment
        (done, found, endsOrLeft done _ _ ends)

--| A token on its own passes the check and leaves words on its line, a comment waiting only if it has a trailing
--| one, or if it is a closer after code that ends its line with one.
--|
--| Proof idea: its own-line comments (`leadingStep`), then its text and trailing comment (`restStep`).
theorem leafStep ∀ (text: Text) (above: List Note) (after: Option Text) (blankBefore: Bool) (around: Around) (key: Nat)
    (solid: isLayout text = False)
    (notes: notesSound above = True)
    (comment: afterSound after = True)
    (comma: (text == ",") = False)
    (closes: isCloserText text = True → closesText text = True)
    (home: isCloserText text = True → around.hoisted = False):
    Step
      (Word.leaf ({ text, comments = { above, after, blankBefore } }) around key)
      (kinds => Calm kinds around.before)
      (kinds => Ends kinds (after.isSome || (isCloserText text && around.before))) :=
  stepDocConcat _ _ _
    (stepAllAppend
      (Word.leading ({ text, comments = { above, after, blankBefore } }) around key)
      (leafRest text (!above.isEmpty) after around.before key)
      (kinds => Calm kinds around.before)
      (LeadHeld (!above.isEmpty && isCloserText text) around.before)
      (kinds => Ends kinds (after.isSome || (isCloserText text && around.before)))
      (leadingStep text above after blankBefore around key notes home)
      (restStep text above after around.before key solid comma closes comment))
