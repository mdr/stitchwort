--| Triples over `Std.Doc`'s `Touches` (SW-4076, step 2 of tools/fmt/NOTES.md, "Printed spacing"): from every seam
--| that satisfies `pre`, every way a document prints adds words whose code words touch as a list of `Spacing`s
--| admits, and leaves a seam that satisfies `post`. One combinator per `Doc` constructor; the rules' lemmas are in
--| `Fmt.TouchProofs`.
--|
--| Comments drop out of what is counted (`codeTouching`): an own-line comment is a word, and a trailing comment
--| waits in the seam (`Awaiting`) and is listed when its line ends, so every seam here holds comments only
--| (`Quiet`).

namespace Fmt.TouchSteps
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (Along, Awaiting, Begun, Seam, Touch, Touches, TouchesAll, isLayout, touchesWeaker)
import Fmt.GlueProofs (codeTouching, codeTouchingAppend, isComment)
import Fmt.OutputStatements (..)

-- Spacings and glue.

--| Each glue as its spacing says, the two lists alike in length.
def admitsGlue: List Spacing → List Bool → Bool
  | [], [] => True
  | [spacing, ..rest], [glued, ..later] => spacing.admits glued && admitsGlue rest later
  | _, _ => False

theorem admitsAppend ∀ (front back: List Spacing) (glues later: List Bool)
    (first: admitsGlue front glues = True)
    (second: admitsGlue back later = True):
    admitsGlue (front ++ back) (glues ++ later) = True :=
  match front, glues, first with
    | [], [], _ => second
    | [spacing, ..rest], [glued, ..more], first =>
      Bool.andIntro (Bool.andLeft first) (admitsAppend rest back more later (Bool.andRight first) second)

-- Seams.

--| A seam whose waiting comment, if any, is a comment.
def Quiet: Seam → Prop
  | Awaiting _ comment => isComment comment = True
  | _ => True

theorem endingQuiet ∀ (seam: Seam) (quiet: Quiet seam): codeTouching seam.ending = [] := match seam, quiet with
  | Begun | Along _, _ => byComputing
  | Awaiting word comment, quiet => rewrite quiet

--| Where an element whose first code word is spaced `first` may start: at a line start or after a space only if it
--| needn't be glued; after a word as `first` admits touching it; after a waiting comment only if the code before ends
--| with one (`before`), on the next line.
def Fits (before: Bool) (first: Spacing) (seam: Seam): Prop := match seam with
  | Begun => first.admits False = True
  | Along word => first.admits word = True
  | Awaiting _ comment => before = True ∧ first.admits False = True ∧ isComment comment = True

--| Where an element ends: a comment waits only if it ends with one (`trails`).
def Ends (trails: Bool) (seam: Seam): Prop := match seam with
  | Begun | Along _ => True
  | Awaiting _ comment => trails = True ∧ isComment comment = True

--| After a space or a line break: nothing on the line to touch.
def Gapped (trails: Bool) (seam: Seam): Prop := match seam with
  | Begun => True
  | Along word => word = False
  | Awaiting _ comment => trails = True ∧ isComment comment = True

theorem fitsQuiet ∀ [before: Bool] [first: Spacing] [seam: Seam] (fits: Fits before first seam): Quiet seam :=
  match seam, fits with
    | Begun | Along _, _ => byComputing
    | Awaiting word comment, (_, _, quiet) => quiet

theorem endsQuiet ∀ (trails: Bool) (seam: Seam) (ends: Ends trails seam): Quiet seam := match seam, ends with
  | Begun | Along _, _ => byComputing
  | Awaiting word comment, (_, quiet) => quiet

--| Anything free may start where an element ended.
theorem endsFits ∀ (trails: Bool) (seam: Seam) (ends: Ends trails seam): Fits trails Free seam := match seam, ends with
  | Begun | Along _, _ => byComputing
  | Awaiting word comment, (waits, quiet) => (waits, byComputing, quiet)

--| A code word that needn't be glued may start after a space.
theorem gappedFits ∀ [trails: Bool] [first: Spacing] [seam: Seam]
    (loose: first.admits False = True)
    (gapped: Gapped trails seam):
    Fits trails first seam :=
  match seam, gapped with
    | Begun, _ => loose
    | Along word, apart => rewrite apart then loose
    | Awaiting word comment, (waits, quiet) => (waits, loose, quiet)

theorem endsWeaker ∀ (trails trails': Bool)
    (implies: trails = True → trails' = True) (seam: Seam)
    (ends: Ends trails seam):
    Ends trails' seam :=
  match seam, ends with
    | Begun | Along _, _ => byComputing
    | Awaiting word comment, (waits, quiet) => (implies waits, quiet)

theorem fitsWeaker ∀ (before: Bool) [before': Bool]
    (implies: before = True → before' = True)
    [first: Spacing] [seam: Seam]
    (fits: Fits before first seam):
    Fits before' first seam :=
  match seam, fits with
    | Begun | Along _, loose => loose
    | Awaiting word comment, (waits, loose, quiet) => (implies waits, loose, quiet)

-- The triples.

--| From every seam satisfying `pre`, `doc` adds words whose code words touch as `spacing` admits, and leaves a seam
--| satisfying `post`.
def Steps (doc: Doc) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop): Prop :=
  ∀ (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop) => pre seam
    → (∀ (after: Seam) (added: List Touch) => post after
      → admitsGlue spacing (codeTouching added) = True
      → next after (trace ++ added))
    → Touches doc seam trace next

def StepsAll (docs: List Doc) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop): Prop :=
  ∀ (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop) => pre seam
    → (∀ (after: Seam) (added: List Touch) => post after
      → admitsGlue spacing (codeTouching added) = True
      → next after (trace ++ added))
    → TouchesAll docs seam trace next

--| Nothing added: the continuation, with the words as they were.
theorem stay ∀ (post: Seam → Prop) (spacing: List Spacing) (seam: Seam)
    (trace: List Touch) (next: Seam → List Touch → Prop)
    (none: admitsGlue spacing [] = True)
    (after: ∀ (left: Seam) (added: List Touch) => post left
      → admitsGlue spacing (codeTouching added) = True
      → next left (trace ++ added)) (holds: post seam):
    next seam trace :=
  rewrite <- List.appendNil trace then after seam [] holds none

theorem stepsFrom ∀ [doc: Doc] [pre weaker: Seam → Prop] [spacing: List Spacing] [post: Seam → Prop]
    (steps: Steps doc pre spacing post) (implies: ∀ (seam: Seam) => weaker seam → pre seam):
    Steps doc weaker spacing post :=
  seam trace next holds after => steps seam trace next (implies seam holds) after

theorem stepsTo ∀ [doc: Doc] [pre: Seam → Prop] [spacing: List Spacing] [post weaker: Seam → Prop]
    (steps: Steps doc pre spacing post) (implies: ∀ (seam: Seam) => post seam → weaker seam):
    Steps doc pre spacing weaker :=
  seam trace next holds after =>
    steps seam trace next holds (left added reached admits => after left added (implies left reached) admits)

theorem allTo ∀ (docs: List Doc) (pre: Seam → Prop) [spacing: List Spacing] (post weaker: Seam → Prop)
    (steps: StepsAll docs pre spacing post) (implies: ∀ (seam: Seam) => post seam → weaker seam):
    StepsAll docs pre spacing weaker :=
  seam trace next holds after =>
    steps seam trace next holds (left added reached admits => after left added (implies left reached) admits)

--| The same documents, spaced alike.
theorem stepsSpacing ∀ [doc: Doc] [pre: Seam → Prop] [spacing spacing': List Spacing] [post: Seam → Prop]
    (same: spacing = spacing')
    (steps: Steps doc pre spacing post):
    Steps doc pre spacing' post :=
  rewrite <- same then steps

theorem allSpacing ∀ [docs: List Doc] (pre: Seam → Prop) [spacing: List Spacing]
    (spacing': List Spacing) (post: Seam → Prop)
    (same: spacing = spacing')
    (steps: StepsAll docs pre spacing post):
    StepsAll docs pre spacing' post :=
  rewrite <- same then steps

theorem stepsNil ∀ (pre post: Seam → Prop) (implies: ∀ (seam: Seam) => pre seam → post seam): StepsAll [] pre [] post :=
  seam trace next holds after => stay post [] seam trace next byComputing after (implies seam holds)

theorem stepsCons ∀ (doc: Doc) (docs: List Doc) (pre middle post: Seam → Prop) [front back: List Spacing]
    (first: Steps doc pre front middle)
    (rest: StepsAll docs middle back post):
    StepsAll [doc, ..docs] pre (front ++ back) post :=
  seam trace next holds after =>
    first seam trace (between later => TouchesAll docs between later next) holds (between added reached admits =>
      rest between (trace ++ added) next reached (left more ended admitsMore =>
        rewrite List.appendAssoc trace added more then
          after left
            (added ++ more)
            ended
            (rewrite codeTouchingAppend added more then
              admitsAppend front back (codeTouching added) (codeTouching more) admits admitsMore)))

theorem stepsLast ∀ [doc: Doc] [pre post: Seam → Prop] [spacing: List Spacing]
    (only: Steps doc pre spacing post):
    StepsAll [doc] pre spacing post :=
  rewrite <- List.appendNil spacing then stepsCons doc [] pre post post only (stepsNil post post (seam holds => holds))

theorem touchesAllAppend ∀ (front back: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: TouchesAll front seam trace (between later => TouchesAll back between later next)):
    TouchesAll (front ++ back) seam trace next :=
  match front, touches with
    | [], touches => touches
    | [doc, ..rest], touches =>
      touchesWeaker doc seam trace
        (between later => TouchesAll rest between later (after more => TouchesAll back after more next))
        (between later => TouchesAll (rest ++ back) between later next)
        (between later inner => touchesAllAppend rest back between later next inner)
        touches

theorem stepsAppend ∀ (front: List Doc) [back: List Doc] (pre middle post: Seam → Prop) [first second: List Spacing]
    (one: StepsAll front pre first middle)
    (other: StepsAll back middle second post):
    StepsAll (front ++ back) pre (first ++ second) post :=
  seam trace next holds after =>
    touchesAllAppend front back seam trace next
      (one seam trace (between later => TouchesAll back between later next) holds (between added reached admits =>
        other between (trace ++ added) next reached (left more ended admitsMore =>
          rewrite List.appendAssoc trace added more then
            after left
              (added ++ more)
              ended
              (rewrite codeTouchingAppend added more then
                admitsAppend first second (codeTouching added) (codeTouching more) admits admitsMore))))

theorem emptyTouches ∀ (doc: Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop)
    (empty: doc.isEmpty = True)
    (touches: Touches doc seam trace next):
    next seam trace :=
  match doc, empty, touches with | Doc.Nothing, _, touches => touches

theorem filterTouches ∀ (docs: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: TouchesAll docs seam trace next):
    TouchesAll (docs.filter (doc => not doc.isEmpty)) seam trace next :=
  match docs, touches with
    | [], touches => touches
    | [doc, ..rest], touches =>
      match empty: doc.isEmpty with
        | True =>
          filterTouches rest seam trace next
            (emptyTouches doc seam trace (between later => TouchesAll rest between later next) empty touches)
        | False =>
          touchesWeaker doc seam trace
            (between later => TouchesAll rest between later next)
            (between later => TouchesAll (rest.filter (doc => not doc.isEmpty)) between later next)
            (between later inner => filterTouches rest between later next inner)
            touches

--| `Doc.concat` touches as the documents one after another.
theorem concatTouches ∀ (docs: List Doc) (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop)
    (touches: TouchesAll docs seam trace next):
    Touches (Doc.concat docs) seam trace next :=
  let kept := filterTouches docs seam trace next touches
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] =>
      touchesWeaker only seam trace
        (between later => TouchesAll [] between later next)
        next
        (between later reached => reached)
        kept
    | [first, second, ..rest] => kept

theorem stepsConcat ∀ (docs: List Doc) [pre: Seam → Prop] [spacing: List Spacing] [post: Seam → Prop]
    (each: StepsAll docs pre spacing post):
    Steps (Doc.concat docs) pre spacing post :=
  seam trace next holds after => concatTouches docs seam trace next (each seam trace next holds after)

theorem stepsTwo ∀ (first: Doc) [second: Doc] (pre middle post: Seam → Prop) [front back: List Spacing]
    (one: Steps first pre front middle)
    (other: Steps second middle back post):
    StepsAll [first, second] pre (front ++ back) post :=
  stepsCons first [second] pre middle post one (stepsLast other)

-- The document's constructors.

theorem stepsNothing ∀ (pre: Seam → Prop): Steps Doc.Nothing pre [] pre := seam trace next holds after =>
  stay pre [] seam trace next byComputing after holds

theorem stepsBreakParent ∀ (pre: Seam → Prop): Steps BreakParent pre [] pre := seam trace next holds after =>
  stay pre [] seam trace next byComputing after holds

theorem stepsBlank ∀ (pre: Seam → Prop): Steps Blank pre [] pre := seam trace next holds after =>
  stay pre [] seam trace next byComputing after holds

theorem stepsMark ∀ (key: Nat) (pre: Seam → Prop): Steps (Mark key) pre [] pre := seam trace next holds after =>
  stay pre [] seam trace next byComputing after holds

--| A line break: the waiting comment, which is no code word, then a line start.
theorem breakStep ∀ (post: Seam → Prop) (seam: Seam) [trace: List Touch] [next: Seam → List Touch → Prop]
    (quiet: Quiet seam)
    (fresh: post Begun)
    (after: ∀ (left: Seam) (added: List Touch) => post left
      → admitsGlue [] (codeTouching added) = True
      → next left (trace ++ added)):
    next Begun (trace ++ seam.ending) :=
  after Begun seam.ending fresh (rewrite endingQuiet seam quiet)

theorem stepsHard ∀ [pre: Seam → Prop] (post: Seam → Prop)
    (quiet: ∀ (seam: Seam) => pre seam → Quiet seam) (fresh: post Begun):
    Steps HardLine pre [] post :=
  seam trace next holds after => breakStep post seam (quiet seam holds) fresh after

theorem stepsLineStart ∀ [pre post: Seam → Prop] (quiet: ∀ (seam: Seam) => pre seam → Quiet seam) (fresh: post Begun):
    Steps LineStart pre [] post :=
  seam trace next holds after => breakStep post seam (quiet seam holds) fresh after

theorem stepsLineStartHere ∀ (pre post: Seam → Prop)
    (quiet: ∀ (seam: Seam) => pre seam → Quiet seam) (fresh: post Begun):
    Steps LineStartHere pre [] post :=
  seam trace next holds after => breakStep post seam (quiet seam holds) fresh after

theorem stepsCloserLine ∀ (key: Nat) [pre post: Seam → Prop]
    (quiet: ∀ (seam: Seam) => pre seam → Quiet seam) (fresh: post Begun):
    Steps (CloserLine key) pre [] post :=
  seam trace next holds after => breakStep post seam (quiet seam holds) fresh after

theorem stepsSoft ∀ (pre post: Seam → Prop) (quiet: ∀ (seam: Seam) => pre seam → Quiet seam)
    (keeps: ∀ (seam: Seam) => pre seam → post seam) (fresh: post Begun):
    Steps SoftLine pre [] post :=
  seam trace next holds after =>
    (
      stay post [] seam trace next byComputing after (keeps seam holds),
      breakStep post seam (quiet seam holds) fresh after
    )

theorem stepsNest ∀ (indent: Nat) [inner: Doc] (pre: Seam → Prop) [spacing: List Spacing] [post: Seam → Prop]
    (steps: Steps inner pre spacing post):
    Steps (Nest indent inner) pre spacing post :=
  steps

theorem stepsGroup ∀ [inner: Doc] (hard: Bool) [pre: Seam → Prop] [spacing: List Spacing] [post: Seam → Prop]
    (steps: Steps inner pre spacing post):
    Steps (Group inner hard) pre spacing post :=
  steps

theorem stepsIdGroup ∀ (id: Nat) [inner: Doc] (hard: Bool) (pre: Seam → Prop)
    [spacing: List Spacing] (post: Seam → Prop)
    (steps: Steps inner pre spacing post):
    Steps (IdGroup id inner hard) pre spacing post :=
  steps

theorem stepsFlatten ∀ [inner: Doc] [pre: Seam → Prop] [spacing: List Spacing] (post: Seam → Prop)
    (steps: Steps inner pre spacing post):
    Steps (Flatten inner) pre spacing post :=
  steps

theorem stepsIfBroken ∀ (id: Nat) [broken flat: Doc] (pre: Seam → Prop) [spacing: List Spacing] (post: Seam → Prop)
    (brokenSteps: Steps broken pre spacing post)
    (flatSteps: Steps flat pre spacing post):
    Steps (IfBroken id broken flat) pre spacing post :=
  seam trace next holds after => (brokenSteps seam trace next holds after, flatSteps seam trace next holds after)

--| Each option of a choice, from the same seams to the same seams, spaced alike.
def EachSteps (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop): List Doc → Prop
  | [] => True
  | [option, ..others] => Steps option pre spacing post ∧ EachSteps pre spacing post others

theorem optionsStep ∀ (first: Doc) (others: List Doc) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop)
    (each: EachSteps pre spacing post [first, ..others])
    (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop) (holds: pre seam)
    (after: ∀ (left: Seam) (added: List Touch) => post left
      → admitsGlue spacing (codeTouching added) = True
      → next left (trace ++ added)):
    Std.Doc.Proofs.OptionsTouch [first, ..others] seam trace next :=
  match others, each with
    | [], (steps, _) => steps seam trace next holds after
    | [second, ..more], (steps, rest) =>
      (steps seam trace next holds after, optionsStep second more pre spacing post rest seam trace next holds after)

--| A choice whose options all step alike.
theorem stepsChoice ∀ (first: Doc) (others: List Doc) (pre: Seam → Prop) [spacing: List Spacing] [post: Seam → Prop]
    (each: EachSteps pre spacing post [first, ..others]):
    Steps (Choice [first, ..others]) pre spacing post :=
  seam trace next holds after => optionsStep first others pre spacing post each seam trace next holds after

--| A displaced element steps if its contents do from where they start, and from a line start where a comment
--| waits.
theorem stepsDisplaced ∀ [inner: Doc] (pre: Seam → Prop) [spacing: List Spacing] (post: Seam → Prop)
    (steps: Steps inner pre spacing post)
    (fresh: pre Begun) (quiet: ∀ (seam: Seam) => pre seam → Quiet seam):
    Steps (Displaced inner) pre spacing post :=
  seam trace next holds after =>
    match seam, holds with
      | Begun, holds => steps Begun trace next holds after
      | Along word, holds => steps (Along word) trace next holds after
      | Awaiting word comment, holds =>
        let ending: List Touch := [{ word = comment, touching = False }]
        let silent: codeTouching ending = [] := endingQuiet (Awaiting word comment) (quiet _ holds)
        steps Begun (trace ++ ending) next fresh (left added reached admits =>
          rewrite List.appendAssoc trace ending added then
            after left (ending ++ added) reached (rewrite codeTouchingAppend ending added, silent then admits))

--| A document one line below: the waiting comment, then the document from a line start.
theorem stepsOneLineBelow ∀ [inner: Doc] (pre: Seam → Prop) [start: Seam → Prop] [spacing: List Spacing]
    (post: Seam → Prop) (quiet: ∀ (seam: Seam) => pre seam → Quiet seam) (fresh: start Begun)
    (steps: Steps inner start spacing post):
    Steps (OneLineBelow inner) pre spacing post :=
  seam trace next holds after =>
    steps Begun (trace ++ seam.ending) next fresh (left added reached admits =>
      rewrite List.appendAssoc trace seam.ending added then
        after left
          (seam.ending ++ added)
          reached
          (rewrite codeTouchingAppend seam.ending added, endingQuiet seam (quiet seam holds) then admits))

--| A `Line` after an element: a space or a line break, after which nothing touches.
theorem stepsLine ∀ (trails: Bool): Steps Line (Ends trails) [] (Gapped trails) := seam trace next holds after =>
  match seam, holds with
    | Begun, _ => (
      stay (Gapped trails) [] (Along False) trace next byComputing after byComputing,
      stay (Gapped trails) [] Begun trace next byComputing after byComputing
    )
    | Along word, _ => (
      stay (Gapped trails) [] (Along False) trace next byComputing after byComputing,
      stay (Gapped trails) [] Begun trace next byComputing after byComputing
    )
    | Awaiting word comment, holds => (
      stay (Gapped trails) [] (Awaiting False comment) trace next byComputing after holds,
      breakStep (Gapped trails) (Awaiting word comment) holds.right byComputing after
    )

--| A space after an element.
theorem stepsSpace ∀ (trails: Bool): Steps (Doc.text " ") (Ends trails) [] (Gapped trails) :=
  seam trace next holds after =>
    match seam, holds with
      | Begun | Along _, _ => stay (Gapped trails) [] (Along False) trace next byComputing after byComputing
      | Awaiting word comment, holds =>
        stay (Gapped trails) [] (Awaiting False comment) trace next byComputing after holds

-- Words.

--| A text the lexer reads as a token: not empty, not layout, no comment.
def Code (text: Text): Prop := text.isEmpty = False ∧ isLayout text = False ∧ isComment text = False

--| A token's text, starting a line, after a word, or after a waiting comment on the next line.
theorem stepsChunk ∀ [text: Text] (size: Nat) (before: Bool) (first: Spacing)
    (code: Code text):
    Steps (Chunk text size) (Fits before first) [first] (seam => seam = Along True) :=
  let (filled, solid, notComment) := code
  seam trace next holds after =>
    match seam, holds with
      | Begun, loose =>
        rewrite filled, solid then
          after (Along True) [{ word = text, touching = False }] byComputing (rewrite notComment, loose)
      | Along word, admits =>
        rewrite filled, solid then
          after (Along True) [{ word = text, touching = word }] byComputing (rewrite notComment, admits)
      | Awaiting word comment, (_, loose, quiet) =>
        let spaces: text.all (char => char == ' ') = False := Bool.orFalseLeft _ _ solid
        let broken: (text == "\n") = False := Bool.orFalseRight _ _ solid
        let ending: List Touch := [{ word = comment, touching = False }]
        rewrite filled, spaces, broken, List.appendAssoc trace ending [{ word = text, touching = False }] then
          after
            (Along True)
            (ending ++ [{ word = text, touching = False }])
            byComputing
            (rewrite codeTouchingAppend ending [{ word = text, touching = False }], quiet, notComment, loose)

--| Where a closer leaves the printer: after it on its line, or, where a comment waited, still waiting.
def Closed (before: Bool) (seam: Seam): Prop := match seam with
  | Begun => Void
  | Along word => word = True
  | Awaiting _ comment => before = True ∧ isComment comment = True

theorem closedEnds ∀ (before: Bool) (seam: Seam) (closed: Closed before seam): Ends before seam :=
  match seam, closed with
    | Along word, _ => byComputing
    | Awaiting word comment, both => both

--| Where no comment waited, a closer leaves the printer after it on its line.
theorem closedAlong ∀ (seam: Seam) (closed: Closed False seam): seam = Along True := match seam, closed with
  | Along word, touched => rewrite touched
  | Awaiting word comment, (never, _) => (Bool.falseNotTrue never).impossible

--| A closer or a comma, which joins the line of a waiting comment before it.
theorem stepsClosing ∀ [text: Text] (before: Bool)
    (code: Code text):
    Steps (Closing text) (Fits before Free) [Free] (Closed before) :=
  let (filled, solid, notComment) := code
  seam trace next holds after =>
    match seam, holds with
      | Begun, _ =>
        rewrite filled, solid then
          after (Along True) [{ word = text, touching = False }] byComputing (rewrite notComment)
      | Along word, _ =>
        rewrite filled, solid then
          after (Along True) [{ word = text, touching = word }] byComputing (rewrite notComment)
      | Awaiting word comment, (waits, _, quiet) =>
        rewrite filled, solid then
          after (Awaiting True comment) [{ word = text, touching = word }] (waits, quiet) (rewrite notComment)

--| A trailing comment, after a word on its line.
theorem stepsSuffix ∀ (text: Text)
    (comment: isComment text = True)
    (solid: isLayout text = False):
    Steps (LineSuffix text) (seam => seam = Along True) [] (Closed True) :=
  seam trace next holds after =>
    rewrite holds then
      (solid, stay (Closed True) [] (Awaiting True text) trace next byComputing after (byComputing, comment))
