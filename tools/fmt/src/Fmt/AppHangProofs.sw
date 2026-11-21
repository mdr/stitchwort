--| Slice 1's `hangs` clause for calls (SW-4030): a call's elements on its line, spaced, keep the fold as after
--| its function's first word.
namespace Fmt.AppHangProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Expr, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)

--| Docs in turn, each starting with a comment waiting only if the one before ended with one (`before`, at first),
--| `step` holding of each, and the last ending with one waiting only if `trails`.
def Chained (step: Bool → Bool → Doc → Prop) (before trails: Bool): List Doc → Prop
  | [] => before = trails
  | [doc, ..rest] => ∃ (middle: Bool) => step before middle doc ∧ Chained step middle trails rest

--| Elements after the first, each after a space: each starts where the one before ended, a comment waiting only if
--| that one's code ends with one (`before`), and the last ends with a comment waiting only if `trails`.
def SpacedParts (kinds: Text → Tok) (indent: Nat) (before trails: Bool) (docs: List Doc): Prop :=
  Chained (before middle doc => PartHangs kinds doc indent before middle) before trails docs

--| Where an element ended after words: the fold as after them, nothing in force right of the indentation.
def AfterWords (state: HangState) (indent: Nat) (trails: Bool): Place → Hang → Prop := place hang =>
  Ended state trails place ∧ hang = Hang.At state ∧ (inForce state.blocks state.top <= indent) = True

theorem partStep ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (part: PartHangs kinds doc indent before trails):
    HangLays kinds doc indent (AfterWords state indent before) (AfterWords state indent trails) :=
  hangsBy (place trace next (ended, folded, clear) after =>
    (part state place quiet unglued) place _ trace next byComputing
      (byComputing, folded, ended, clear)
      (hangsAfter (left later (done, landed) => after left later (done, landed, clear))))

--| Spaced elements after the first.
--|
--| Proof idea: by the list; each space keeps where the element before ended (`gapKeeps`), and each element starts
--| there and ends with the fold as it was (`partStep`).
theorem spacedRest ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (parts: SpacedParts kinds indent before trails docs):
    HangLaysAll kinds
      (docs.concatMap (doc => [Doc.text " ", doc]))
      indent
      (AfterWords state indent before)
      (AfterWords state indent trails) :=
  match docs, parts with
    | [], same =>
      rewrite same then
        hangsNil kinds indent (AfterWords state indent trails) (AfterWords state indent trails) (place hang holds =>
          holds)
    | [doc, ..rest], (middle, part, more) =>
      hangsCons
        [doc, ..rest.concatMap (doc => [Doc.text " ", doc])]
        (hangsBy (place trace next (ended, folded, clear) after =>
          (gapKeeps kinds
                (Doc.text " ")
                indent
                state
                before
                ((inForce state.blocks state.top <= indent) = True)
                (Inr byComputing)) place _ trace next byComputing
              (ended, folded, clear)
              (hangsAfter after)))
        (hangsCons
          (rest.concatMap (doc => [Doc.text " ", doc]))
          (partStep kinds doc indent state before middle quiet unglued part)
          (spacedRest kinds rest indent state middle trails quiet unglued more))

--| Docs joined by a separator: the first, then the separator before each other.
theorem joinedWithIs ∀ (separator first: Doc) (rest: List Doc):
    Doc.joinedWith separator [first, ..rest] = [first, ..rest.concatMap (doc => [separator, doc])] :=
  match rest with
    | [] => byComputing
    | [second, ..more] => rewrite joinedWithIs separator second more

--| Elements spaced on one line (`spaced`) as one element: the fold after them as after the first one's first word.
--|
--| Proof idea: the first element leaves the fold as after its first word, which starts nothing and glues nothing,
--| with nothing in force right of the indentation (`openedBound`); the rest keep it (`spacedRest`).
theorem spacedHangs ∀ [kinds: Text → Tok] [first: Doc] (rest: List Doc) [indent column: Nat] [middle trails: Bool]
    (head: ElHangs kinds first indent column False middle wordStart)
    (parts: SpacedParts kinds indent middle trails rest):
    ElHangs kinds (spaced [first, ..rest]) indent column False trails wordStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      let (_, _, (seated, below, clear, room)) := entered
      let opened := openedBy state (wordStart indent entry)
      let bound: (inForce opened.blocks opened.top <= indent) = True := openedBound seated below clear room
      let pre := Entered indent column False state entry (wordStart indent entry)
      rewrite joinedWithIs (Doc.text " ") first rest then
        (hangsConcat
              (hangsCons
                (rest.concatMap (doc => [Doc.text " ", doc]))
                (hangsPost (head state entry) (place hang (ended, folded) => (ended, folded, bound)))
                (spacedRest kinds rest indent opened middle trails
                  (openedQuietStart state (wordStart indent entry))
                  (openedUnglued state (wordStart indent entry))
                  parts))) place _ trace next byComputing entered
            (hangsAfter (left later (ended, folded, _) => after left later (ended, folded))))

-- A call's arguments, each an element laid at `inset`, the fold as after the call's first word.

--| Where an argument laid at `inset` starts: a seat there, after a waiting comment only if `before`, after words or
--| right after a line break (never a plain line start).
def ArgSeat (state: HangState) (inset: Nat) (before: Bool): Place → Hang → Prop := place hang =>
  hang = Hang.At state ∧ Seat inset inset before state place (wordStart inset place) ∧ plainStart place = False

--| An argument, from its seat: the fold after it as before it, which starts nothing and glues nothing.
theorem argHangs ∀ (kinds: Text → Tok) (doc: Doc) (inset indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (el: ElHangs kinds doc inset inset before trails wordStart):
    HangLays kinds doc inset (ArgSeat state inset before) (AfterWords state indent trails) :=
  hangsBy (place trace next (folded, seat, _) after =>
    let same := openedQuiet (wordStart inset place) quiet unglued
    (el state place) place _ trace next byComputing
      (byComputing, folded, seat)
      (hangsAfter (left later (ended, landed) =>
        after left later (rewrite same at ended then ended, rewrite same at landed then landed, clear))))

theorem brokenArgSeat ∀ (inset: Nat) (state: HangState) (before: Bool) (carry: Carry)
    (unglued: state.glue = False)
    (floor: carry.floor = None)
    (bound: (inForce state.blocks state.top < inset) = True):
    ArgSeat state inset before (Broken (floored carry inset) (carry.breakTo inset)) (Hang.At state) :=
  let landed: floored carry inset = inset := rewrite floor
  rewrite landed then
    (byComputing, ((byComputing, byComputing), Nat.leRefl inset, arithmetic, (unglued, arithmetic)), byComputing)

theorem midArgSeat ∀ (inset at: Nat) (state: HangState) (before: Bool) (carry: Carry)
    (floor: carry.floor = None)
    (left: (inForce state.blocks state.top <= at) = True)
    (bound: (inForce state.blocks state.top < inset) = True):
    ArgSeat state inset before (Mid at carry) (Hang.At state) :=
  (byComputing, ((floor, left), Nat.leRefl inset, arithmetic, byComputing), byComputing)

theorem heldArgSeat ∀ (inset at: Nat) (state: HangState) (carry: Carry)
    (unglued: state.glue = False)
    (floor: carry.floor = None)
    (left: (inForce state.blocks state.top <= at) = True)
    (bound: (inForce state.blocks state.top < inset) = True):
    ArgSeat state inset True (Held at carry) (Hang.At state) :=
  let landed: floored carry (Nat.max inset (at + 2)) = Nat.max inset (at + 2) := rewrite floor
  (
    byComputing,
    ((byComputing, floor, left), Nat.leRefl inset, arithmetic, (unglued, rewrite landed then arithmetic)),
    byComputing
  )

--| A `Line` before an argument laid deeper than the call: a space, or a line break at `inset`.
theorem lineArg ∀ (kinds: Text → Tok) (inset indent: Nat) (state: HangState) (before: Bool)
    (unglued: state.glue = False)
    (deeper: (indent < inset) = True):
    HangLays kinds Line inset (AfterWords state indent before) (ArgSeat state inset before) :=
  hangsLine kinds inset (AfterWords state indent before) (ArgSeat state inset before) (place trace (ended, folded,
    clear) =>
    let bound: (inForce state.blocks state.top < inset) = True := arithmetic
    match place, ended with
      | Mid at carry, (floor, left) =>
        rewrite folded then
          (
            midArgSeat inset at state before { carry | floor = None } byComputing left bound,
            brokenArgSeat inset state before carry unglued floor bound
          )
      | Held at carry, (waits, floor, left) =>
        rewrite folded then
          (
            rewrite waits then heldArgSeat inset at state carry unglued floor left bound,
            brokenArgSeat inset state before carry unglued floor bound
          ))

--| Arguments each on a line of its own, laid at `inset`, each first word where `startFor` says: at a line start the
--| comments above an argument, if any, change nothing of where its first word starts.
def LinedArgs (kinds: Text → Tok) (inset: Nat) (before trails: Bool) (docs: List Doc): Prop :=
  Chained
    (before middle doc => ∃ (noted: Bool) => ElHangs kinds doc inset inset False middle (startFor noted))
    before
    trails
    docs

--| Whether the place is right after a line break.
def brokenPlace: Place → Bool
  | Broken _ _ => True
  | _ => False

--| Where an argument on a line of its own starts: a seat right after the line break before it.
def LineSeat (state: HangState) (inset: Nat): Place → Hang → Prop := place hang =>
  ArgSeat state inset False place hang ∧ brokenPlace place = True

--| Right after a line break an element's first word starts the line, whatever comments it has above it.
theorem lineStartFor ∀ (noted: Bool) (inset: Nat) (place: Place)
    (start: brokenPlace place = True):
    startFor noted inset place = wordStart inset place :=
  match place, start with
    | Broken at carry, _ => cases noted then byComputing
    | AtStart _ _ | Mid _ _ | Held _ _, never => (Bool.falseNotTrue never).impossible

--| A `HardLine` before an argument laid deeper than the call: the start of a line at `inset`.
theorem hardLineArg ∀ (kinds: Text → Tok) (inset indent: Nat) (state: HangState) (before: Bool)
    (unglued: state.glue = False)
    (deeper: (indent < inset) = True):
    HangLays kinds HardLine inset (AfterWords state indent before) (LineSeat state inset) :=
  hangsHardBroken kinds inset (AfterWords state indent before) (LineSeat state inset) (place hang (ended, folded,
    clear) =>
    let bound: (inForce state.blocks state.top < inset) = True := arithmetic
    match place, ended with
      | Mid at carry, (floor, _) =>
        (byComputing, (rewrite folded then brokenArgSeat inset state False carry unglued floor bound, byComputing))
      | Held at carry, (_, floor, _) =>
        (byComputing, (rewrite folded then brokenArgSeat inset state False carry unglued floor bound, byComputing)))

--| An argument on a line of its own, from its seat, its first word where `startFor` says: the fold after it as before
--| it, as `argHangs`.
theorem argLineHangs ∀ (kinds: Text → Tok) (doc: Doc) (inset indent: Nat) (state: HangState) (trails noted: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (el: ElHangs kinds doc inset inset False trails (startFor noted)):
    HangLays kinds doc inset (LineSeat state inset) (AfterWords state indent trails) :=
  hangsBy (place trace next ((folded, seat, _), start) after =>
    let first: startFor noted inset place = wordStart inset place := lineStartFor noted inset place start
    let seated: Seat inset inset False state place (startFor noted inset place) := rewrite first then seat
    let same := openedQuiet (startFor noted inset place) quiet unglued
    (el state place) place _ trace next byComputing
      (byComputing, folded, seated)
      (hangsAfter (left later (ended, landed) =>
        after left later (rewrite same at ended then ended, rewrite same at landed then landed, clear))))

--| Arguments each on a line of its own (a broken call's `rest`), laid deeper than the call: the fold kept.
theorem linedRest ∀ (kinds: Text → Tok) (docs: List Doc) (inset indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (deeper: (indent < inset) = True)
    (args: LinedArgs kinds inset before trails docs):
    HangLaysAll kinds
      (docs.concatMap (doc => [HardLine, doc]))
      inset
      (AfterWords state indent before)
      (AfterWords state indent trails) :=
  match docs, args with
    | [], same =>
      rewrite same then
        hangsNil kinds inset (AfterWords state indent trails) (AfterWords state indent trails) (place hang holds =>
          holds)
    | [doc, ..rest], (middle, (noted, el), more) =>
      hangsCons
        [doc, ..rest.concatMap (doc => [HardLine, doc])]
        (hardLineArg kinds inset indent state before unglued deeper)
        (hangsCons
          (rest.concatMap (doc => [HardLine, doc]))
          (argLineHangs kinds doc inset indent state middle noted quiet unglued clear el)
          (linedRest kinds rest inset indent state middle trails quiet unglued clear deeper more))

--| Arguments filling lines, laid at `inset`: each after a separator, after a waiting comment only if the one before
--| ended with one.
def FilledArgs (kinds: Text → Tok) (inset: Nat) (before trails: Bool) (docs: List Doc): Prop :=
  Chained (before middle doc => ElHangs kinds doc inset inset before middle wordStart) before trails docs

theorem sepsArgs ∀ (kinds: Text → Tok) (docs: List Doc) (inset indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (deeper: (indent < inset) = True)
    (args: FilledArgs kinds inset before trails docs)
    (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (holds: AfterWords state indent before place (hangOf kinds trace))
    (after: ∀ (left: Place) (later: List Event) => AfterWords state indent trails left (hangOf kinds later)
      → next left later):
    SepsLay docs inset place trace next :=
  match docs, args with
    | [], same => after place trace (rewrite same at holds then holds)
    | [doc, ..rest], (middle, el, more) =>
      lineArg kinds inset indent state before unglued deeper place _ trace
        (seat between => Lays doc inset seat between (left later => SepsLay rest inset left later next))
        byComputing
        holds
        (hangsAfter (seat between ready =>
          argHangs kinds doc inset indent state before middle quiet unglued clear el seat _ between
            (left later => SepsLay rest inset left later next)
            byComputing
            ready
            (hangsAfter (left later done =>
              sepsArgs kinds rest inset indent state middle trails quiet unglued clear deeper more left later next done
                  after))))

--| Where an element laid at `indent` may start, one laid deeper from the same seat may: its first word starts the
--| same line, if any.
theorem enteredDeeper ∀ (indent inset column: Nat) (state: HangState) (entry place: Place) (hang: Hang)
    (deeper: (indent <= inset) = True)
    (entered: Entered indent column False state entry (wordStart indent entry) place hang):
    Entered inset column False state entry (wordStart inset entry) place hang
      ∧ wordStart inset entry = wordStart indent entry :=
  match entry, entered with
    | AtStart _ _ | Broken _ _ | Mid _ _, (isEntry, folded, (seated, _, _, room)) =>
      ((isEntry, folded, (seated, arithmetic, arithmetic, room)), byComputing)
    | Held at carry, (_, _, ((never, _, _), _, _, _)) => (Bool.falseNotTrue never).impossible

--| A call's elements filling lines laid at `inset`, deeper than the call (`Nest 4 (Fill …)`): the function at the
--| call's seat, the arguments after it.
--|
--| Proof idea: the function, laid deeper from the call's seat (`enteredDeeper`), leaves the fold as after its first
--| word, which starts nothing and glues nothing, with nothing in force right of the call's indentation
--| (`openedBound`); each argument then starts after a separator and keeps it (`sepsArgs`).
theorem filledHangs ∀ (kinds: Text → Tok) (head: Doc) (args: List Doc) (more indent column: Nat) (middle trails: Bool)
    (positive: (0 < more) = True)
    (headHangs: ElHangs kinds head (indent + more) column False middle wordStart)
    (filled: FilledArgs kinds (indent + more) middle trails args):
    ElHangs kinds (Nest more (Fill [head, ..args])) indent column False trails wordStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      let inset := indent + more
      let (_, _, (seated, below, clear, room)) := entered
      let opened := openedBy state (wordStart indent entry)
      let bound: (inForce opened.blocks opened.top <= indent) = True := openedBound seated below clear room
      let (deep, same) := enteredDeeper indent inset column state entry place (hangOf kinds trace) arithmetic entered
      headHangs state entry place _ trace
        (left later => SepsLay args inset left later next)
        byComputing
        deep
        (hangsAfter (left later (ended, folded) =>
          sepsArgs kinds args inset indent opened middle trails
            (openedQuietStart state (wordStart indent entry))
            (openedUnglued state (wordStart indent entry))
            bound
            arithmetic
            filled
            left
            later
            next
            (rewrite same at ended then ended, rewrite same at folded then folded, bound)
            (left later (done, landed, _) => after left later (done, landed)))))

--| A broken call's arguments each on a line of its own, laid deeper than the call, as a part after its function.
theorem linedPart ∀ (kinds: Text → Tok) (docs: List Doc) (more indent: Nat) (before trails: Bool)
    (positive: (0 < more) = True)
    (args: LinedArgs kinds (indent + more) before trails docs):
    PartHangs kinds (Nest more (Doc.concat (docs.concatMap (doc => [HardLine, doc])))) indent before trails :=
  state entry quiet unglued =>
    hangsBy (place trace next (isEntry, folded, ended, clear) after =>
      (hangsConcat
            (linedRest kinds docs (indent + more) indent state before trails quiet unglued clear arithmetic args))
          place _ trace next byComputing
          (rewrite isEntry then ended, folded, clear)
          (hangsAfter (left later (done, landed, _) => after left later (done, landed))))

-- A call's layouts.

--| A choice among options that each hang hangs; with one option at least, nothing is asked of where it starts.
theorem hangsOptions ∀ [kinds: Text → Tok] [first: Doc] [others: List Doc] [indent: Nat] [pre post: Place → Hang → Prop]
    (one: HangLays kinds first indent pre post)
    (each: EachHangs kinds indent pre post others):
    HangLays kinds (Choice [first, ..others]) indent pre post :=
  hangsBy (place trace next holds after =>
    match others, each with
      | [], _ => one place _ trace next byComputing holds (hangsAfter after)
      | [second, ..more], (two, rest) => (
        one place _ trace next byComputing holds (hangsAfter after),
        (hangsOptions two rest) place _ trace next byComputing holds (hangsAfter after)
      ))

theorem elFlatten ∀ [kinds: Text → Tok] (doc: Doc) [indent column: Nat] [before trails: Bool]
    (el: ElHangs kinds doc indent column before trails wordStart):
    ElHangs kinds (Flatten doc) indent column before trails wordStart :=
  state entry => hangsFlatten (el state entry)

theorem elChoice ∀ (kinds: Text → Tok) (first: Doc) (others: List Doc) (indent column: Nat) (before trails: Bool)
    (one: ElHangs kinds first indent column before trails wordStart)
    (each: ∀ (state: HangState) (entry: Place) => EachHangs kinds indent
      (Entered indent column before state entry (wordStart indent entry))
      (place hang =>
        Ended (openedBy state (wordStart indent entry)) trails place
          ∧ hang = Hang.At (openedBy state (wordStart indent entry)))
      others):
    ElHangs kinds (Choice [first, ..others]) indent column before trails wordStart :=
  state entry => hangsOptions (one state entry) (each state entry)

--| What a call's layouts ask of its elements (`appFrom`), the function first, the arguments `args`, `k` of them kept
--| on the function's line when the call breaks: spaced on one line, or filling lines at 4 where no comment sits
--| between them (`between`); the kept ones likewise (`betweenFront`) and the rest on lines of their own at 2 or 4;
--| and the hug's opened argument after the others spaced, if it has one.
def AppArgs (kinds: Text → Tok) (indent: Nat) (middle trails between betweenFront: Bool) (args: List Doc) (k: Nat)
    (front: List Doc) (hug: Option Doc):
    Prop :=
  SpacedParts kinds indent middle trails args
    ∧ (between = False → FilledArgs kinds (indent + 4) middle trails args)
    ∧ (∃ (kept: Bool) => SpacedParts kinds indent middle kept (args.take k)
      ∧ (betweenFront = False → FilledArgs kinds (indent + 4) middle kept (args.take k))
      ∧ LinedArgs kinds (indent + 2) kept trails (args.drop k)
      ∧ LinedArgs kinds (indent + 4) kept trails (args.drop k))
    ∧ (∃ (fronted: Bool) => SpacedParts kinds indent middle fronted front
      ∧ (∀ (opened: Doc) => hug = Some opened → PartHangs kinds opened indent fronted trails))

--| The kept elements fill lines only where no comment sits between them.
theorem fillsQuiet ∀ (more betweenFront: Bool) (fills: (more && !betweenFront) = True): betweenFront = False :=
  match more, betweenFront with | True, False => byComputing

--| `appFrom`'s broken layout, `k` arguments kept on the function's line.
def brokenApp (id k: Nat) (fillFront: Bool) (headDoc: Doc) (args: List Doc): Doc :=
  let rest := Doc.concat (args.drop k |> .concatMap (doc => [HardLine, doc]))
  Doc.concat [
    if fillFront then IdGroup id (Nest 4 (Fill [headDoc, ..args.take k])) False else spaced [headDoc, ..args.take k],
    if fillFront then IfBroken id (Nest 4 rest) (Nest 2 rest) else Nest 2 rest
  ]

--| A call broken (`appFrom`'s last option): the function and the kept arguments, spaced or filling lines at 4, then
--| the rest on lines of their own at 2, or at 4 if the kept ones filled lines and broke.
theorem brokenAppHangs ∀ (kinds: Text → Tok) (id k: Nat) (fillFront: Bool) (headDoc: Doc) (args: List Doc)
    (indent column: Nat) (middle kept trails: Bool)
    (head: ∀ (inset: Nat) => ElHangs kinds headDoc inset column False middle wordStart)
    (keptSpaced: SpacedParts kinds indent middle kept (args.take k))
    (keptFilled: fillFront = True → FilledArgs kinds (indent + 4) middle kept (args.take k))
    (restAt2: LinedArgs kinds (indent + 2) kept trails (args.drop k))
    (restAt4: LinedArgs kinds (indent + 4) kept trails (args.drop k)):
    ElHangs kinds (brokenApp id k fillFront headDoc args) indent column False trails wordStart :=
  let rest := args.drop k |> .concatMap (doc => [HardLine, doc])
  let at2: PartHangs kinds (Nest 2 (Doc.concat rest)) indent kept trails :=
    linedPart kinds (args.drop k) 2 indent kept trails byComputing restAt2
  match fillFront with
    | True =>
      let at4: PartHangs kinds (Nest 4 (Doc.concat rest)) indent kept trails :=
        linedPart kinds (args.drop k) 4 indent kept trails byComputing restAt4
      elThen
        (IdGroup id (Nest 4 (Fill [headDoc, ..args.take k])) False)
        (IfBroken id (Nest 4 (Doc.concat rest)) (Nest 2 (Doc.concat rest)))
        (state entry =>
          hangsIdGroup id False
            (filledHangs kinds headDoc
              (args.take k)
              4
              indent
              column
              middle
              kept
              byComputing
              (head (indent + 4))
              (keptFilled byComputing)
              state
              entry))
        (state entry quiet unglued =>
          hangsIfBroken id indent (at4 state entry quiet unglued) (at2 state entry quiet unglued))
    | False =>
      elThen
        (spaced [headDoc, ..args.take k])
        (Nest 2 (Doc.concat rest))
        (spacedHangs (args.take k) (head indent) keptSpaced)
        at2

--| A call (`appFrom`) as one element: whichever layout the printer takes, the fold after it as after its first
--| word.
--|
--| Proof idea: `appFrom`'s cases. All its elements on its line are spaced (`spacedHangs`) or fill lines at 4
--| (`filledHangs`); otherwise it is a choice (`elChoice`) of those flattened, the hug after the others spaced
--| (`elGapThen`), and the call broken (`brokenAppHangs`).
theorem appFromHangs ∀ (kinds: Text → Tok) (id k: Nat) (between betweenFront: Bool) (headDoc: Doc) (front: List Doc)
    (lastDoc: Doc) (hug: Option Doc) (indent column: Nat) (middle trails: Bool)
    (head: ∀ (inset: Nat) => ElHangs kinds headDoc inset column False middle wordStart)
    (facts: AppArgs kinds indent middle trails between betweenFront (front ++ [lastDoc]) k front hug):
    ElHangs kinds
      (appFrom id (k + 1) between betweenFront headDoc front lastDoc hug).doc
      indent
      column
      False
      trails
      wordStart :=
  let args := front ++ [lastDoc]
  let (spacedAll, filledAll, (kept, keptSpaced, keptFilled, restAt2, restAt4), (fronted, frontSpaced, hugged)) := facts
  let all := spaced [headDoc, ..args]
  let allHangs: ElHangs kinds all indent column False trails wordStart := spacedHangs args (head indent) spacedAll
  let pre: HangState → Place → Place → Hang → Prop := state entry =>
    Entered indent column False state entry (wordStart indent entry)
  let post: HangState → Place → Place → Hang → Prop := state entry place hang =>
    Ended (openedBy state (wordStart indent entry)) trails place
      ∧ hang = Hang.At (openedBy state (wordStart indent entry))
  let fillFront := k + 1 > 2 && !betweenFront
  let broken :=
    brokenAppHangs kinds id k fillFront headDoc args indent column middle kept trails head keptSpaced
      (fills => keptFilled (fillsQuiet (k + 1 > 2) betweenFront fills))
      restAt2
      restAt4
  match whole: k + 1 == args.length + 1 with
    | True =>
      match between with
        | True => allHangs
        | False =>
          filledHangs kinds headDoc args 4 indent column middle trails byComputing
            (head (indent + 4))
            (filledAll byComputing)
    | False =>
      match hug, hugged with
        | None, _ =>
          elChoice kinds
            (Flatten all)
            [brokenApp id k fillFront headDoc args]
            indent
            column
            False
            trails
            (elFlatten all allHangs)
            (state entry => (broken state entry, byComputing))
        | Some opened, hugged =>
          let hugDoc := Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", opened]
          let hugHangs: ElHangs kinds hugDoc indent column False trails wordStart :=
            elGapThen
              (Flatten (spaced [headDoc, ..front]))
              (Doc.text " ")
              opened
              (elFlatten (spaced [headDoc, ..front]) (spacedHangs front (head indent) frontSpaced))
              (Inr byComputing)
              (hugged opened byComputing)
          elChoice kinds
            (Flatten all)
            [hugDoc, brokenApp id k fillFront headDoc args]
            indent
            column
            False
            trails
            (elFlatten all allHangs)
            (state entry => (hugHangs state entry, broken state entry, byComputing))

-- Chains of elements.

theorem chainedWeaker ∀ (step weaker: Bool → Bool → Doc → Prop) (before trails: Bool)
    (docs: List Doc) (implies: ∀ (before middle: Bool) (doc: Doc) => step before middle doc → weaker before middle doc)
    (chained: Chained step before trails docs):
    Chained weaker before trails docs :=
  match docs, chained with
    | [], same => same
    | [doc, ..rest], (middle, holds, more) =>
      (middle, implies before middle doc holds, chainedWeaker step weaker middle trails rest implies more)

theorem chainedSnoc ∀ (step: Bool → Bool → Doc → Prop) (before middle trails: Bool) (docs: List Doc) (last: Doc)
    (chained: Chained step before middle docs) (holds: step middle trails last):
    Chained step before trails (docs ++ [last]) :=
  match docs, chained with
    | [], same => rewrite same then (trails, holds, byComputing)
    | [doc, ..rest], (between, first, more) =>
      (between, first, chainedSnoc step between middle trails rest last more holds)

-- A call's arguments.

--| Where a call's argument stands, after the element before it.
def argAround (arm: Bool) (previous: Expr) (at: Nat): Around :=
  { before = previous.trails, hoisted = False, item = False, at, inArm = arm }

--| A call's last argument.
def lastArg (argument: Expr): List Expr → Expr
  | [] => argument
  | [next, ..rest] => lastArg next rest

--| An element that hangs wherever it is laid, seated at its indentation, its first word where `startFor noted` says:
--| on the line after the comments above it, if it writes any (`noted`).
def HangsFor (kinds: Text → Tok) (noted before trails: Bool) (doc: Doc): Prop :=
  ∀ (inset: Nat) => ElHangs kinds doc inset inset before trails (startFor noted)

--| What a call's arguments ask, each after the one before (`previous`, the function at first): each hangs as an
--| element, its first word where `startFor` says for the comments above it, and the last's hug, if it has one, as
--| well.
def ArgsHang (kinds: Text → Tok) (arm: Bool) (previous: Expr) (at: Nat): List Expr → Prop
  | [] => True
  | [argument] =>
    HangsFor kinds argument.noted previous.trails argument.trails
      (lastArgument argument (argAround arm previous at)).fst
      ∧ (∀ (opened: Doc) => (lastArgument argument (argAround arm previous at)).snd = Some opened
        → HangsFor kinds argument.noted previous.trails argument.trails opened)
  | [argument, ..rest] =>
    HangsFor kinds argument.noted previous.trails argument.trails (argument.el (argAround arm previous at))
      ∧ ArgsHang kinds arm argument (at + argument.size) rest

--| An argument's document in a call's chain: it hangs, its first word where `startFor` says, with no comments above
--| it where no comment sits between the call's elements (`between`).
def ArgStep (kinds: Text → Tok) (between before middle: Bool) (doc: Doc): Prop :=
  ∃ (noted: Bool) => HangsFor kinds noted before middle doc ∧ (between = False → noted = False)

--| Where no comment sits between a call's elements from an argument on, that argument has none above it, the element
--| before it ends with none, and none sits between the rest.
theorem betweenParts ∀ (noted trails rest: Bool)
    (quiet: (noted || trails || rest) = False):
    noted = False ∧ rest = False :=
  (
    Bool.orFalseLeft noted (trails || rest) quiet,
    Bool.orFalseRight trails rest (Bool.orFalseRight noted (trails || rest) quiet)
  )

--| An element after words is a part, its first token where `startFor` says: `elPart`, and the same from
--| `endedLead` for an element whose first token has comments above it.
theorem partHangsFor ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails noted: Bool)
    (el: ElHangs kinds doc indent indent before trails (startFor noted)):
    PartHangs kinds doc indent before trails :=
  match noted with
    | False => elPart kinds doc indent before trails el
    | True => state entry quiet unglued =>
      let pre: Place → Hang → Prop := place hang =>
        place = entry
          ∧ hang = Hang.At state
          ∧ Ended state before entry
          ∧ (inForce state.blocks state.top <= indent) = True
      let opened := openedBy state (leadStart indent entry)
      hangsPost
        (hangsPre (el state entry) (place hang (isEntry, folded, ended, clear) =>
          (isEntry, folded, endedLead indent before state entry unglued ended clear)))
        (place hang (ended, folded) =>
          let same: opened = state := openedQuiet (leadStart indent entry) quiet unglued
          (rewrite same at ended then ended, rewrite same at folded then folded))

--| A call's argument documents (`argumentDocs`) hang in turn, from where the function ended, each with no comments
--| above it where none sits between the elements (`between`).
--|
--| Proof idea: by the arguments, as `argumentDocs` builds its documents; the last gives the last document and its
--| hug.
theorem argumentDocsHang ∀ (kinds: Text → Tok) (arm: Bool) (previous: Expr) (at: Nat) (argument: Expr)
    (rest: List Expr) (between: Bool)
    (quiet: between = False → commentBetween previous [argument, ..rest] = False)
    (facts: ArgsHang kinds arm previous at [argument, ..rest]):
    ∃ (fronted: Bool) => Chained
      (ArgStep kinds between)
      previous.trails
      fronted
      (argumentDocs arm previous at [argument, ..rest]).fst
      ∧ ArgStep kinds between fronted
        (lastArg argument rest).trails
        ((argumentDocs arm previous at [argument, ..rest]).snd.getOrElse (Nothing, None)).fst
      ∧ (∀ (opened: Doc) => ((argumentDocs arm previous at [argument, ..rest]).snd.getOrElse (Nothing, None)).snd
        = Some opened
        → ∃ (noted: Bool) => HangsFor kinds noted fronted (lastArg argument rest).trails opened) :=
  let unnoted: between = False → argument.noted = False := none =>
    (betweenParts argument.noted previous.trails (commentBetween argument rest) (quiet none)).left
  match rest, facts with
    | [], (last, hug) =>
      (previous.trails, byComputing, (argument.noted, last, unnoted), opened same => (argument.noted, hug opened same))
    | [following, ..more], (first, others) =>
      let (fronted, chain, last, hug) :=
        argumentDocsHang kinds arm argument
          (at + argument.size)
          following
          more
          between
          (none =>
            (betweenParts argument.noted previous.trails
              (commentBetween argument [following, ..more])
              (quiet none)).right)
          others
      (fronted, (argument.trails, (argument.noted, first, unnoted), chain), last, hug)

--| A call's argument documents cut where those kept on its line end (`keptFront`): the kept ones in turn, each with
--| no comments above it where none sits between them (`betweenFront`), then the rest.
--|
--| Proof idea: by the arguments, as `keptFront` counts them; where it stops, the rest are all of
--| `argumentDocsHang`'s chain.
theorem keptArgsHang ∀ (kinds: Text → Tok) (arm: Bool) (previous: Expr) (at: Nat) (argument: Expr)
    (rest: List Expr) (betweenFront: Bool)
    (quiet: betweenFront = False
      → commentBetween previous ([argument, ..rest].take (keptFront previous [argument, ..rest])) = False)
    (facts: ArgsHang kinds arm previous at [argument, ..rest]):
    ∃ (kept: Bool) => Chained
      (ArgStep kinds betweenFront)
      previous.trails
      kept
      (((argumentDocs arm previous at [argument, ..rest]).fst
        ++ [((argumentDocs arm previous at [argument, ..rest]).snd.getOrElse (Nothing, None)).fst]).take
        (keptFront previous [argument, ..rest]))
      ∧ Chained
        (ArgStep kinds True)
        kept
        (lastArg argument rest).trails
        (((argumentDocs arm previous at [argument, ..rest]).fst
          ++ [((argumentDocs arm previous at [argument, ..rest]).snd.getOrElse (Nothing, None)).fst]).drop
          (keptFront previous [argument, ..rest])) :=
  match keeps: argument.simple && !previous.trails with
    | False =>
      let (fronted, chain, last, _) :=
        argumentDocsHang kinds arm previous at argument rest True (never => (Bool.trueNotFalse never).impossible) facts
      (
        previous.trails,
        byComputing,
        chainedSnoc (ArgStep kinds True) previous.trails fronted (lastArg argument rest).trails _ _ chain last
      )
    | True =>
      let unnoted: betweenFront = False → argument.noted = False := none =>
        (betweenParts argument.noted previous.trails _ (quiet none)).left
      match rest, facts with
        | [], (last, _) => (
          (lastArg argument []).trails,
          ((lastArg argument []).trails, (argument.noted, last, unnoted), byComputing),
          byComputing
        )
        | [following, ..more], (first, others) =>
          let (kept, keptChain, restChain) :=
            keptArgsHang kinds arm argument
              (at + argument.size)
              following
              more
              betweenFront
              (none => (betweenParts argument.noted previous.trails _ (quiet none)).right)
              others
          (kept, (argument.trails, (argument.noted, first, unnoted), keptChain), restChain)

--| `appDocs` as `appFrom` takes it, the count of elements kept on the call's line written `k + 1`.
theorem appDocsIs ∀ (head: Expr) (arguments: List Expr) (around: Around):
    appDocs head arguments around
      = appFrom
        (around.at + 1)
        (keptFront head arguments + 1)
        (commentBetween head arguments)
        (commentBetween head (arguments.take (keptFront head arguments)))
        (head.el around)
        (argumentDocs around.inArm head (around.at + head.size) arguments).fst
        ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).fst
        ((argumentDocs around.inArm head (around.at + head.size) arguments).snd.getOrElse (Nothing, None)).snd :=
  rewrite Nat.addComm 1 (keptFront head arguments)

--| A call's parts (`appDocs`) as one element, the fold after them as after its function's first word.
--|
--| Proof idea: `appDocsIs` and `appFromHangs`; what each layout asks of the elements comes from each argument
--| hanging wherever it is laid (`argumentDocsHang`, `keptArgsHang`): spaced, it is a part (`partHangsFor`); on a
--| line of its own, it starts after no waiting comment (`elUnheld`), at a line start, where its comments change
--| nothing; filling lines, only where no comment sits between the elements, so it has none above it.
theorem appDocsHangs ∀ (kinds: Text → Tok) (head argument: Expr) (rest: List Expr) (around: Around) (indent column: Nat)
    (headHangs: ∀ (inset: Nat) => ElHangs kinds (head.el around) inset column False head.trails wordStart)
    (facts: ArgsHang kinds around.inArm head (around.at + head.size) [argument, ..rest]):
    ElHangs kinds
      (appDocs head [argument, ..rest] around).doc
      indent
      column
      False
      (lastArg argument rest).trails
      wordStart :=
  let arguments := [argument, ..rest]
  let docs := argumentDocs around.inArm head (around.at + head.size) arguments
  let front := docs.fst
  let lastDoc := (docs.snd.getOrElse (Nothing, None)).fst
  let hug := (docs.snd.getOrElse (Nothing, None)).snd
  let k := keptFront head arguments
  let trails := (lastArg argument rest).trails
  let between := commentBetween head arguments
  let betweenFront := commentBetween head (arguments.take k)
  let (fronted, chain, last, hugs) :=
    argumentDocsHang kinds around.inArm head (around.at + head.size) argument rest between (none => none) facts
  let all := chainedSnoc (ArgStep kinds between) head.trails fronted trails front lastDoc chain last
  let spacedOf: ∀ (quiet before after: Bool) (docs: List Doc) (chained: Chained
    (ArgStep kinds quiet)
    before
    after
    docs) => SpacedParts kinds indent before after docs :=
    quiet before after docs chained =>
      chainedWeaker
        (ArgStep kinds quiet)
        (before middle doc => PartHangs kinds doc indent before middle)
        before
        after
        docs
        (before middle doc (noted, hangs, _) => partHangsFor kinds doc indent before middle noted (hangs indent))
        chained
  let filledOf: ∀ (quiet before after: Bool) (docs: List Doc) (chained: Chained
    (ArgStep kinds quiet)
    before
    after
    docs) => quiet = False → FilledArgs kinds (indent + 4) before after docs :=
    quiet before after docs chained none =>
      chainedWeaker
        (ArgStep kinds quiet)
        (before middle doc => ElHangs kinds doc (indent + 4) (indent + 4) before middle wordStart)
        before
        after
        docs
        (before middle doc (noted, hangs, unnoted) => rewrite unnoted none at hangs then hangs (indent + 4))
        chained
  let (kept, keptChain, restChain) :=
    keptArgsHang kinds around.inArm head (around.at + head.size) argument rest betweenFront (none => none) facts
  let lined: ∀ (more: Nat) => LinedArgs kinds (indent + more) kept trails ((front ++ [lastDoc]).drop k) := more =>
    chainedWeaker
      (ArgStep kinds True)
      (before middle doc =>
        ∃ (noted: Bool) => ElHangs kinds doc (indent + more) (indent + more) False middle (startFor noted))
      kept
      trails
      ((front ++ [lastDoc]).drop k)
      (before middle doc (noted, hangs, _) =>
        (
          noted,
          elUnheld kinds doc (indent + more) (indent + more) before middle (startFor noted) (hangs (indent + more))
        ))
      restChain
  let hugged: ∀ (opened: Doc) => hug = Some opened → PartHangs kinds opened indent fronted trails := opened same =>
    let (noted, hangs) := hugs opened same
    partHangsFor kinds opened indent fronted trails noted (hangs indent)
  rewrite appDocsIs head arguments around then
    appFromHangs kinds
      (around.at + 1)
      k
      between
      betweenFront
      (head.el around)
      front
      lastDoc
      hug
      indent
      column
      head.trails
      trails
      headHangs
      (
        spacedOf between head.trails trails (front ++ [lastDoc]) all,
        filledOf between head.trails trails (front ++ [lastDoc]) all,
        (
          kept,
          spacedOf betweenFront head.trails kept ((front ++ [lastDoc]).take k) keptChain,
          filledOf betweenFront head.trails kept ((front ++ [lastDoc]).take k) keptChain,
          lined 2,
          lined 4
        ),
        (fronted, spacedOf between head.trails fronted front chain, hugged)
      )

--| A call (`App`) as an element, framed, the call's own-line comments written elsewhere or none.
theorem appElHangs ∀ (kinds: Text → Tok) (head argument: Expr) (rest: List Expr) (around: Around) (indent column: Nat)
    (bare: (App head [argument, ..rest]).firstWord.leading around around.at = [])
    (headHangs: ∀ (inset seat: Nat) => ElHangs kinds
      (head.el { around | hoisted = True })
      inset
      seat
      False
      head.trails
      wordStart)
    (facts: ArgsHang kinds around.inArm head (around.at + head.size) [argument, ..rest]):
    ElHangs kinds
      (Expr.el (App head [argument, ..rest]) around)
      indent
      column
      around.before
      (lastArg argument rest).trails
      wordStart :=
  let inside := { around | hoisted = True }
  framedHangs
    (App head [argument, ..rest]).firstWord
    (appDocs head [argument, ..rest] inside).doc
    indent
    column
    (lastArg argument rest).trails
    bare
    (inset seat =>
      appDocsHangs kinds head argument rest inside inset seat (headInset => headHangs headInset seat) facts)
