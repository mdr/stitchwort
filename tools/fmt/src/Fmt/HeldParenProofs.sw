--| `printedHangs` for a `paren` whose opener ends its line with a comment (ticket 18g): what the brackets hold then
--| starts a line, on the comment break at `s = max indent (at + 2)`, `at` the opener's line, so the bracket's block
--| is `Some s`, and a closer that takes a line of its own must land left of `s`.
--|
--| It does, by the opener's mark: the opener is on the line `at` (`lineOpeningHangs`), and the contents' first word
--| breaks to `s` before anything else (`HeldLowers`), which lowers the mark to at most `s`; later lines only lower
--| it further (`framed`). So the closer lands at `min at indent < s` if a line since the opener is at or left of
--| the indentation, else at the indentation, left of that line and so of `s` (`heldFits`).

namespace Fmt.HeldParenProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Expr, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.MarkProofs (..)
import Fmt.BracketHangProofs (..)
import Syntax.SharedFacts (solidSpaces)

-- The opener's line.

theorem withCarryLine ∀ (place: Place) (carry: Carry): (place.withCarry carry).indent = place.indent := match place with
  | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _ => byComputing

--| A word written at a seat that no comment waits at stays on the seat's line.
theorem wordAfterLine ∀ (indent column: Nat) (text: Text) (state: HangState) (place: Place)
    (seated: Seated column False state place):
    (wordAfter indent text place).indent = place.indent :=
  match place, seated with
    | AtStart _ _ | Broken _ _ | Mid _ _, _ => byComputing
    | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible

--| `openerStep`, the opener staying on the line `line`.
theorem lineOpenerStep ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (state: HangState)
    (start: Option Nat) (line: Nat)
    (token: OpenerToken kinds text):
    HangLays kinds
      (Doc.text text)
      indent
      (place hang =>
        (hang = Hang.At state
          ∧ Seated column False state place
          ∧ Room state (wordStart indent place)
          ∧ wordStart indent place = start)
          ∧ place.indent = line)
      (place hang =>
        (Ended (openingBy state start) False place ∧ hang = Hang.At (openingBy state start)) ∧ place.indent = line) :=
  let (opener, closer, comma, assign, colon, arrow, notComment, solid, _, _) := token
  hangsChunk kinds text text.length indent
    (place hang =>
      (hang = Hang.At state
        ∧ Seated column False state place
        ∧ Room state (wordStart indent place)
        ∧ wordStart indent place = start)
        ∧ place.indent = line)
    (place hang =>
      (Ended (openingBy state start) False place ∧ hang = Hang.At (openingBy state start)) ∧ place.indent = line)
    solid
    (place trace ((folded, seated, room, same), onLine) =>
      let ended := wordEnded notComment seated room
      let stepped :=
        stepOpener kinds state text
          (wordStart indent place)
          (tokenCode text (wordStart indent place) notComment solid)
          opener
          closer
          comma
          assign
          colon
          arrow
          room
      rewrite folded then
        (
          (openingEnded state start False _ (rewrite same at ended then ended), rewrite stepped, same),
          Eq.trans (wordAfterLine indent column text state place seated) onLine
        ))

--| `trailingHangs`, the token staying on the line `line`.
theorem lineTrailingHangs ∀ (kinds: Text → Tok) (word: Word) (indent: Nat) (state: HangState) (line: Nat)
    (trailed: TrailsComment word):
    HangLaysAll kinds word.trailing indent
      (place hang => (Ended state False place ∧ hang = Hang.At state) ∧ place.indent = line)
      (place hang => (Ended state word.trails place ∧ hang = Hang.At state) ∧ place.indent = line) :=
  let pre: Place → Hang → Prop := place hang => (Ended state False place ∧ hang = Hang.At state) ∧ place.indent = line
  let post: Place → Hang → Prop := place hang => (Ended state True place ∧ hang = Hang.At state) ∧ place.indent = line
  match after: word.comments.after, trailed with
    | None, _ => hangsNil kinds indent pre pre (place hang held => held)
    | Some comment, (isComment, layout) =>
      hangsLast
        (hangsSuffix kinds indent pre post isComment layout (place hang ((ended, folded), onLine) =>
          match place, ended, onLine with
            | Mid at carry, (floor, left), onLine =>
              (at, carry, (byComputing, ((byComputing, floor, left), folded), onLine))
            | Held at carry, (never, _, _), _ => (Bool.falseNotTrue never).impossible
            | AtStart at carry, never, _ => (Bool.falseNotTrue never).impossible
            | Broken at carry, never, _ => (Bool.falseNotTrue never).impossible))

--| `markedOpeningHangs`, and the place after the opener is on the opener's line.
--|
--| Proof idea: as `markedOpeningHangs`, each step also carrying the line: the `Mark` changes only the carry
--| (`withCarryLine`), the opener is written at a seat no comment waits at (`wordAfterLine`), and its trailing
--| comment waits on the same line.
theorem lineOpeningHangs ∀ (kinds: Text → Tok) (word closer: Word) (around: Around) (indent column: Nat)
    (state: HangState) (entry: Place)
    (token: OpenerToken kinds word.text)
    (hoisted: around.hoisted = True)
    (trailed: TrailsComment word)
    (marks: (closer.noted || closer.trails) = True):
    HangLays kinds
      (word.opening around closer)
      indent
      (Entered indent column False state entry (wordStart indent entry))
      (place hang =>
        ((Ended (openingBy state (wordStart indent entry)) word.trails place
          ∧ hang = Hang.At (openingBy state (wordStart indent entry)))
          ∧ place.indent = entry.indent)
          ∧ MarksKept (around.at + 1) (markedCarry around.at entry) place.carry) :=
  let (_, _, _, _, _, _, _, _, notCloser, notComma) := token
  let start := wordStart indent entry
  let opened := openingBy state start
  let origin := markedCarry around.at entry
  let low := around.at + 1
  let line := entry.indent
  let ready: Place → Hang → Prop := place hang =>
    (hang = Hang.At state
      ∧ Seated column False state place
      ∧ Room state (wordStart indent place)
      ∧ wordStart indent place = start)
      ∧ place.indent = line
  let written: Place → Hang → Prop := place hang =>
    (Ended opened False place ∧ hang = Hang.At opened) ∧ place.indent = line
  let post: Place → Hang → Prop := place hang =>
    (Ended opened word.trails place ∧ hang = Hang.At opened) ∧ place.indent = line
  let rest: HangLaysAll kinds [Doc.text word.text, ..word.trailing] indent ready post :=
    hangsCons word.trailing
      (lineOpenerStep kinds word.text indent column state start line token)
      (lineTrailingHangs kinds word indent opened line trailed)
  let kept := allHangsKept [docs := [Doc.text word.text, ..word.trailing]] low origin (trailingKeys low word) rest
  rewrite hoisted, notCloser, notComma, marks then
    hangsConcat
      (hangsCons
        [Doc.text word.text, ..word.trailing]
        (hangsMark kinds around.at indent
          (Entered indent column False state entry start)
          (place hang => ready place hang ∧ MarksKept low origin place.carry)
          (place hang (isEntry, folded, (seated, _, _, room)) =>
            let (stays, same) := markSeated indent column around.at False state place (rewrite isEntry then seated)
            (
              (
                (folded, stays, rewrite same, isEntry then room, rewrite same, isEntry),
                rewrite isEntry then withCarryLine entry (entry.carry.mark around.at entry.indent)
              ),
              rewrite Doc.Proofs.withCarryCarry place (place.carry.mark around.at place.indent), isEntry then
                keptRefl low origin
            )))
        kept)

-- The contents' first line break.

--| From where a comment waits, every way `doc` lays out breaks to the comment break first, so the marks below `low`
--| are kept against the carry that break leaves: its line, `max indent (at + 2)`, lowered every open mark to it.
def HeldLowers (doc: Doc) (indent low: Nat): Prop :=
  ∀ (at: Nat) (carry: Carry) (trace: List Event) (next: Place → List Event → Prop) => Lays doc indent
    (Held at carry)
    trace
    (after later => MarksKept low (carry.breakTo (Nat.max indent (at + 2))) after.carry → next after later)
    → Lays doc indent (Held at carry) trace next

--| A displaced element: its contents start on the comment break.
theorem displacedLowers ∀ (doc: Doc) (indent low: Nat)
    (keys: keysFrom low doc = True):
    HeldLowers (Displaced doc) indent low :=
  at carry trace next lays =>
    framed low
      (carry.breakTo (Nat.max indent (at + 2)))
      (Nat.max indent (at + 2))
      (Broken (floored carry (Nat.max indent (at + 2))) (carry.breakTo (Nat.max indent (at + 2))))
      trace
      next
      keys
      (keptRefl low (carry.breakTo (Nat.max indent (at + 2))))
      lays

--| A node whose first token has no own-line comments, after a waiting comment, is displaced.
theorem framedDisplaced ∀ (first: Word) (around: Around) (doc: Doc)
    (bare: first.leading around around.at = [])
    (before: around.before = True):
    framedBy first around doc = Displaced doc :=
  rewrite bare then
    match placed: first.displaces around with
      | True => byComputing
      | False => (Bool.falseNotTrue (Eq.trans (displacesUnheld first around placed).flipped before)).impossible

theorem framedLowers ∀ (first: Word) (around: Around) (doc: Doc) (indent low: Nat)
    (bare: first.leading around around.at = [])
    (before: around.before = True)
    (keys: keysFrom low doc = True):
    HeldLowers (framedBy first around doc) indent low :=
  rewrite framedDisplaced first around doc bare before then displacedLowers doc indent low keys

--| A word written where a comment waits starts the comment break's line.
theorem heldWrite ∀ (indent low: Nat) (text: Text) (at: Nat) (carry: Carry)
    (trace: List Event) (next: Place → List Event → Prop)
    (solid: isLayout text = False)
    (lays: WriteLays indent text (Held at carry) trace (after later =>
      MarksKept low (carry.breakTo (Nat.max indent (at + 2))) after.carry → next after later)):
    WriteLays indent text (Held at carry) trace next :=
  let origin := carry.breakTo (Nat.max indent (at + 2))
  rewrite wordFilled text solid, solidSpaces text solid at lays then
    match lays with
      | (line, reached) =>
        rewrite wordFilled text solid, solidSpaces text solid then
          (line, reached (keptFloorAfter low text origin origin (keptRefl low origin)))

--| A word, then more, written where a comment waits: the word starts the comment break's line.
theorem heldWriteThen ∀ (indent low: Nat) (text: Text) (rest: List Doc) (at: Nat) (carry: Carry)
    (trace: List Event) (next: Place → List Event → Prop)
    (solid: isLayout text = False)
    (keys: allKeysFrom low rest = True)
    (lays: LaysAll [Doc.text text, ..rest] indent (Held at carry) trace (after later =>
      MarksKept low (carry.breakTo (Nat.max indent (at + 2))) after.carry → next after later)):
    LaysAll [Doc.text text, ..rest] indent (Held at carry) trace next :=
  let origin := carry.breakTo (Nat.max indent (at + 2))
  let broken := floored carry (Nat.max indent (at + 2))
  rewrite wordFilled text solid, solidSpaces text solid at lays then
    match lays with
      | (line, reached) =>
        rewrite wordFilled text solid, solidSpaces text solid then
          (
            line,
            allFramed low origin indent
              (Mid broken (floorAfter text origin))
              (trace ++ [{ word = text, start = Some broken }])
              next
              keys
              (keptFloorAfter low text origin origin (keptRefl low origin))
              reached
          )

--| A token with no own-line comments: written first.
theorem leafLowers ∀ (word: Word) (around: Around) (key indent low: Nat)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (bare: word.leading around key = []):
    HeldLowers (word.leaf around key) indent low :=
  rewrite leafIsText word around key closer comma bare then
    match after: word.comments.after with
      | None => at carry trace next lays => heldWrite indent low word.text at carry trace next solid lays
      | Some comment => at carry trace next lays =>
        heldWriteThen indent low word.text [LineSuffix comment] at carry trace next solid byComputing lays

-- The closer's line.

theorem lowestBelow ∀ (least: Option Nat) (at: Nat): (lowest least at <= at) = True := match least with
  | None => Nat.leRefl at
  | Some known => arithmetic

--| A closer's line of its own, its opener on the line `line` and the mark lowered since to at most the comment
--| break's line `max indent (line + 2)`, the block: left of the block and not left of what is in force outside.
theorem heldFitsAt ∀ (key indent line outside: Nat) (carry: Carry) (markKey marked least: Nat)
    (found: carry.marks.find (mark => mark.key == key) = Some { key = markKey, marked, least = Some least })
    (onLine: marked = line)
    (under: (least <= Nat.max indent (line + 2)) = True)
    (atOpener: (outside <= line) = True)
    (clear: (outside <= indent) = True):
    CloserFits key indent (Some (Nat.max indent (line + 2))) outside carry :=
  rewrite found, onLine then match low: least <= indent with | True | False => (arithmetic, arithmetic)

--| As `heldFitsAt`, from the marks kept: against the opener's mark at the comment's place `held`, and against the
--| carry the comment break left.
theorem heldFits ∀ (low key indent line outside: Nat) (held final: Carry)
    (below: (key < low) = True)
    (opened: MarkBelow (held.marks.find (mark => mark.key == key)) { key, marked = line, least = None })
    (floor: held.floor = None)
    (kept: MarksKept low (held.breakTo (Nat.max indent (line + 2))) final)
    (atOpener: (outside <= line) = True)
    (clear: (outside <= indent) = True):
    CloserFits key indent (Some (Nat.max indent (line + 2))) outside final :=
  let column := Nat.max indent (line + 2)
  let landed: floored held column = column := rewrite floor
  match was: held.marks.find (mark => mark.key == key), opened with
    | Some old, (same, _) =>
      let lowered := { old | least = Some (lowest old.least (floored held column)) }
      let lowerFound: (held.breakTo column).marks.find (mark => mark.key == key) = Some lowered :=
        rewrite findLower (floored held column) key held.marks, was
      let below := kept key lowered below lowerFound
      let atMost: ∀ (least: Nat) => (least <= lowest old.least (floored held column)) = True
        → (least <= column) = True :=
        least under =>
          let under: (least <= lowest old.least column) = True := rewrite landed at under then under
          let bound := lowestBelow old.least column
          arithmetic
      laterFits key indent line outside final lowered
        (lowest old.least (floored held column))
        (final.marks.find (mark => mark.key == key))
        byComputing
        byComputing
        below
        (Eq.trans byComputing same)
        atMost
        atOpener
        clear
    | None, never => (Bool.falseNotTrue never).impossible

theorem laterFits ∀ (key indent line outside: Nat) (final: Carry) (mark: OpenMark) (bound: Nat) (later: Option OpenMark)
    (seen: mark.least = Some bound)
    (now: final.marks.find (found => found.key == key) = later)
    (below: MarkBelow later mark)
    (onLine: mark.marked = line)
    (atMost: ∀ (least: Nat) => under (Some least) mark.least = True → (least <= Nat.max indent (line + 2)) = True)
    (atOpener: (outside <= line) = True)
    (clear: (outside <= indent) = True):
    CloserFits key indent (Some (Nat.max indent (line + 2))) outside final :=
  match later, below with
    | Some { key = markKey, marked, least = Some least }, (sameLine, lower) =>
      heldFitsAt key indent line outside final markKey marked least now
        (Eq.trans sameLine onLine)
        (atMost least lower)
        atOpener
        clear
    | Some { key = markKey, marked, least = None }, (_, never) =>
      (Bool.falseNotTrue (rewrite seen at never then never)).impossible
    | None, never => (Bool.falseNotTrue never).impossible

-- The paren.

--| After an opener whose comment waits: the bracket's block open with no column yet, and where the closer may take a
--| line of its own (`flag`), the opener's mark kept and the comment waiting on the opener's line.
def HeldGap (outer: List (Option Nat)) (top: Option Nat) (flag: Bool) (low: Nat) (origin: Carry) (line: Nat):
    Place → Hang → Prop :=
  place hang =>
    ItemGap outer top True place hang ∧ (flag = True → MarksKept low origin place.carry ∧ place.indent = line)

--| After what the brackets hold: the bracket's block at the column it started a line at, if it did, at the
--| indentation or right of it, and where the closer may take a line of its own (`flag`), room for that line.
def HeldDone (indent key: Nat) (outer: List (Option Nat)) (top: Option Nat) (flag trails: Bool): Place → Hang → Prop :=
  place hang =>
    ∃ (block: Option Nat) => deepFrom indent block = True
      ∧ (Ended (bracketState outer top block False) trails place ∧ hang = Hang.At (bracketState outer top block False))
      ∧ (flag = True → CloserFits key indent block (inForce outer top) place.carry)

--| The opener, its comment waiting after it.
theorem heldOpening ∀ (kinds: Text → Tok) (open close: Word) (around: Around) (indent column: Nat)
    (state: HangState) (entry: Place)
    (token: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (trailed: TrailsComment open)
    (trails: open.trails = True):
    HangLays kinds
      (open.opening around close)
      indent
      (Entered indent column False state entry (wordStart indent entry))
      (HeldGap
        (openedBy state (wordStart indent entry)).blocks
        (openedBy state (wordStart indent entry)).top
        (close.noted || close.trails)
        (around.at + 1)
        (markedCarry around.at entry)
        entry.indent) :=
  let start := wordStart indent entry
  let pre := Entered indent column False state entry start
  let gap :=
    HeldGap
      (openedBy state start).blocks
      (openedBy state start).top
      (close.noted || close.trails)
      (around.at + 1)
      (markedCarry around.at entry)
      entry.indent
  Bool.inspect
    (close.noted || close.trails)
    (_ => HangLays kinds (open.opening around close) indent pre gap)
    (marks =>
      hangsPost
        (lineOpeningHangs kinds open close around indent column state entry token hoisted trailed marks)
        (place hang (((ended, folded), line), kept) =>
          ((rewrite trails at ended then ended, folded), _ => (kept, line))))
    (marks =>
      hangsPost (openingHangs close indent column state entry token hoisted trailed) (place hang (ended, folded) =>
        (
          (rewrite trails at ended then ended, folded),
          never => (Bool.falseNotTrue (Eq.trans marks.flipped never)).impossible
        )))

--| The opener's mark is still open, on the opener's line, wherever its keys were kept: a closer's line of its own
--| lands left of what no item started a line at.
theorem keptFits ∀ (low key indent line outside: Nat) (entry: Place) (carry: Carry)
    (below: (key < low) = True)
    (onLine: entry.indent = line)
    (kept: MarksKept low (markedCarry key entry) carry)
    (atOpener: (outside <= line) = True)
    (clear: (outside <= indent) = True):
    CloserFits key indent None outside carry :=
  let was := kept key { key, marked = entry.indent, least = None } below (markedFound key entry)
  match found: carry.marks.find (found => found.key == key) with
    | Some mark =>
      let (same, _) := was
      closerFitsOf key indent None outside line carry mark found (Eq.trans same onLine) atOpener clear byComputing

--| What the brackets hold, after the opener's waiting comment: it starts on the comment break, or mid-line.
--|
--| Proof idea: the contents are an element seated where the opener ended (`endedSeat`), which leaves the block at
--| the column its first word started a line at, if it did. Where the closer may need it, the opener's mark is kept
--| through the contents (`framed`); mid-line the block has no column and the mark gives the room (`keptFits`); on
--| the comment break the contents lower the mark to that break's line first (`HeldLowers`), so a closer's line lands
--| left of it (`heldFits`).
theorem heldInner ∀ (kinds: Text → Tok) (doc: Doc) (indent key: Nat) (entry: Place) (outer: List (Option Nat))
    (top: Option Nat) (flag trails: Bool)
    (bound: (inForce outer top <= indent) = True)
    (atOpener: (inForce outer top <= entry.indent) = True)
    (el: ElHangs kinds doc indent indent True trails wordStart)
    (lowers: HeldLowers doc indent (key + 1))
    (keys: keysFrom (key + 1) doc = True):
    HangLays kinds doc indent
      (HeldGap outer top flag (key + 1) (markedCarry key entry) entry.indent)
      (HeldDone indent key outer top flag trails) :=
  let low := key + 1
  let origin := markedCarry key entry
  let state := itemState outer top
  hangsBy (place trace next ((ended, folded), cond) after =>
    let seat := endedSeat indent True state place byComputing ended bound
    let (seated, _, _, _) := seat
    let deep := seatDeep place seated
    let entered: Entered indent indent True state place (wordStart indent place) place (hangOf kinds trace) :=
      (byComputing, folded, seat)
    match marks: flag with
      | False =>
        (el state place) place _ trace next byComputing entered
          (hangsAfter (later laid (done, landed) =>
            after later laid (
              wordStart indent place,
              deep,
              (
                rewrite openedItem outer top (wordStart indent place) at done then done,
                rewrite openedItem outer top (wordStart indent place) at landed then landed
              ),
              never => (Bool.falseNotTrue never).impossible
            )))
      | True =>
        let (kept, line) := cond byComputing
        match place, ended with
          | Mid at carry, ended =>
            let seat := endedSeat indent True state (Mid at carry) byComputing ended bound
            let entered: Entered indent indent True state (Mid at carry) None (Mid at carry) (hangOf kinds trace) :=
              (byComputing, folded, seat)
            framed low origin indent
              (Mid at carry)
              trace
              next
              keys
              kept
              (el state
                (Mid at carry)
                (Mid at carry) _
                trace
                (later laid => MarksKept low origin later.carry → next later laid)
                byComputing
                entered
                (hangsAfter (later laid (done, landed) keptEnd =>
                  after later laid (
                    None,
                    byComputing,
                    (done, landed),
                    _ =>
                      keptFits low key indent entry.indent
                        (inForce outer top)
                        entry
                        later.carry
                        arithmetic
                        byComputing
                        keptEnd
                        atOpener
                        bound
                  ))))
          | Held at carry, (waits, floor, left) =>
            let column := Nat.max indent (at + 2)
            let seat := endedSeat indent True state (Held at carry) byComputing (waits, floor, left) bound
            let (seated, _, _, _) := seat
            let deep := seatDeep (Held at carry) seated
            let entered: Entered indent indent True state
              (Held at carry)
              (wordStart indent (Held at carry))
              (Held at carry)
              (hangOf kinds trace) :=
              (byComputing, folded, seat)
            let onLine: at = entry.indent := line
            let landed: floored carry column = column := rewrite floor
            let opened := kept key { key, marked = entry.indent, least = None } arithmetic (markedFound key entry)
            lowers at carry trace next
              (framed low origin indent
                (Held at carry)
                trace
                (later laid => MarksKept low (carry.breakTo column) later.carry → next later laid)
                keys
                kept
                (el state
                  (Held at carry)
                  (Held at carry) _
                  trace
                  (later laid =>
                    MarksKept low origin later.carry
                      → MarksKept low (carry.breakTo column) later.carry
                      → next later laid)
                  byComputing
                  entered
                  (hangsAfter (later laid (done, folds) _ lowered =>
                    after later laid (
                      Some (floored carry column),
                      deep,
                      (done, folds),
                      _ =>
                        rewrite landed, onLine then
                          heldFits low key indent entry.indent
                            (inForce outer top)
                            carry
                            later.carry
                            arithmetic
                            opened
                            floor
                            (rewrite onLine at lowered then lowered)
                            atOpener
                            bound
                    ))))))

--| The closer, where what the brackets hold ended: its block gone, the fold as after the opener alone.
theorem heldCloser ∀ (kinds: Text → Tok) (close: Word) (closeAround: Around) (key indent: Nat)
    (outer: List (Option Nat)) (top: Option Nat)
    (token: CloserToken kinds close.text)
    (hoisted: closeAround.hoisted = False)
    (single: closeAround.item = False)
    (comments: NotesComment close.comments.above)
    (trailed: TrailsComment close)
    (bound: (inForce outer top <= indent) = True):
    HangLays kinds
      (close.leaf closeAround key)
      indent
      (HeldDone indent key outer top (close.noted || close.trails) closeAround.before)
      (place hang =>
        Ended { blocks = outer, top, start = False, glue = False } (close.trails || closeAround.before) place
          ∧ hang = Hang.At { blocks = outer, top, start = False, glue = False }) :=
  hangsBy (place trace next (block, deep, (ended, folded), fits) after =>
    let state := bracketState outer top block False
    let nested: (inForce outer top <= inForce [block, ..outer] top) = True := match block, deep with
      | None, _ => Nat.leRefl (inForce outer top)
      | Some column, deep => arithmetic
    let fold: CloserFold indent state block outer := (byComputing, byComputing, nested, bound)
    let seat: CloserSeat indent closeAround.before (close.lone closeAround) state place := match place, ended with
      | Mid at carry, (floor, left) => (floor, left)
      | Held at carry, (waits, floor, left) => (waits, floor, left)
    let lineFits: (close.noted || close.lone closeAround) = True
      → CloserFits key indent block (inForce outer state.top) place.carry :=
      line => fits (loneMarks close closeAround line)
    closerLeafHangs kinds close closeAround key indent state block outer token fold hoisted single comments trailed
        place _ trace next byComputing
        (folded, seat, lineFits)
        (hangsAfter after))

--| A `paren` holding anything `parenInner` writes as it is, its opener ending its line with a comment, as one
--| element.
--|
--| Proof idea: as `parenHangs`, from the opener with its comment waiting (`heldOpening`), what the brackets hold
--| seated after it (`heldInner`), which starts on the comment break or mid-line, and the closer (`heldCloser`). Where
--| the closer may take a line of its own, `heldInner` gives it room: the opener's mark, on the opener's line, lowered
--| to the comment break's line by the contents' first word.
theorem parenHeldHangs ∀ (kinds: Text → Tok) (open: Word) (inner: Expr) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (openTrailed: TrailsComment open)
    (trails: open.trails = True)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (plain: parenInner inner (around.next open.trails 1) = inner.el (around.next open.trails 1))
    (innerHangs: ElHangs kinds (inner.el (around.next open.trails 1)) indent indent True inner.trails wordStart)
    (lowers: HeldLowers (inner.el (around.next open.trails 1)) indent (around.at + 1))
    (keys: keysFrom (around.at + 1) (inner.el (around.next open.trails 1)) = True):
    ElHangs kinds (parenDoc open inner close around) indent column False (close.trails || inner.trails) wordStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      let (_, _, (seated, below, clear, room)) := entered
      let start := wordStart indent entry
      let opened := openedBy state start
      let outer := opened.blocks
      let top := opened.top
      let low := around.at + 1
      let origin := markedCarry around.at entry
      let flag := close.noted || close.trails
      let innerAround := around.next open.trails 1
      let innerDoc := inner.el innerAround
      let closeAround := around.next inner.trails (1 + inner.size)
      let closerDoc := close.leaf closeAround around.at
      let prefix := open.opening around close
      let bound: (inForce outer top <= indent) = True := openedBound seated below clear room
      let atOpener := openerLine (seated, below, clear, room)
      let pre := Entered indent column False state entry start
      let gap := HeldGap outer top flag low origin entry.indent
      let done := HeldDone indent around.at outer top flag inner.trails
      let post: Place → Hang → Prop := place hang =>
        Ended opened (close.trails || inner.trails) place ∧ hang = Hang.At opened
      let opening: HangLays kinds prefix indent pre gap :=
        heldOpening kinds open close around indent column state entry opener hoisted openTrailed trails
      let middle: HangLays kinds innerDoc indent gap done :=
        heldInner kinds innerDoc indent around.at entry outer top flag inner.trails bound atOpener innerHangs lowers
            keys
      let closing: HangLays kinds closerDoc indent done post :=
        heldCloser kinds close closeAround around.at indent outer top closer byComputing byComputing closeComments
            closeTrailed bound
      rewrite plain then
        (hangsConcat (hangsCons [innerDoc, closerDoc] opening (hangsTwo middle closing))) place _ trace next byComputing
            entered
            (hangsAfter after))

-- What the brackets may hold, after the waiting comment.

--| A token with no own-line comments, after a waiting comment: written first, so `HeldLowers` holds of it.
theorem atomLowers ∀ (kind: Tok) (word: Word) (around: Around) (indent low: Nat)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (hoisted: around.hoisted = False)
    (bare: word.comments.above = [])
    (single: around.item = False):
    HeldLowers ((Atom kind word).el around) indent low :=
  leafLowers word around around.at indent low solid closer comma
    (bareCloserLeading word around around.at hoisted bare single)
