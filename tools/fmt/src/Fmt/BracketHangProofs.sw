--| `printedHangs` for brackets (ticket 18f): a tuple's or list's items, each an element on a block of its own that the
--| comma after it ends, and the bracket from its opener to its closer.
--|
--| Inside a bracket the fold has the bracket's block innermost: no column while an item starts (`itemState`), the
--| item's first column if it started a line once it has (`itemDone`), back to none at the comma. An item starts
--| where a separator leaves it (`ItemSeat`) and ends where its element does (`ItemEnd`); a comma takes the fold back
--| to the next item's start (`ItemGap`).

namespace Fmt.BracketHangProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Expr, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.MarkProofs (..)
import Fmt.CalmProofs (bracketIs)

-- The fold inside a bracket.

--| Where a bracket's item may start: the bracket's block innermost with no column yet, `outer` outside it, the
--| type's or body's column `top`.
def itemState (outer: List (Option Nat)) (top: Option Nat): HangState :=
  { blocks = [None, ..outer], top, start = True, glue = False }

--| After an item: its block's column is where the item started a line, if it did.
def itemDone (outer: List (Option Nat)) (top block: Option Nat): HangState :=
  { blocks = [block, ..outer], top, start = False, glue = False }

--| A block column, if there is one, at `inset` or right of it.
def deepFrom (inset: Nat): Option Nat → Bool
  | None => True
  | Some column => inset <= column

--| Where an item may follow: after the opener or a comma, a comment waiting only if `trails`.
def ItemGap (outer: List (Option Nat)) (top: Option Nat) (trails: Bool): Place → Hang → Prop := place hang =>
  Ended (itemState outer top) trails place ∧ hang = Hang.At (itemState outer top)

--| Where an item starts, laid at `inset`: a seat there, after a waiting comment only if `before`, and no plain line
--| start (a separator leaves the printer mid-line, after a waiting comment or after a line break).
def ItemSeat (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (before: Bool): Place → Hang → Prop :=
  place hang =>
    hang = Hang.At (itemState outer top)
      ∧ plainStart place = False
      ∧ Seat inset inset before (itemState outer top) place (wordStart inset place)

--| Where an item ended: its block's column at `inset` or right of it, a comment waiting only if `trails`.
def ItemEnd (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (trails: Bool): Place → Hang → Prop :=
  place hang =>
    ∃ (block: Option Nat) => deepFrom inset block = True
      ∧ Ended (itemDone outer top block) trails place
      ∧ hang = Hang.At (itemDone outer top block)

theorem openedItem ∀ (outer: List (Option Nat)) (top start: Option Nat):
    openedBy (itemState outer top) start = itemDone outer top start :=
  match start with | None | Some _ => byComputing

--| An item seated at `inset` starts its line, if it does, at `inset` or right of it.
theorem seatDeep ∀ [inset: Nat] [before: Bool] [state: HangState] (place: Place)
    (seated: Seated inset before state place):
    deepFrom inset (wordStart inset place) = True :=
  match place, seated with
    | AtStart _ _ | Broken _ _, (atInset, _) => rewrite atInset then Nat.leRefl inset
    | Mid at carry, _ => byComputing
    | Held at carry, (_, floor, _) =>
      let landed: floored carry (Nat.max inset (at + 2)) = Nat.max inset (at + 2) := rewrite floor
      rewrite landed then arithmetic

--| An item seated at `inset` starts its line, if it does, at `inset` or right of it, its first token where
--| `startFor noted` says: on the line after comments above it (`noted`) or not.
theorem startDeep ∀ (noted: Bool) (inset: Nat) (before: Bool) (state: HangState) (place: Place)
    (seated: Seated inset before state place)
    (fresh: plainStart place = False):
    deepFrom inset (startFor noted inset place) = True :=
  match noted, place, seated, fresh with
    | False, place, seated, _ => seatDeep place seated
    | True, AtStart at carry, _, never => (Bool.trueNotFalse never).impossible
    | True, Broken at carry, (atInset, _), _ => rewrite atInset then Nat.leRefl inset
    | True, Mid _ _ | Held _ _, _, _ => arithmetic

--| An item's seat with room for its first word where `wordStart` says has room for it where `startFor` says: the two
--| agree at a line start and after a waiting comment, and mid-line the comment break is right of the line.
theorem seatFor ∀ (noted: Bool) (inset: Nat) (before: Bool) (outer: List (Option Nat)) (top: Option Nat) (place: Place)
    (seat: Seat inset inset before (itemState outer top) place (wordStart inset place))
    (fresh: plainStart place = False):
    Seat inset inset before (itemState outer top) place (startFor noted inset place) :=
  match noted, place, seat, fresh with
    | False, place, seat, _ => seat
    | True, AtStart at carry, _, never => (Bool.trueNotFalse never).impossible
    | True, Broken at carry, seat, _ => seat
    | True, Mid at carry, ((floor, left), column, clear, _), _ =>
      ((floor, left), column, clear, (byComputing, arithmetic))
    | True, Held at carry, ((waits, floor, left), column, clear, room), _ =>
      let landed: floored carry (Nat.max inset (at + 2)) = Nat.max inset (at + 2) := rewrite floor
      ((waits, floor, left), column, clear, rewrite landed at room then room)

--| What is in force outside an item's block is no further right than what is in force with it.
theorem outerBelow ∀ (inset at: Nat) (outer: List (Option Nat)) (top block: Option Nat)
    (deep: deepFrom inset block = True)
    (bound: (inForce outer top < inset) = True)
    (left: (inForce [block, ..outer] top <= at) = True):
    (inForce outer top <= at) = True :=
  match block, deep, left with
    | None, _, left => left
    | Some column, deep, left => arithmetic

-- Items.

--| What an item asks of its element: laid at `inset` from a seat there, at any entry but a plain line start, its
--| first word where `startFor noted` says for some `noted` (on the line after the comments or kept blank line it
--| writes above its first token, if it writes any), it ends after words as one token.
def ItemHangs (kinds: Text → Tok) (doc: Doc) (inset: Nat) (before trails: Bool): Prop :=
  ∃ (noted: Bool) => ∀ (state: HangState) (entry: Place) => plainStart entry = False
    → HangLays kinds doc inset (Entered inset inset before state entry (startFor noted inset entry)) (place hang =>
      Ended (openedBy state (startFor noted inset entry)) trails place
        ∧ hang = Hang.At (openedBy state (startFor noted inset entry)))

--| An item: from its seat, as its element hangs, to where it ended.
theorem itemHangs ∀ (kinds: Text → Tok) (doc: Doc) (inset: Nat) (outer: List (Option Nat))
    (top: Option Nat) (before trails: Bool)
    (el: ItemHangs kinds doc inset before trails):
    HangLays kinds doc inset (ItemSeat inset outer top before) (ItemEnd inset outer top trails) :=
  let (noted, lays) := el
  hangsBy (place trace next (folded, fresh, seat) after =>
    let (seated, _, _, _) := seat
    let start := startFor noted inset place
    (lays (itemState outer top) place fresh) place _ trace next byComputing
      (byComputing, folded, seatFor noted inset before outer top place seat fresh)
      (hangsAfter (left later (ended, done) =>
        after left later (
          start,
          startDeep noted inset before (itemState outer top) place seated fresh,
          rewrite openedItem outer top start at ended then ended,
          rewrite openedItem outer top start at done then done
        ))))

--| Right after a line break at `inset`, with no comment floor, an item may start.
theorem brokenItemSeat ∀ (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (before: Bool) (carry: Carry)
    (floor: carry.floor = None)
    (bound: (inForce outer top < inset) = True):
    ItemSeat inset outer top before
      (Broken (floored carry inset) (carry.breakTo inset))
      (Hang.At (itemState outer top)) :=
  let landed: floored carry inset = inset := rewrite floor
  rewrite landed then
    (byComputing, byComputing, ((byComputing, byComputing), Nat.leRefl inset, arithmetic, (byComputing, arithmetic)))

--| Mid-line where an item may follow, an item may start.
theorem midItemSeat ∀ (inset at: Nat) (outer: List (Option Nat)) (top: Option Nat) (before: Bool) (carry: Carry)
    (floor: carry.floor = None)
    (left: (inForce outer top <= at) = True)
    (bound: (inForce outer top < inset) = True):
    ItemSeat inset outer top before (Mid at carry) (Hang.At (itemState outer top)) :=
  (byComputing, byComputing, ((floor, left), Nat.leRefl inset, arithmetic, byComputing))

--| After a waiting comment, an item that may start there may start.
theorem heldItemSeat ∀ (inset at: Nat) (outer: List (Option Nat)) (top: Option Nat) (carry: Carry)
    (floor: carry.floor = None)
    (left: (inForce outer top <= at) = True)
    (bound: (inForce outer top < inset) = True):
    ItemSeat inset outer top True (Held at carry) (Hang.At (itemState outer top)) :=
  let landed: floored carry (Nat.max inset (at + 2)) = Nat.max inset (at + 2) := rewrite floor
  (
    byComputing,
    byComputing,
    ((byComputing, floor, left), Nat.leRefl inset, arithmetic, (byComputing, rewrite landed then arithmetic))
  )

--| A `Line` before an item: mid-line, on the waiting comment's line, or a line break at `inset`.
theorem lineSeats ∀ (kinds: Text → Tok) (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (trails: Bool)
    (bound: (inForce outer top < inset) = True):
    HangLays kinds Line inset (ItemGap outer top trails) (ItemSeat inset outer top trails) :=
  hangsLine kinds inset (ItemGap outer top trails) (ItemSeat inset outer top trails) (place trace (ended, folded) =>
    match place, ended with
      | Mid at carry, (floor, left) =>
        rewrite folded then
          (
            (midItemSeat inset at outer top trails { carry | floor = None } byComputing left bound),
            (brokenItemSeat inset outer top trails carry floor bound)
          )
      | Held at carry, (waits, floor, left) =>
        rewrite folded then
          (
            (rewrite waits then heldItemSeat inset at outer top carry floor left bound),
            (brokenItemSeat inset outer top trails carry floor bound)
          ))

--| A `SoftLine` before an item, likewise.
theorem softSeats ∀ (kinds: Text → Tok) (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (trails: Bool)
    (bound: (inForce outer top < inset) = True):
    HangLays kinds SoftLine inset (ItemGap outer top trails) (ItemSeat inset outer top trails) :=
  hangsSoft kinds inset (ItemGap outer top trails) (ItemSeat inset outer top trails) (place trace (ended, folded) =>
    match place, ended with
      | Mid at carry, (floor, left) =>
        rewrite folded then
          (
            (midItemSeat inset at outer top trails carry floor left bound),
            (brokenItemSeat inset outer top trails carry floor bound)
          )
      | Held at carry, (waits, floor, left) =>
        rewrite folded then
          (
            (rewrite waits then heldItemSeat inset at outer top carry floor left bound),
            (brokenItemSeat inset outer top trails carry floor bound)
          ))

--| The separator before a broken bracket's item: a `SoftLine` before the first, a `Line` before the others.
theorem sepSeats ∀ (kinds: Text → Tok) (first: Bool) (inset: Nat) (outer: List (Option Nat))
    (top: Option Nat) (trails: Bool)
    (bound: (inForce outer top < inset) = True):
    HangLays kinds
      (if first then SoftLine else Line)
      inset
      (ItemGap outer top trails)
      (ItemSeat inset outer top trails) :=
  match first with
    | True => softSeats kinds inset outer top trails bound
    | False => lineSeats kinds inset outer top trails bound

--| The comma after an item: the bracket's next item starts.
theorem commaHangs ∀ (kinds: Text → Tok) (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (trails: Bool)
    (comma: kinds "," = Comma)
    (bound: (inForce outer top < inset) = True):
    HangLays kinds (Closing ",") inset (ItemEnd inset outer top trails) (ItemGap outer top trails) :=
  hangsClosing kinds "," inset
    (ItemEnd inset outer top trails)
    (ItemGap outer top trails)
    byComputing
    byComputing
    (place trace (block, deep, ended, folded) =>
      let step := stepComma kinds (itemDone outer top block) block outer "," byComputing comma byComputing
      rewrite folded then
        match place, ended with
          | Mid at carry, (floor, left) =>
            rewrite step then ((byComputing, outerBelow inset at outer top block deep bound left), byComputing)
          | Held at carry, (waits, floor, left) =>
            rewrite step then ((waits, byComputing, outerBelow inset at outer top block deep bound left), byComputing)
          | AtStart at carry, never => (Bool.falseNotTrue never).impossible
          | Broken at carry, never => (Bool.falseNotTrue never).impossible)

--| Each item of a broken bracket hangs as an element laid at `inset` (`ItemHangs`), seated after the separator before
--| it: after a waiting comment only if the code before it, the opener or the item before, ends with one (`seat`).
def ItemsHang (kinds: Text → Tok) (inset: Nat) (bare arm before seat: Bool) (at: Nat): List Expr → Prop
  | [] => True
  | [item, ..rest] =>
    ItemHangs kinds (item.el (firstAround bare arm before at)) inset seat item.trails
      ∧ ItemsHang kinds inset False arm item.trails item.trails (at + item.size) rest

--| Whether the last item ends with a trailing comment: the opener if there is none.
def lastTrails (seat: Bool): List Expr → Bool
  | [] => seat
  | [item, ..rest] => lastTrails item.trails rest

--| A broken bracket's items (`brokenItems`), each after its separator, a comma after each but the last.
theorem brokenItemsHang ∀ (kinds: Text → Tok) (bare arm first before seat: Bool) (at inset: Nat)
    (outer: List (Option Nat)) (top: Option Nat) (item: Expr) (rest: List Expr)
    (comma: kinds "," = Comma)
    (bound: (inForce outer top < inset) = True)
    (each: ItemsHang kinds inset bare arm before seat at [item, ..rest]):
    HangLaysAll kinds
      (brokenItems bare arm first before at [item, ..rest])
      inset
      (ItemGap outer top seat)
      (ItemEnd inset outer top (lastTrails seat [item, ..rest])) :=
  let doc := item.el (firstAround bare arm before at)
  match rest, each with
    | [], (el, _) =>
      hangsTwo
        (sepSeats kinds first inset outer top seat bound)
        (itemHangs kinds doc inset outer top seat item.trails el)
    | [next, ..more], (el, others) =>
      hangsCons
        [doc, Closing ",", ..brokenItems False arm False item.trails (at + item.size) [next, ..more]]
        (sepSeats kinds first inset outer top seat bound)
        (hangsCons
          [Closing ",", ..brokenItems False arm False item.trails (at + item.size) [next, ..more]]
          (itemHangs kinds doc inset outer top seat item.trails el)
          (hangsCons
            (brokenItems False arm False item.trails (at + item.size) [next, ..more])
            (commaHangs kinds inset outer top item.trails comma bound)
            (brokenItemsHang kinds False arm False item.trails item.trails
              (at + item.size)
              inset
              outer
              top
              next
              more
              comma
              bound
              others)))

-- A filled list's cells.

--| Where an item may follow, it may start: mid-line, or after the comment waiting there.
theorem gapSeat ∀ (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (trails: Bool) (place: Place) (hang: Hang)
    (bound: (inForce outer top < inset) = True)
    (gap: ItemGap outer top trails place hang):
    ItemSeat inset outer top trails place hang :=
  match place, gap with
    | Mid at carry, ((floor, left), folded) =>
      rewrite folded then midItemSeat inset at outer top trails carry floor left bound
    | Held at carry, ((waits, floor, left), folded) =>
      rewrite folded, waits then heldItemSeat inset at outer top carry floor left bound
    | AtStart _ _ | Broken _ _, (never, _) => (Bool.falseNotTrue never).impossible

--| A filled list's cell with its comma: the item, then the comma, after which the next item starts.
theorem cellCommaHangs ∀ (kinds: Text → Tok) (doc: Doc) (inset: Nat) (outer: List (Option Nat))
    (top: Option Nat) (seat trails: Bool)
    (comma: kinds "," = Comma)
    (bound: (inForce outer top < inset) = True)
    (el: ItemHangs kinds doc inset seat trails):
    HangLays kinds (Doc.concat [doc, Closing ","]) inset (ItemSeat inset outer top seat) (ItemGap outer top trails) :=
  hangsConcat
    (hangsTwo
      (itemHangs kinds doc inset outer top seat trails el)
      (commaHangs kinds inset outer top trails comma bound))

--| The cells after a filled list's first, each after a fill's separator.
theorem sepsCellsHang ∀ (kinds: Text → Tok) (arm seat: Bool) (at inset: Nat) (outer: List (Option Nat))
    (top: Option Nat) (item: Expr) (rest: List Expr)
    (comma: kinds "," = Comma)
    (bound: (inForce outer top < inset) = True)
    (each: ItemsHang kinds inset False arm seat seat at [item, ..rest])
    (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (holds: ItemGap outer top seat place (hangOf kinds trace))
    (after: ∀ (left: Place) (later: List Event) => ItemEnd inset outer top
      (lastTrails seat [item, ..rest])
      left
      (hangOf kinds later)
      → next left later):
    SepsLay (cells False arm seat at [item, ..rest]) inset place trace next :=
  let doc := item.el (firstAround False arm seat at)
  let seated := lineSeats kinds inset outer top seat bound
  match rest, each with
    | [], (el, _) =>
      seated place _ trace
        (middle between => Lays doc inset middle between (left later => SepsLay [] inset left later next))
        byComputing
        holds
        (hangsAfter (middle between ready =>
          itemHangs kinds doc inset outer top seat item.trails el middle _ between next byComputing ready
            (hangsAfter after)))
    | [following, ..more], (el, others) =>
      seated place _ trace
        (middle between =>
          Lays (Doc.concat [doc, Closing ","]) inset middle between (left later =>
            SepsLay (cells False arm item.trails (at + item.size) [following, ..more]) inset left later next))
        byComputing
        holds
        (hangsAfter (middle between ready =>
          cellCommaHangs kinds doc inset outer top seat item.trails comma bound el middle _ between
            (left later =>
              SepsLay (cells False arm item.trails (at + item.size) [following, ..more]) inset left later next)
            byComputing
            ready
            (hangsAfter (left later gap =>
              sepsCellsHang kinds arm item.trails
                (at + item.size)
                inset
                outer
                top
                following
                more
                comma
                bound
                others
                left
                later
                next
                gap
                after))))

--| A filled list's cells (`cells`) in their `Fill`: the first where the opener left off, each later one after a
--| separator, a comma after each but the last.
theorem fillCellsHang ∀ (kinds: Text → Tok) (bare arm before seat: Bool) (at inset: Nat) (outer: List (Option Nat))
    (top: Option Nat) (item: Expr) (rest: List Expr)
    (comma: kinds "," = Comma)
    (bound: (inForce outer top < inset) = True)
    (each: ItemsHang kinds inset bare arm before seat at [item, ..rest]):
    HangLays kinds
      (Fill (cells bare arm before at [item, ..rest]))
      inset
      (ItemGap outer top seat)
      (ItemEnd inset outer top (lastTrails seat [item, ..rest])) :=
  hangsBy (place trace next holds after =>
    let doc := item.el (firstAround bare arm before at)
    let ready := gapSeat inset outer top seat place (hangOf kinds trace) bound holds
    match rest, each with
      | [], (el, _) =>
        itemHangs kinds doc inset outer top seat item.trails el place _ trace
          (left later => SepsLay [] inset left later next)
          byComputing
          ready
          (hangsAfter after)
      | [following, ..more], (el, others) =>
        cellCommaHangs kinds doc inset outer top seat item.trails comma bound el place _ trace
          (left later =>
            SepsLay (cells False arm item.trails (at + item.size) [following, ..more]) inset left later next)
          byComputing
          ready
          (hangsAfter (left later gap =>
            sepsCellsHang kinds arm item.trails
              (at + item.size)
              inset
              outer
              top
              following
              more
              comma
              bound
              others
              left
              later
              next
              gap
              after)))

-- Marks through a bracket.

--| What holds of a document's places holds with the marks below `low` that were open at `origin` still kept, when
--| its keys are at least `low` (`framed`).
theorem hangsKept ∀ [kinds: Text → Tok] [doc: Doc] [indent: Nat] (low: Nat)
    (origin: Carry) [pre post: Place → Hang → Prop]
    (keys: keysFrom low doc = True)
    (lays: HangLays kinds doc indent pre post):
    HangLays kinds doc indent (place hang => pre place hang ∧ MarksKept low origin place.carry) (place hang =>
      post place hang ∧ MarksKept low origin place.carry) :=
  hangsBy (place trace next (holds, kept) after =>
    framed low origin indent place trace next keys kept
      (lays place _ trace
        (left later => MarksKept low origin left.carry → next left later)
        byComputing
        holds
        (hangsAfter (left later reached held => after left later (reached, held)))))

theorem allHangsKept ∀ [kinds: Text → Tok] [docs: List Doc] [indent: Nat] (low: Nat)
    (origin: Carry) [pre post: Place → Hang → Prop]
    (keys: allKeysFrom low docs = True)
    (lays: HangLaysAll kinds docs indent pre post):
    HangLaysAll kinds docs indent (place hang => pre place hang ∧ MarksKept low origin place.carry) (place hang =>
      post place hang ∧ MarksKept low origin place.carry) :=
  allHangsBy (place trace next (holds, kept) after =>
    allFramed low origin indent place trace next keys kept
      (lays place _ trace
        (left later => MarksKept low origin left.carry → next left later)
        byComputing
        holds
        (hangsAfter (left later reached held => after left later (reached, held)))))

--| Where a bracket's closer may take a line of its own (`flag`), the marks kept.
def Marked (flag: Bool) (low: Nat) (origin carry: Carry): Prop := flag = True → MarksKept low origin carry

theorem hangsMarked ∀ [kinds: Text → Tok] [doc: Doc] [indent low: Nat] (origin: Carry)
    (flag: Bool) [pre post: Place → Hang → Prop]
    (keys: keysFrom low doc = True)
    (lays: HangLays kinds doc indent pre post):
    HangLays kinds doc indent (place hang => pre place hang ∧ Marked flag low origin place.carry) (place hang =>
      post place hang ∧ Marked flag low origin place.carry) :=
  match flag with
    | True =>
      hangsPost
        (hangsPre (hangsKept low origin keys lays) (place hang (holds, kept) => (holds, kept byComputing)))
        (place hang (reached, kept) => (reached, _ => kept))
    | False => hangsPost (hangsPre lays (place hang (holds, _) => holds)) (place hang reached =>
      (reached, never => (Bool.falseNotTrue never).impossible))

--| The carry right after an opener's `Mark` at `entry`.
def markedCarry (key: Nat) (entry: Place): Carry := entry.carry.mark key entry.indent

theorem markedFound ∀ (key: Nat) (entry: Place):
    (markedCarry key entry).marks.find (found => found.key == key)
      = Some { key, marked = entry.indent, least = None } :=
  rewrite Nat.equalRefl key

theorem trailingKeys ∀ (low: Nat) (word: Word): allKeysFrom low word.trailing = True :=
  match after: word.comments.after with | Some _ | None => byComputing

--| An opener whose closer may take a line of its own: its mark, then the bracket and its trailing comment, the mark
--| still open after them.
theorem markedOpeningHangs ∀ (kinds: Text → Tok) (word closer: Word) (around: Around) (indent column: Nat)
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
        (Ended (openingBy state (wordStart indent entry)) word.trails place
          ∧ hang = Hang.At (openingBy state (wordStart indent entry)))
          ∧ MarksKept (around.at + 1) (markedCarry around.at entry) place.carry) :=
  let (_, _, _, _, _, _, _, _, notCloser, notComma) := token
  let start := wordStart indent entry
  let opened := openingBy state start
  let origin := markedCarry around.at entry
  let low := around.at + 1
  let ready: Place → Hang → Prop := place hang =>
    hang = Hang.At state
      ∧ Seated column False state place
      ∧ Room state (wordStart indent place)
      ∧ wordStart indent place = start
  let written: Place → Hang → Prop := place hang => Ended opened False place ∧ hang = Hang.At opened
  let post: Place → Hang → Prop := place hang => Ended opened word.trails place ∧ hang = Hang.At opened
  let rest: HangLaysAll kinds [Doc.text word.text, ..word.trailing] indent ready post :=
    hangsCons word.trailing
      (openerStep kinds word.text indent column state start token)
      (trailingHangs kinds indent opened trailed)
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
              (folded, stays, rewrite same, isEntry then room, rewrite same, isEntry),
              rewrite Doc.Proofs.withCarryCarry place (place.carry.mark around.at place.indent), isEntry then
                keptRefl low origin
            )))
        kept)

-- The closer.

--| The fold at a bracket's closer: its block innermost, at `block`, `outer` outside it.
def bracketState (outer: List (Option Nat)) (top block: Option Nat) (start: Bool): HangState :=
  { blocks = [block, ..outer], top, start, glue = False }

--| Where a bracket's closer may be written: its block innermost, at `inset` or right of it, and a seat for it.
def CloserSits (inset indent: Nat) (outer: List (Option Nat)) (top: Option Nat) (close: Word) (closeAround: Around):
    Place → Hang → Prop :=
  place hang =>
    ∃ (block: Option Nat) => ∃ (start: Bool) => deepFrom inset block = True
      ∧ hang = Hang.At (bracketState outer top block start)
      ∧ CloserSeat indent closeAround.before (close.lone closeAround) (bracketState outer top block start) place

--| As `CloserSits`, and a closer that may take a line of its own has its opener's mark: found by the bracket's key,
--| on the opener's line.
def CloserReady (inset indent key: Nat) (entry: Place) (outer: List (Option Nat)) (top: Option Nat)
    (close: Word) (closeAround: Around):
    Place → Hang → Prop :=
  place hang =>
    CloserSits inset indent outer top close closeAround place hang
      ∧ Marked (close.noted || close.trails) (key + 1) (markedCarry key entry) place.carry

theorem leftOfLower ∀ (low high: Nat) (block: Option Nat)
    (le: (low <= high) = True)
    (left: leftOf high block = True):
    leftOf low block = True :=
  match block, left with
    | None, _ => byComputing
    | Some column, left => arithmetic

--| Where a closer's line of its own lands, given its opener's mark: left of the bracket's block, not left of what is
--| in force outside it, which is no further right than the opener's line.
theorem closerFitsOf ∀ (key indent: Nat) (block: Option Nat) (outside marked: Nat) (carry: Carry) (mark: OpenMark)
    (found: carry.marks.find (found => found.key == key) = Some mark)
    (line: mark.marked = marked)
    (atOpener: (outside <= marked) = True)
    (clear: (outside <= indent) = True)
    (shallow: leftOf indent block = True):
    CloserFits key indent block outside carry :=
  let fromMark: (outside <= carry.closerAt key indent) = True :=
    rewrite found then
      match mark, line with
        | { key = markKey, marked = markLine, least = None }, _ => clear
        | { key = markKey, marked = markLine, least = Some least }, line =>
          match low: least <= indent with
            | True => rewrite line then arithmetic
            | False => clear
  (leftOfLower (carry.closerAt key indent) indent block (closerAtMost carry key indent) shallow, fromMark)

--| A closer that takes a line of its own has a mark: it has own-line comments, or a trailing comment.
theorem loneMarks ∀ (word: Word) (around: Around)
    (line: (word.noted || word.lone around) = True):
    (word.noted || word.trails) = True :=
  match noted: word.noted, line with
    | True, _ => byComputing
    | False, line =>
      match trails: word.trails, line with
        | True, _ => byComputing
        | False, line =>
          match before: around.before, line with
            | True, never => (Bool.falseNotTrue never).impossible

--| The bracket's closer, from where it is ready: its block gone, the fold as after its opener alone.
--|
--| Proof idea: `closerLeafHangs`, with the fold facts from the block's depth, and `CloserFits`, where the closer may
--| take a line of its own, from the opener's mark (`closerFitsOf`): the marks kept since give it, found by the
--| bracket's key on the opener's line.
theorem closerStep ∀ (kinds: Text → Tok) (close: Word) (closeAround: Around) (key indent inset: Nat) (entry: Place)
    (outer: List (Option Nat)) (top: Option Nat)
    (token: CloserToken kinds close.text)
    (hoisted: closeAround.hoisted = False)
    (single: closeAround.item = False)
    (comments: NotesComment close.comments.above)
    (trailed: TrailsComment close)
    (deeper: (indent < inset) = True)
    (bound: (inForce outer top <= indent) = True)
    (atOpener: (inForce outer top <= entry.indent) = True):
    HangLays kinds
      (close.leaf closeAround key)
      indent
      (CloserReady inset indent key entry outer top close closeAround)
      (place hang =>
        Ended { blocks = outer, top, start = False, glue = False } (close.trails || closeAround.before) place
          ∧ hang = Hang.At { blocks = outer, top, start = False, glue = False }) :=
  hangsBy (place trace next ((block, start, deep, folded, seat), marked) after =>
    let state := bracketState outer top block start
    let nested: (inForce outer top <= inForce [block, ..outer] top) = True := match block, deep with
      | None, _ => Nat.leRefl (inForce outer top)
      | Some column, deep => arithmetic
    let shallow: leftOf indent block = True := match block, deep with
      | None, _ => byComputing
      | Some column, deep => arithmetic
    let fold: CloserFold indent state block outer := (byComputing, byComputing, nested, bound)
    let fits: (close.noted || close.lone closeAround) = True
      → CloserFits key indent block (inForce outer top) place.carry :=
      line =>
        let was: MarkBelow (place.carry.marks.find (found => found.key == key)) {
          key,
          marked = entry.indent,
          least = None
        } :=
          marked
            (loneMarks close closeAround line)
            key
            { key, marked = entry.indent, least = None }
            arithmetic
            (markedFound key entry)
        match found: place.carry.marks.find (found => found.key == key) with
          | Some mark =>
            let (same, _) := was
            closerFitsOf key indent block
              (inForce outer top)
              entry.indent
              place.carry
              mark
              found
              same
              atOpener
              bound
              shallow
    closerLeafHangs kinds close closeAround key indent state block outer token fold hoisted single comments trailed
        place _ trace next byComputing
        (folded, seat, fits)
        (hangsAfter after))

theorem allHangsMarked ∀ [kinds: Text → Tok] [docs: List Doc] [indent: Nat] (low: Nat) (origin: Carry)
    (flag: Bool) [pre post: Place → Hang → Prop]
    (keys: allKeysFrom low docs = True)
    (lays: HangLaysAll kinds docs indent pre post):
    HangLaysAll kinds docs indent (place hang => pre place hang ∧ Marked flag low origin place.carry) (place hang =>
      post place hang ∧ Marked flag low origin place.carry) :=
  match flag with
    | True =>
      allHangsPost
        (allHangsPre (allHangsKept low origin keys lays) (place hang (holds, kept) => (holds, kept byComputing)))
        (place hang (reached, kept) => (reached, _ => kept))
    | False => allHangsPost (allHangsPre lays (place hang (holds, _) => holds)) (place hang reached =>
      (reached, never => (Bool.falseNotTrue never).impossible))

-- The bracket.

--| The opener: where the bracket's first item may follow, the opener's mark kept where the closer may need it.
theorem bracketOpening ∀ (kinds: Text → Tok) (open close: Word) (around: Around) (indent column: Nat)
    (state: HangState) (entry: Place)
    (token: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (trailed: TrailsComment open):
    HangLays kinds
      (open.opening around close)
      indent
      (Entered indent column False state entry (wordStart indent entry))
      (place hang =>
        ItemGap
          (openedBy state (wordStart indent entry)).blocks
          (openedBy state (wordStart indent entry)).top
          open.trails
          place
          hang
          ∧ Marked (close.noted || close.trails) (around.at + 1) (markedCarry around.at entry) place.carry) :=
  let start := wordStart indent entry
  let pre := Entered indent column False state entry start
  let opened := openingBy state start
  let goal: Prop := HangLays kinds (open.opening around close) indent pre (place hang =>
    ItemGap (openedBy state start).blocks (openedBy state start).top open.trails place hang
      ∧ Marked (close.noted || close.trails) (around.at + 1) (markedCarry around.at entry) place.carry)
  Bool.inspect
    (close.noted || close.trails)
    (_ => goal)
    (marks =>
      hangsPost
        (markedOpeningHangs kinds open close around indent column state entry token hoisted trailed marks)
        (place hang (gap, kept) => (gap, _ => kept)))
    (marks =>
      hangsPost (openingHangs close indent column state entry token hoisted trailed) (place hang gap =>
        (gap, never => (Bool.falseNotTrue (Eq.trans marks.flipped never)).impossible)))

--| Where an item or the opener ended, the closer may sit, a comment waiting only if the code before it ends with
--| one.
theorem endedSits ∀ (inset indent: Nat) [outer: List (Option Nat)] [top block: Option Nat] [start: Bool] (trails: Bool)
    (close: Word) [closeAround: Around] [place: Place] [hang: Hang]
    (beforeOf: trails = True → closeAround.before = True)
    (deep: deepFrom inset block = True)
    (ended: Ended (bracketState outer top block start) trails place)
    (folded: hang = Hang.At (bracketState outer top block start)):
    CloserSits inset indent outer top close closeAround place hang :=
  match place, ended with
    | Mid at carry, (floor, left) => (block, start, deep, folded, (floor, left))
    | Held at carry, (waits, floor, left) => (block, start, deep, folded, (beforeOf waits, floor, left))

--| The `SoftLine` before a broken bracket's closer: the closer sits where the last item ended, or at the start of the
--| line after it at the bracket's indentation.
theorem softSits ∀ (kinds: Text → Tok) (inset indent: Nat) (outer: List (Option Nat)) (top: Option Nat) (trails: Bool)
    (close: Word) (closeAround: Around)
    (deeper: (indent < inset) = True)
    (beforeOf: trails = True → closeAround.before = True):
    HangLays kinds SoftLine indent
      (ItemEnd inset outer top trails)
      (CloserSits inset indent outer top close closeAround) :=
  hangsSoft kinds indent
    (ItemEnd inset outer top trails)
    (CloserSits inset indent outer top close closeAround)
    (place trace (block, deep, ended, folded) =>
      let shallow: leftOf indent block = True := match block, deep with
        | None, _ => byComputing
        | Some column, deep => arithmetic
      match place, ended with
        | Mid at carry, (floor, left) =>
          let landed: floored carry indent = indent := rewrite floor
          ((block, False, deep, folded, (floor, left)), (block, False, deep, folded, Inr (landed, floor, shallow)))
        | Held at carry, (waits, floor, left) =>
          let landed: floored carry indent = indent := rewrite floor
          (
            (block, False, deep, folded, (beforeOf waits, floor, left)),
            (block, False, deep, folded, Inr (landed, floor, shallow))
          ))

--| What is in force after an element's first word, no comment waiting, is no further right than the line it is on:
--| the line's column, which a `Mark` there records.
theorem openerLine ∀ [indent column: Nat] [state: HangState] [entry: Place]
    (seat: Seat indent column False state entry (wordStart indent entry)):
    (inForce (openedBy state (wordStart indent entry)).blocks (openedBy state (wordStart indent entry)).top
      <= entry.indent)
      = True :=
  match entry, seat with
    | AtStart at _ | Broken at _, (_, _, _, (_, _)) => openedSome at arithmetic
    | Mid at carry, ((_, left), _, _, _) => rewrite openedNone state then left
    | Held at carry, ((never, _, _), _, _, _) => (Bool.falseNotTrue never).impossible

--| A tuple's or list's parts (`bracketContent`) as one element: the fold after it as after its opener alone.
--|
--| Proof idea: `bracketIs` names the three layouts. The opener leaves the fold with the bracket's block open
--| (`bracketOpening`); the items keep it (`fillCellsHang`, `brokenItemsHang`), and the closer closes it
--| (`closerStep`), from where the opener or the last item ended, or the line break before it (`softSits`). Its
--| `CloserFits` comes from the opener's mark, which the items keep, their keys being past the opener's
--| (`hangsMarked`).
theorem bracketContentHangs ∀ (kinds: Text → Tok) (list: Bool) (open: Word) (items: List Expr) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (comma: kinds "," = Comma)
    (each: ItemsHang kinds
      (indent + 2)
      (list && items.all Expr.plainItem)
      around.inArm
      open.trails
      open.trails
      (around.at + 1)
      items)
    (filledKeys: allKeysFrom
      (around.at + 1)
      (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
      = True)
    (brokenKeys: allKeysFrom
      (around.at + 1)
      (brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items)
      = True)
    (closeBefore: lastTrails open.trails items = True → (ListOf open items False close).trailsBeforeClose = True):
    ElHangs kinds
      (bracketContent list open items close around)
      indent
      column
      False
      (close.trails || (ListOf open items False close).trailsBeforeClose)
      wordStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      let (_, _, (seated, below, clear, room)) := entered
      let start := wordStart indent entry
      let opened := openedBy state start
      let outer := opened.blocks
      let top := opened.top
      let inset := indent + 2
      let low := around.at + 1
      let origin := markedCarry around.at entry
      let flag := close.noted || close.trails
      let whole := ListOf open items False close
      let closeAround := around.next whole.trailsBeforeClose (whole.size - 1)
      let closerDoc := close.leaf closeAround around.at
      let prefix := open.opening around close
      let bare := list && items.all Expr.plainItem
      let trails := close.trails || whole.trailsBeforeClose
      let bound: (inForce outer top <= indent) = True := openedBound seated below clear room
      let inner: (inForce outer top < inset) = True := arithmetic
      let atOpener := openerLine (seated, below, clear, room)
      let pre := Entered indent column False state entry start
      let openDone: Place → Hang → Prop := place hang =>
        ItemGap outer top open.trails place hang ∧ Marked flag low origin place.carry
      let contentsDone: Place → Hang → Prop := place hang =>
        ItemEnd inset outer top (lastTrails open.trails items) place hang ∧ Marked flag low origin place.carry
      let ready := CloserReady inset indent around.at entry outer top close closeAround
      let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = Hang.At opened
      let opening: HangLays kinds prefix indent pre openDone :=
        bracketOpening kinds open close around indent column state entry opener hoisted openTrailed
      let closing: HangLays kinds closerDoc indent ready post :=
        closerStep kinds close closeAround around.at indent inset entry outer top closer byComputing byComputing
            closeComments closeTrailed arithmetic bound atOpener
      let endReady: ∀ (place: Place) (hang: Hang) => contentsDone place hang → ready place hang := place hang (
        (block, deep, ended, folded),
        marked
      ) =>
        (endedSits inset indent (lastTrails open.trails items) close closeBefore deep ended folded, marked)
      let soft: HangLays kinds SoftLine indent contentsDone ready :=
        hangsMarked origin flag byComputing
          (softSits kinds inset indent outer top
            (lastTrails open.trails items)
            close
            closeAround
            arithmetic
            closeBefore)
      rewrite bracketIs list open items close around then
        match items, each, filledKeys, brokenKeys, closeBefore with
          | [], _, _, _, closeBefore =>
            let gapReady: ∀ (place: Place) (hang: Hang) => openDone place hang → ready place hang := place hang (
              (ended, folded),
              marked
            ) =>
              (endedSits inset indent open.trails close closeBefore byComputing ended folded, marked)
            (hangsConcat (hangsTwo opening (hangsPre closing gapReady))) place _ trace next byComputing entered
              (hangsAfter after)
          | [item, ..rest], each, filledKeys, brokenKeys, closeBefore =>
            let cellDocs := cells bare around.inArm open.trails low [item, ..rest]
            let brokenDocs := brokenItems bare around.inArm True open.trails low [item, ..rest]
            let filled: HangLays kinds (Nest 2 (Fill cellDocs)) indent openDone contentsDone :=
              hangsNest
                (hangsMarked origin flag filledKeys
                  (fillCellsHang kinds bare around.inArm open.trails open.trails low inset outer top item rest comma
                      inner each))
            let broken: HangLays kinds (Nest 2 (Doc.concat brokenDocs)) indent openDone contentsDone :=
              hangsNest
                (hangsConcat
                  (allHangsMarked low origin flag brokenKeys
                    (brokenItemsHang kinds bare around.inArm True open.trails open.trails low inset outer top item rest
                        comma inner each)))
            match fill: list
              && !(ListOf open [item, ..rest] False close).holdsTrailingComment
              && [item, ..rest].all Expr.plainItem with
              | True =>
                (hangsConcat
                      (hangsCons
                        [Nest 2 (Fill cellDocs), closerDoc]
                        opening
                        (hangsTwo filled (hangsPre closing endReady)))) place _ trace next byComputing entered
                    (hangsAfter after)
              | False =>
                let tail: HangLaysAll kinds [Nest 2 (Doc.concat brokenDocs), SoftLine] indent openDone ready :=
                  hangsTwo broken soft
                match holds: (ListOf open [item, ..rest] False close).holdsTrailingComment with
                  | True =>
                    (hangsConcat
                          (hangsCons
                            [Nest 2 (Doc.concat brokenDocs), SoftLine, closerDoc, BreakParent]
                            opening
                            (hangsAppend tail (hangsTwo closing (hangsBreakParent kinds indent post))))) place _ trace
                        next byComputing entered
                        (hangsAfter after)
                  | False =>
                    (hangsConcat
                          (hangsCons
                            [Nest 2 (Doc.concat brokenDocs), SoftLine, closerDoc]
                            opening
                            (hangsAppend tail (hangsLast closing)))) place _ trace next byComputing entered
                        (hangsAfter after))

--| A tuple or list (`commaBracket`) as one element.
theorem commaBracketHangs ∀ (kinds: Text → Tok) (list: Bool) (open: Word) (items: List Expr) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (comma: kinds "," = Comma)
    (each: ItemsHang kinds
      (indent + 2)
      (list && items.all Expr.plainItem)
      around.inArm
      open.trails
      open.trails
      (around.at + 1)
      items)
    (filledKeys: allKeysFrom
      (around.at + 1)
      (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
      = True)
    (brokenKeys: allKeysFrom
      (around.at + 1)
      (brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items)
      = True)
    (closeBefore: lastTrails open.trails items = True → (ListOf open items False close).trailsBeforeClose = True):
    ElHangs kinds
      (commaBracket list open items close around)
      indent
      column
      False
      (close.trails || (ListOf open items False close).trailsBeforeClose)
      wordStart :=
  state entry =>
    hangsGroup
      (bracketContent list open items close around).forcesBreak
      (bracketContentHangs kinds list open items close around indent column opener hoisted openTrailed closer
          closeComments closeTrailed comma each filledKeys brokenKeys closeBefore state entry)

--| A bracket's trailing comment: on its closer, or, the closer being one, on what comes before it.
theorem bracketTrails ∀ (open: Word) (items: List Expr) (list: Bool) (close: Word)
    (closer: isCloserText close.text = True):
    (ListOf open items list close).trails = (close.trails || (ListOf open items False close).trailsBeforeClose) :=
  rewrite List.reverseSnoc [open, ..itemsWords items] close, closer

theorem tupleTrails ∀ (open: Word) (items: List Expr) (list: Bool) (close: Word)
    (closer: isCloserText close.text = True):
    (Tuple open items list close).trails = (close.trails || (ListOf open items False close).trailsBeforeClose) :=
  rewrite List.reverseSnoc [open, ..itemsWords items] close, closer

--| A list's items each hang, wherever the list is: from its indentation, `inset` further in.
def ItemsHangFrom (kinds: Text → Tok) (list: Bool) (open: Word) (items: List Expr) (around: Around): Prop :=
  ∀ (indent: Nat) => ItemsHang kinds
    (indent + 2)
    (list && items.all Expr.plainItem)
    around.inArm
    open.trails
    open.trails
    (around.at + 1)
    items

--| A list (`[ … ]`) as an element, its trailing comment as `bracketTrails` reads it.
theorem listHangs ∀ (kinds: Text → Tok) (open: Word) (items: List Expr) (trailing: Bool) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (comma: kinds "," = Comma)
    (bare: open.leading around around.at = [])
    (each: ItemsHangFrom kinds True open items around)
    (filledKeys: allKeysFrom
      (around.at + 1)
      (cells (items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
      = True)
    (brokenKeys: allKeysFrom
      (around.at + 1)
      (brokenItems (items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items)
      = True)
    (closeBefore: lastTrails open.trails items = True → (ListOf open items False close).trailsBeforeClose = True):
    ElHangs kinds
      (Expr.el (ListOf open items trailing close) around)
      indent
      column
      around.before
      (close.trails || (ListOf open items False close).trailsBeforeClose)
      wordStart :=
  let inside := { around | hoisted = True }
  framedHangs open
    (commaBracket True open items close inside)
    indent
    column
    (close.trails || (ListOf open items False close).trailsBeforeClose)
    bare
    (inset seat =>
      commaBracketHangs kinds True open items close inside inset seat opener byComputing openTrailed closer
          closeComments closeTrailed comma
          (each inset)
          filledKeys
          brokenKeys
          closeBefore)

--| A tuple (`( … , … )`) as an element, its trailing comment as `tupleTrails` reads it.
theorem tupleHangs ∀ (kinds: Text → Tok) (open: Word) (items: List Expr) (trailing: Bool) (close: Word)
    (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (comma: kinds "," = Comma)
    (bare: open.leading around around.at = [])
    (each: ItemsHangFrom kinds False open items around)
    (filledKeys: allKeysFrom (around.at + 1) (cells False around.inArm open.trails (around.at + 1) items) = True)
    (brokenKeys: allKeysFrom (around.at + 1) (brokenItems False around.inArm True open.trails (around.at + 1) items)
      = True)
    (closeBefore: lastTrails open.trails items = True → (ListOf open items False close).trailsBeforeClose = True):
    ElHangs kinds
      (Expr.el (Tuple open items trailing close) around)
      indent
      column
      around.before
      (close.trails || (ListOf open items False close).trailsBeforeClose)
      wordStart :=
  let inside := { around | hoisted = True }
  framedHangs open
    (commaBracket False open items close inside)
    indent
    column
    (close.trails || (ListOf open items False close).trailsBeforeClose)
    bare
    (inset seat =>
      commaBracketHangs kinds False open items close inside inset seat opener byComputing openTrailed closer
          closeComments closeTrailed comma
          (each inset)
          filledKeys
          brokenKeys
          closeBefore)

-- Parentheses.

--| What a bracket holds, written right after an opener that ends no line with a comment: it starts mid-line, so it
--| starts no line of the bracket's, and the fold after it is as after the opener, the bracket's block still empty.
theorem heldInnerHangs ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (outer: List (Option Nat))
    (top: Option Nat) (opened trails: Bool)
    (quiet: opened = False)
    (clear: (inForce outer top <= indent) = True)
    (el: ElHangs kinds doc indent indent False trails wordStart):
    HangLays kinds doc indent (ItemGap outer top opened) (place hang =>
      Ended (bracketState outer top None False) trails place ∧ hang = Hang.At (bracketState outer top None False)) :=
  hangsBy (place trace next (ended, folded) after =>
    match place, ended with
      | Mid at carry, ended =>
        (el (itemState outer top) (Mid at carry))
          (Mid at carry) _
          trace
          next
          byComputing
          (byComputing, folded, endedSeat indent False (itemState outer top) (Mid at carry) byComputing ended clear)
          (hangsAfter (left later (done, landed) => after left later (done, landed)))
      | Held at carry, (waits, _, _) => (Bool.falseNotTrue (Eq.trans quiet.flipped waits)).impossible)

--| A `paren` holding anything `parenInner` writes as it is (all but a block or an `if`), its opener ending no line with a comment, as one element.
--|
--| Proof idea: as `bracketContentHangs` with one item and no commas. What the brackets hold starts mid-line after
--| the opener (`heldInnerHangs`), so the bracket's block stays empty and the closer fits wherever its line of its
--| own lands, right of what is in force outside the bracket: the opener's mark, which the inner element's keys
--| leave kept (`hangsMarked`), gives that (`closerStep`).
theorem parenHangs ∀ (kinds: Text → Tok) (open: Word) (inner: Expr) (close: Word) (around: Around) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (hoisted: around.hoisted = True)
    (openTrailed: TrailsComment open)
    (quiet: open.trails = False)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (plain: parenInner inner (around.next open.trails 1) = inner.el (around.next open.trails 1))
    (innerHangs: ElHangs kinds (inner.el (around.next open.trails 1)) indent indent False inner.trails wordStart)
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
      let openDone: Place → Hang → Prop := place hang =>
        ItemGap outer top open.trails place hang ∧ Marked flag low origin place.carry
      let innerDone: Place → Hang → Prop := place hang =>
        (Ended (bracketState outer top None False) inner.trails place
          ∧ hang = Hang.At (bracketState outer top None False))
          ∧ Marked flag low origin place.carry
      let ready := CloserReady (indent + 1) indent around.at entry outer top close closeAround
      let post: Place → Hang → Prop := place hang =>
        Ended opened (close.trails || inner.trails) place ∧ hang = Hang.At opened
      let opening: HangLays kinds prefix indent pre openDone :=
        bracketOpening kinds open close around indent column state entry opener hoisted openTrailed
      let middle: HangLays kinds innerDoc indent openDone innerDone :=
        hangsMarked origin flag keys
          (heldInnerHangs kinds innerDoc indent outer top open.trails inner.trails quiet bound innerHangs)
      let closing: HangLays kinds closerDoc indent ready post :=
        closerStep kinds close closeAround around.at indent
          (indent + 1)
          entry
          outer
          top
          closer
          byComputing
          byComputing
          closeComments
          closeTrailed
          arithmetic
          bound
          atOpener
      let innerReady: ∀ (place: Place) (hang: Hang) => innerDone place hang → ready place hang := place hang (
        (ended, folded),
        marked
      ) =>
        (endedSits (indent + 1) indent inner.trails close (waits => waits) byComputing ended folded, marked)
      rewrite plain then
        (hangsConcat (hangsCons [innerDoc, closerDoc] opening (hangsTwo middle (hangsPre closing innerReady)))) place _
            trace next byComputing entered
            (hangsAfter after))

-- A call's last argument.

--| A tuple's or list's parts in a group, broken or not, as one element: as `huggedBracket` writes them.
theorem groupedBracketHangs ∀ (kinds: Text → Tok) (list: Bool) (open: Word) (items: List Expr) (close: Word)
    (around: Around) (hard: Bool) (indent column: Nat)
    (opener: OpenerToken kinds open.text)
    (openTrailed: TrailsComment open)
    (closer: CloserToken kinds close.text)
    (closeComments: NotesComment close.comments.above)
    (closeTrailed: TrailsComment close)
    (comma: kinds "," = Comma)
    (each: ItemsHang kinds
      (indent + 2)
      (list && items.all Expr.plainItem)
      around.inArm
      open.trails
      open.trails
      (around.at + 1)
      items)
    (filledKeys: allKeysFrom
      (around.at + 1)
      (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
      = True)
    (brokenKeys: allKeysFrom
      (around.at + 1)
      (brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items)
      = True)
    (closeBefore: lastTrails open.trails items = True → (ListOf open items False close).trailsBeforeClose = True):
    ElHangs kinds
      (Group (bracketContent list open items close { around | hoisted = True }) hard)
      indent
      column
      False
      (close.trails || (ListOf open items False close).trailsBeforeClose)
      wordStart :=
  state entry =>
    hangsGroup hard
      (bracketContentHangs kinds list open items close
        { around | hoisted = True }
        indent
        column
        opener
        byComputing
        openTrailed
        closer
        closeComments
        closeTrailed
        comma
        each
        filledKeys
        brokenKeys
        closeBefore
        state
        entry)
