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

--| Where an item starts, laid at `inset`: a seat there, after a waiting comment only if `before`.
def ItemSeat (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (before: Bool): Place → Hang → Prop :=
  place hang =>
    hang = Hang.At (itemState outer top) ∧ Seat inset inset before (itemState outer top) place (wordStart inset place)

--| Where an item ended: its block's column at `inset` or right of it, a comment waiting only if `trails`.
def ItemEnd (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (trails: Bool): Place → Hang → Prop :=
  place hang =>
    ∃ (block: Option Nat) => deepFrom inset block = True
      ∧ Ended (itemDone outer top block) trails place
      ∧ hang = Hang.At (itemDone outer top block)

theorem openedItem ∀ (outer: List (Option Nat)) (top start: Option Nat):
    openedBy (itemState outer top) start = itemDone outer top start :=
  match start with
    | None => byComputing
    | Some column => byComputing

--| An item seated at `inset` starts its line, if it does, at `inset` or right of it.
theorem seatDeep ∀ (inset: Nat) (before: Bool) (state: HangState) (place: Place)
    (seated: Seated inset before state place):
    deepFrom inset (wordStart inset place) = True :=
  match place, seated with
    | AtStart at carry, (atInset, _) => rewrite atInset then Nat.leRefl inset
    | Broken at carry, (atInset, _) => rewrite atInset then Nat.leRefl inset
    | Mid at carry, _ => byComputing
    | Held at carry, (_, floor, _) =>
      let landed: floored carry (Nat.max inset (at + 2)) = Nat.max inset (at + 2) := rewrite floor
      rewrite landed then arithmetic

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

--| An item: from its seat, as its element hangs, to where it ended.
theorem itemHangs ∀ (kinds: Text → Tok) (doc: Doc) (inset: Nat) (outer: List (Option Nat))
    (top: Option Nat) (before trails: Bool)
    (el: ElHangs kinds doc inset inset before trails wordStart):
    HangLays kinds doc inset (ItemSeat inset outer top before) (ItemEnd inset outer top trails) :=
  place trace next (folded, seat) after =>
    let (seated, _, _, _) := seat
    let start := wordStart inset place
    el (itemState outer top) place place trace next (byComputing, folded, seat) (left later (ended, done) =>
      after left later (
        start,
        seatDeep inset before (itemState outer top) place seated,
        rewrite openedItem outer top start at ended then ended,
        rewrite openedItem outer top start at done then done
      ))

--| Right after a line break at `inset`, with no comment floor, an item may start.
theorem brokenItemSeat ∀ (inset: Nat) (outer: List (Option Nat)) (top: Option Nat) (before: Bool) (carry: Carry)
    (floor: carry.floor = None)
    (bound: (inForce outer top < inset) = True):
    ItemSeat inset outer top before
      (Broken (floored carry inset) (carry.breakTo inset))
      (Hang.At (itemState outer top)) :=
  let landed: floored carry inset = inset := rewrite floor
  rewrite landed then
    (byComputing, ((byComputing, byComputing), Nat.leRefl inset, arithmetic, (byComputing, arithmetic)))

--| Mid-line where an item may follow, an item may start.
theorem midItemSeat ∀ (inset at: Nat) (outer: List (Option Nat)) (top: Option Nat) (before: Bool) (carry: Carry)
    (floor: carry.floor = None)
    (left: (inForce outer top <= at) = True)
    (bound: (inForce outer top < inset) = True):
    ItemSeat inset outer top before (Mid at carry) (Hang.At (itemState outer top)) :=
  (byComputing, ((floor, left), Nat.leRefl inset, arithmetic, byComputing))

--| After a waiting comment, an item that may start there may start.
theorem heldItemSeat ∀ (inset at: Nat) (outer: List (Option Nat)) (top: Option Nat) (carry: Carry)
    (floor: carry.floor = None)
    (left: (inForce outer top <= at) = True)
    (bound: (inForce outer top < inset) = True):
    ItemSeat inset outer top True (Held at carry) (Hang.At (itemState outer top)) :=
  let landed: floored carry (Nat.max inset (at + 2)) = Nat.max inset (at + 2) := rewrite floor
  (
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

--| Each item of a broken bracket hangs as an element laid at `inset`, seated after the separator before it: after a
--| waiting comment only if the code before it, the opener or the item before, ends with one (`seat`).
def ItemsHang (kinds: Text → Tok) (inset: Nat) (bare arm before seat: Bool) (at: Nat): List Expr → Prop
  | [] => True
  | [item, ..rest] =>
    ElHangs kinds (item.el (firstAround bare arm before at)) inset inset seat item.trails wordStart
      ∧ ItemsHang kinds inset False arm False item.trails (at + item.size) rest

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
      hangsTwo kinds
        (if first then SoftLine else Line)
        doc
        inset
        (ItemGap outer top seat)
        (ItemSeat inset outer top seat)
        (ItemEnd inset outer top item.trails)
        (sepSeats kinds first inset outer top seat bound)
        (itemHangs kinds doc inset outer top seat item.trails el)
    | [next, ..more], (el, others) =>
      hangsCons kinds
        (if first then SoftLine else Line)
        [doc, Closing ",", ..brokenItems False arm False False (at + item.size) [next, ..more]]
        inset
        (ItemGap outer top seat)
        (ItemSeat inset outer top seat)
        (ItemEnd inset outer top (lastTrails item.trails [next, ..more]))
        (sepSeats kinds first inset outer top seat bound)
        (hangsCons kinds doc
          [Closing ",", ..brokenItems False arm False False (at + item.size) [next, ..more]]
          inset
          (ItemSeat inset outer top seat)
          (ItemEnd inset outer top item.trails)
          (ItemEnd inset outer top (lastTrails item.trails [next, ..more]))
          (itemHangs kinds doc inset outer top seat item.trails el)
          (hangsCons kinds
            (Closing ",")
            (brokenItems False arm False False (at + item.size) [next, ..more])
            inset
            (ItemEnd inset outer top item.trails)
            (ItemGap outer top item.trails)
            (ItemEnd inset outer top (lastTrails item.trails [next, ..more]))
            (commaHangs kinds inset outer top item.trails comma bound)
            (brokenItemsHang kinds False arm False False item.trails
              (at + item.size)
              inset
              outer
              top
              next
              more
              comma
              bound
              others)))
