-- Laying items end to end from a start offset, as `zipWith` of the items
-- and their running offsets (`scanLeft`), and proving it with the std
-- lemmas (std/List/Toolkit.sw, std/List/Index.sw): every item keeps its id,
-- item k starts at the start plus the sizes before it, and each item starts
-- where the one before it ends.
import Std (List)

type Item = { id: Nat, size: Nat, start: Nat }

def moveTo (offset: Nat) (item: Item): Item := { item | start = offset }

def layout (start: Nat) (items: List Item): List Item :=
  List.zipWith items (List.scanLeft items start (offset item => offset + item.size)) (item offset => moveTo offset item)

def blank: Item := { id = 0, size = 0, start = 0 }

def sample: List Item := [{ id = 1, size = 2, start = 0 }, { id = 2, size = 3, start = 0 }, { id = 3, size = 4, start = 0 }]

test "starts" := List.map (layout 10 sample) (item => item.start) == [10, 12, 15]

theorem layoutLength (start: Nat) (items: List Item): List.length (layout start items) = List.length items :=
  List.lengthZipWithScanLeft (offset item => offset + item.size) (item offset => moveTo offset item) items start

theorem layoutIds (start: Nat) (items: List Item): List.map (layout start items) (item => item.id) = List.map items (item => item.id) :=
  List.mapZipWithScanLeft (item => item.id) (item => item.id) (item offset => moveTo offset item) (item offset => rfl)
    items start (offset item => offset + item.size)

theorem layoutStart (start: Nat) (items: List Item) (k: Nat) (h: k < List.length items):
    (List.getOr (layout start items) blank k).start = start + List.sumBy (List.take items k) (item => item.size) :=
  rewrite List.getOrZipWithScanLeft (offset item => offset + item.size) (item offset => moveTo offset item) blank blank items start k h in
  List.sumByFrom (List.take items k) start (item => item.size)

theorem layoutContiguous (start: Nat) (items: List Item) (k: Nat) (h: Succ k < List.length items):
    (List.getOr (layout start items) blank (Succ k)).start
      = (List.getOr (layout start items) blank k).start + (List.getOr items blank k).size :=
  rewrite List.getOrZipWithScanLeft (offset item => offset + item.size) (item offset => moveTo offset item) blank blank items start (Succ k) h,
    List.getOrZipWithScanLeft (offset item => offset + item.size) (item offset => moveTo offset item) blank blank items start k omega,
    List.foldLeftTakeSucc (offset item => offset + item.size) blank items start k omega in
  rfl

-- The same placement as `mapAccumLeft`, threading the offset.
theorem layoutMapAccum (start: Nat) (items: List Item):
    Pair.snd (List.mapAccumLeft items start (offset item => MkPair (offset + item.size) (moveTo offset item))) = layout start items :=
  List.mapAccumLeftList items start (offset item => MkPair (offset + item.size) (moveTo offset item))
