-- In a group of types defined together, one with its own `DecEq` instance
-- keeps it, and only its own `Ord` instance waits for it to be checked: the
-- others, and the orders' functions and laws, are derived with the group
-- (docs/proposals/derived-equality.md §5.3).

import Std (Decidable, Eq, Option, Ord)

type Frame = { inner: Option Shape, depth: Nat }

type Shape = | Flat | Boxed (frame: Frame)

def Frame.decide (x y: Frame): Decidable (x = y) :=
  if h: (x.inner, x.depth) = (y.inner, y.depth) then Decidable.yes (Frame.sameParts x y h)
  else Decidable.no (e => h (Eq.cong (f => (f.inner, f.depth)) e))

theorem Frame.sameParts ∀ (x y: Frame) (h: (x.inner, x.depth) = (y.inner, y.depth)): x = y := match x, y with
  | { inner = a1, depth = b1 }, { inner = a2, depth = b2 } =>
    rewrite Eq.cong Pair.fst h, Eq.cong Pair.snd h then byComputing

instance Frame.instDecEq: DecEq Frame := { decide = Frame.decide }

def shallow: Frame := { inner = None, depth = 1 }
def deep: Frame := { inner = Some (Boxed shallow), depth = 0 }

test "the group's other type has its derived ==" := Boxed shallow == Boxed shallow && Boxed shallow != Flat
test "the own DecEq is used" := deep == deep && deep != shallow
-- `Shape`'s order is derived with the group, `Frame`'s once its `DecEq` is.
test "shape order" := Flat < Boxed shallow && Boxed shallow < Boxed deep
test "frame order" := shallow < deep || deep < shallow
test "frame compare" := Ord.compare deep deep == Equal
