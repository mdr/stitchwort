-- expect-error: E-INSTANCE-NONE
-- A derived order or display through another type must agree with that
-- type's own (docs/proposals/derived-equality.md §5.4), so it's built only
-- through `List`, `Option`, pairs and types whose instance is derived too.
-- Through a type whose module wrote its own `Ord` (or `Show`), or in a
-- group where one type has its own, it isn't derived, and the note says
-- why; `==` still is, since any two decisions of `x = y` agree. A group
-- with a field that can't be compared gets none, and the note names the
-- field. accept/mutual-data-derived.sw has the ones that are derived.

import Std (Eq, Nat, Ord, Show, Text)

-- A box ordered backwards, by hand.
type Box (a: Type) = | MkBox (inner: a)

theorem Box.sameInner ∀ (x y: Box a) (h: x.inner = y.inner): x = y := match x, y with
  | MkBox p, MkBox q => Eq.cong MkBox h

instance Box.instOrd [auto o: Ord a]: Ord (Box a) := Ord.byKey [ord := Ord.reverse] (b => b.inner) Box.sameInner

type Boxed = | End | More (next: Box Boxed)

test "equal through the box" := More (MkBox End) == More (MkBox End)
test "ordered through the box" := Ord.compare End (More (MkBox End)) == Less

-- A group where one type is shown by hand.
type Expr = | Number (n: Nat) | Block (body: Body)

type Body = | Empty | Line (first: Expr) (rest: Body)

instance Body.instShow: Show Body := { toText = b => "…", toSource = b => "…" }

test "equal in the group" := Block (Line (Number 1) Empty) == Block (Line (Number 1) Empty)
def describe (e: Expr): Text := "${e}"

-- A group with a function in it.
type Rule = | Accept | Check (guard: Guard)

type Guard = | Always (next: Rule) | When (holds: Nat → Bool) (next: Rule)

test "rules" := Accept == Accept
