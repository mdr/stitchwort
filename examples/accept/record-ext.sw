-- Generated extensionality lemmas for records (SW-263): `T.ext` says two
-- values are equal when their data fields are. Proof fields are left out.

import Std (Nat, Eq)

-- A plain record.
type Point = { x: Nat, y: Nat }

theorem pointSwap (p: Point) (q: Point) (e1: p.x = q.x) (e2: p.y = q.y): p = q :=
  Point.ext p q e1 e2

-- A proof field: any two proofs of the equation are equal.
type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }

theorem dialSame (a: Dial 10) (b: Dial 10) (e: a.position = b.position): a = b :=
  Dial.ext a b e

-- A parameterised record, with a function field.
type Box (a: Type) = { item: a, show: a -> Text }

theorem boxSame (b: Box Nat) (c: Box Nat) (e1: b.item = c.item) (e2: b.show = c.show): b = c :=
  Box.ext b c e1 e2

-- No data fields: all values are equal.
type Unit2 = {}

theorem unit2 (a: Unit2) (b: Unit2): a = b := Unit2.ext a b

-- Only a proof field.
type Evidence = { ok: 1 = 1 }

theorem evidence (a: Evidence) (b: Evidence): a = b := Evidence.ext a b

-- A written `T.ext` wins over the generated one, with no clash.
type Mine = { v: Nat }
theorem Mine.ext (a: Mine) (b: Mine) (e: a.v = b.v): a = b :=
  match a, b with
    | { v = x }, { v = y } => Eq.cong (v => ({ v = v }: Mine)) e
