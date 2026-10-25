-- Types that match an app's own TypeScript types (docs/syntax.md, Attributes;
-- docs/proposals/attributes.md, "As built (stage 2)"):
--
-- - every list in a declaration is a mutable `T[]`, so an app's `{ xs: T[] }`
--   and the generated type are assignable both ways;
-- - `js.optional` on a constructor's `Option` field makes it an optional
--   property, `fill?: string`, like the app's `fill?: string`: a missing key
--   (or `undefined`) is `None`, and `None` is no key. A record's `Option`
--   fields are optional properties already.
--
-- run: area (Circle 2 None)
-- run: area (Circle 2 (Some "red"))
-- run: area (Polygon [{ x = 0, y = 0 }, { x = 1, y = 1 }] None)
-- run: recolour (Circle 2 None)
-- run: recolour (Circle 2 (Some "red"))
-- run: recolour (Polygon [] (Some "x"))
-- run: recolour Dot
-- run: tag (Circle 2 (Some "red"))
-- run: total { id = 1, lines = [{ sku = "a", quantity = 2 }, { sku = "b", quantity = 3 }], coupon = None }
-- run: withCoupon { id = 1, lines = [], coupon = None }
-- run: countItems [{ sku = "a", quantity = 1 }]

type Point = { x: Nat, y: Nat }

@[js.tag "kind"]
type Shape =
  | @[js.name "circle"] Circle (radius: Nat) (@[js.optional] fill: Option Text)
  | @[js.name "polygon"] Polygon (points: List Point) (@[js.name "fillColour", js.optional] fill: Option Text)
  | @[js.name "dot"] Dot

export def area: Shape → Nat
  | Circle r _ => r * r
  | Polygon ps _ => ps.length
  | Dot => 0

export def recolour: Shape → Shape
  | Circle r None => Circle r (Some "black")
  | Circle r (Some _) => Circle r None
  | Polygon ps _ => Polygon ps (Some "grey")
  | Dot => Dot

export def tag: Shape → Option Text
  | Circle _ f => f
  | Polygon _ f => f
  | Dot => None

type Item = { sku: Text, quantity: Nat }

type Order = { id: Nat, lines: List Item, coupon: Option Text }

export def total (o: Order): Nat := o.lines.length

export def withCoupon (o: Order): Order := { o | coupon = Some "SAVE" }

-- A function's list parameter is `readonly Item[]`, so a caller may pass a
-- `readonly` array too.
export def countItems (items: List Item): Nat := items.length
