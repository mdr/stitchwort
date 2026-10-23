-- Attributes set a data type's JavaScript form (docs/syntax.md, Attributes;
-- docs/proposals/attributes.md): `js.tag` is the key that says which
-- constructor an object is (`$tag` without it), and `js.name` is a
-- constructor's tag value, or a field's key. Inside Stitchwort nothing
-- changes: patterns, field access and `show` use the Stitchwort names.
--
-- run: area (Circle 3 4)
-- run: area Dot
-- run: grow (Polygon 5 "pent")
-- run: grow (Circle 1 2)
-- run: shapes [Dot, Circle 1 2, Polygon 3 "tri"]
-- run: describe (Circle 1 2)
-- run: render { kind = "svg", shapes = [Dot, Circle 2 0] }
-- run: rename { kind = "svg", shapes = [] }
-- run: flip (Picture 7 "a.png")
-- run: flip (Note 1 "hi")
-- run: odd (Constructor 1)
-- run: odd (Proto "p")
-- run: odd ToString

@[js.tag "type"]
type Shape =
  | @[js.name "DOT"] Dot
  | @[js.name "CIRCLE"] Circle (radius: Nat) (@[js.name "center_x"] centerX: Nat)
  | @[js.name "POLYGON"] Polygon (sides: Nat) (label: Text)

export def area: Shape -> Nat
  | Dot => 0
  | Circle r x => r * r + x
  | Polygon n _ => n

export def grow: Shape -> Shape
  | Dot => Dot
  | Circle r x => Circle (r + 1) x
  | Polygon n l => Polygon (n + 1) (l ++ "!")

export def shapes (xs: List Shape): List Shape := xs.reverse

-- `show` prints the Stitchwort names, not the JS ones.
export def describe (s: Shape): Text := "${s}"

-- A record's field keys too.
type Drawing = {
  @[js.name "type"] kind: Text,
  @[js.name "items"] shapes: List Shape
}

export def render (d: Drawing): Nat := d.shapes.length + d.kind.length

export def rename (d: Drawing): Drawing := { d | kind = d.kind ++ "2" }

-- The same logical field may have a different key in each constructor.
-- Attributes may span lines, and a group may close at the start of a line.
@[
  js.tag "kind"
]
type Message =
  | Note (@[js.name "note_id"] id: Nat) (body: Text)
  | Picture (@[js.name "picture_id"] id: Nat) (url: Text)

export def flip: Message -> Message
  | Note i b => Picture i b
  | Picture i u => Note i u

-- Tag values that are also the names of `Object.prototype`'s properties
-- dispatch correctly, and a field called `tag` keeps its key.
type Odd =
  | @[js.name "constructor"] Constructor (tag: Nat)
  | @[js.name "__proto__"] Proto (@[js.name "a-b"] value: Text)
  | @[js.name "toString"] ToString

export def odd (o: Odd): Odd := o
