-- String unions (docs/syntax.md, Attributes; docs/proposals/attributes.md,
-- "As built (stage 2b: string unions)"): `@[js.enum]` on a data type whose
-- constructors have no fields makes it cross as a plain string, each
-- constructor as its name, or as its `@[js.name "…"]`, instead of as an
-- object `{ $tag: "…" }`. In TypeScript, `type Label = "IMPORTANT" | …`.
--
-- run: toggle Important
-- run: toggle SlideText
-- run: tickets
-- run: describe { label = SlideText, priority = Some High, tags = [Important, SlideText] }
-- run: describe { label = Important, priority = None, tags = [] }
-- run: shout (Ping Important None)
-- run: shout (Ping SlideText (Some High))
-- run: shout Pong
-- run: rank High
-- run: colourOf Red
-- run: byLabel (Map.fromList [("a", Important), ("b", SlideText)])
-- run: fixed Two

import Std (Map)

@[js.enum]
type Label =
  | @[js.name "IMPORTANT"] Important
  | @[js.name "SLIDE_TEXT"] SlideText

-- `js.name` chooses the string (without it, the constructor's name).
@[js.enum]
type Priority =
  | @[js.name "low"] Low
  | @[js.name "high"] High

-- No `js.name`: the strings are `"Red"` and `"Green"`.
@[js.enum]
type Colour =
  | Red
  | Green

-- A type parameter isn't a field, so it is allowed.
@[js.enum]
type Fixed (a: Type) =
  | One
  | Two

type Ticket = { label: Label, priority: Option Priority, tags: List Label }

-- A tagged union with a string union in its fields, one optional.
@[js.tag "kind"]
type Message =
  | @[js.name "ping"] Ping (label: Label) (@[js.optional] urgency: Option Priority)
  | @[js.name "pong"] Pong

export def toggle: Label -> Label
  | Important => SlideText
  | SlideText => Important

export def tickets: List Ticket :=
  [{ label = Important, priority = Some High, tags = [SlideText] }]

def priorityText: Option Priority -> Text
  | None => "no priority"
  | Some Low => "low"
  | Some High => "high"

export def describe (t: Ticket): Text := priorityText t.priority

export def shout: Message -> Message
  | Ping l u => Ping (toggle l) u
  | Pong => Pong

export def rank: Priority -> Nat
  | Low => 1
  | High => 2

export def colourOf (c: Colour): Colour := c

export def byLabel (xs: Map Text Label): Map Text Label := xs

export def fixed (f: Fixed Nat): Fixed Nat := f
