-- Fields with defaults at the JS boundary (docs/proposals/named-arguments.md
-- §5.3): going in, a defaulted field may be left out, and the decoder fills
-- it by running the default, in field order, from the fields before it.
-- Coming out, a value has every field. The TypeScript declarations have two
-- shapes: `RangeOptionsInput` for parameters, `RangeOptions` for results.
-- A defaulted `Option` field tells a missing property (the default) from
-- `undefined` (`None`), and is always present on output (D1114).
--
-- run: bounds { stop = 10 }
-- run: bounds { start = 2, stop = 10, step = 3 }
-- run: widen { stop = 4 }
-- run: colourOf { nick = None }
-- run: colourOf { colour = None, nick = None }
-- run: colourOf { colour = Some "red", nick = None }
-- run: echo { colour = None, nick = None }
-- run: echo { nick = Some "Al" }
-- run: area { width = 3 }
-- run: area { width = 3, height = 2 }
-- run: area { width = 3, height = 2, area = 7 }
-- run: label (Circle { radius = 1 })
-- run: label (Circle { radius = 1, label = "wheel" })
-- run: label Dot
-- run: steps [{ name = "a", options = { stop = 3 } }, { name = "b", options = { stop = 3, step = 2 } }]
-- run: boxLabel { item = 1 }
-- run: boxLabel { item = 1, label = "crate" }
-- run: nested { item = { stop = 2 } }

import Std (List, Nat, Option, Text)

type RangeOptions = {
  start: Nat := 0,
  stop: Nat,
  step: Nat := 1
}

export def bounds (options: RangeOptions): List Nat :=
  [options.start, options.stop, options.step]

-- A result has every field.
export def widen (options: RangeOptions): RangeOptions := { options | stop = options.stop + 10 }

-- A missing `colour` is its default; `undefined` is `None`. `nick` has no
-- default, so it keeps the encoding of a record's `Option` field: missing
-- and `undefined` are both `None`, and `None` is no property.
type Config = {
  colour: Option Text := Some "blue",
  nick: Option Text
}

export def colourOf (config: Config): Option Text := config.colour

export def echo (config: Config): Config := config

-- Defaults that use the fields before them, given or defaulted.
type Rect = {
  width: Nat,
  height: Nat := width,
  area: Nat := width * height
}

export def area (rect: Rect): List Nat := [rect.width, rect.height, rect.area]

-- A constructor's field.
type Shape =
  | Circle (radius: Nat) (label: Text := "circle")
  | Dot

export def label: Shape -> Text
  | Circle _ l => l
  | Dot => "dot"

-- All the way down: a record holding one with defaults has an input shape
-- too, `JobInput`.
type Job = { name: Text, options: RangeOptions }

export def steps (jobs: List Job): List Nat := List.map (job => job.options.step) jobs

-- A generic record: `BoxInput<T>`, and a type argument is an input too,
-- `BoxInput<RangeOptionsInput>`.
type Box (a: Type) = { item: a, label: Text := "box", extra: List a := [] }

export def boxLabel (box: Box Nat): Text := box.label

export def nested (box: Box RangeOptions): Box RangeOptions := box
