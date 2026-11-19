-- expect-error: E-PARSE
-- A proof block is written by indentation, not braces: `{` starts a record
-- or a record update, so the error points at the closing brace. The note
-- says how a proof block is written (SW-4274).

theorem t: 1 + 1 = 2 := {
  let x := 1
  byComputing }
