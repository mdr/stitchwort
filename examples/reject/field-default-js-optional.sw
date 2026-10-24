-- expect-error: E-ATTRIBUTE
-- `js.optional` and a default can't share a field: with a default, a
-- missing property already means the default and `undefined` means `None`
-- (docs/proposals/named-arguments.md §5.3, D1114).

type Paint =
  | Fill (@[js.optional] colour: Option Text := Some "black")
  | Clear
