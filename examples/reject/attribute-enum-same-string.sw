-- expect-error: E-JS-NAME-CLASH
@[js.enum]
type Priority =
  | @[js.name "x"] Low
  | @[js.name "x"] High
