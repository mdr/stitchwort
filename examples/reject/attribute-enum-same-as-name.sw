-- expect-error: E-JS-NAME-CLASH
@[js.enum]
type Priority =
  | Low
  | @[js.name "Low"] High
