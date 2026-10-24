-- expect-error: E-FIELD-DEFAULT
-- An interface's methods can't have defaults: each instance gives every
-- method (docs/proposals/named-arguments.md, "As built (stage 2)").

interface Describe (a: Type) = {
  describe: a -> Text,
  name: Text := "thing"
}
