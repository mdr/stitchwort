-- expect-error: E-PARSE
-- A constructor's explicit fields are all in brackets or all in braces.

type Shape = | Circle (id: Text) { radius: Nat }
