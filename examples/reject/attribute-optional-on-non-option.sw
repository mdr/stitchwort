-- expect-error: E-ATTRIBUTE
-- Only a field of type `Option T` can be an optional property.
type Shape =
  | Circle (radius: Nat) (@[js.optional] fill: Text)
