-- expect-error: E-ATTRIBUTE
type Label =
  | Important (@[js.enum] n: Nat)
  | SlideText
