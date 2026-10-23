-- expect-error: E-NONEXHAUSTIVE
-- Coverage of a named-field pattern is its positional pattern's: the
-- circles whose `start` isn't 0 are missing.

type Shape =
  | Dot (ref: Nat) (start: Nat)
  | Circle (ref: Nat) (start: Nat) (text: Text)

def describe: Shape -> Text
  | Dot { .. }               => "dot"
  | Circle { start = 0, .. } => "at zero"
