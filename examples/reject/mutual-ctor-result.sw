-- expect-error: E-MUTUAL-KIND
-- A constructor's result type uses a function, and the function's type
-- mentions the data type (through a theorem it takes): a cycle.
type P: Type =
  | A
  | B

def pick (h: SameP A B → Void): P := A

type SameP (x: P): P → Prop =
  | R: SameP x (pick noAB)

theorem noAB: SameP A B → Void
  | ()
