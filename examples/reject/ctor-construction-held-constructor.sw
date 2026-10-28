-- expect-error: E-UNKNOWN-FIELD
-- Braces right after a constructor name its fields, even when its one field
-- holds a one-constructor type that is not a record: the hint names that
-- constructor, `Ok (Make { … })`.

type Outputs = | Make (initial: Nat) (gates: Nat)

def parsed: Result Outputs Text := Ok (Make { initial = 1, gates = 2 })

def same: Bool := parsed == Ok { initial = 1, gates = 2 }
