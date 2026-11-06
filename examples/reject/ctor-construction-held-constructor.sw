-- expect-error: E-UNKNOWN-FIELD
-- Braces right after a constructor declared with its fields in braces name
-- its fields, even when its one field holds a one-constructor type that is
-- not a record: the hint names that constructor, `MkParsed (Make { … })`.

type Outputs = | Make { initial: Nat, gates: Nat }

type Parsed = | MkParsed { outputs: Outputs }

def parsed: Parsed := MkParsed { initial = 1, gates = 2 }
