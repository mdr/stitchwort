-- expect-error: E-NONEXHAUSTIVE
-- Prefixes don't cover every text either: the message lists them as
-- `"--" ++ _` beside the exact texts, a chain as the whole start.
def kind: Text → Nat
  | "--" ++ _ => 1
  | "-" => 2
  | "a" ++ "b" ++ _ => 3
