-- expect-error: E-NONEXHAUSTIVE
-- Prefixes don't cover every text either: the message lists them as
-- `"--" ++ _` beside the exact texts.
def kind: Text → Nat
  | "--" ++ _ => 1
  | "-" => 2
