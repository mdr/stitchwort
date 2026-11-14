-- expect-error: E-NONEXHAUSTIVE
-- Text patterns alone never cover every case: there's always another text.
def keyword: Text → Nat
  | "def" => 1
  | "do" => 2
  | "else" => 3
