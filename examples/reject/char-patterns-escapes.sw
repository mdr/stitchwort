-- expect-error: E-NONEXHAUSTIVE
-- The missing case names characters as they're written in source.
def special : Char -> Bool
  | '\n' => True
  | '\'' => True
  | 'x' => True
