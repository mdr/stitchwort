-- expect-error: E-TEXT-PATTERN
-- The rest of a `Text` is a `Text`: a list pattern there would match its
-- characters, which the type doesn't say.
def arrow: Text → Bool
  | "->" ++ [c, ..cs] => True
  | _ => False
