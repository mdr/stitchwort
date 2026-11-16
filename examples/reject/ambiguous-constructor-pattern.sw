-- expect-error: E-AMBIGUOUS
-- Two types of this file have a constructor `Str`, so a bare `Str` has no
-- one meaning, even in a `match` on a `Doc`: the error names both spellings.
-- A file that needs only one of the types should not declare or import both
-- (keep a lexer and a printer in separate files).
type Token = | Str (text: Text) | Name (text: Text)

type Doc = | Str (text: Text) | Line

def width (d: Doc): Nat := match d with
  | Str t => 1
  | Line => 0
