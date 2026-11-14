-- expect-error: E-TEXT-PATTERN
-- A text pattern is one fixed text: an interpolation would need a search.
def greeting (name: Text) (line: Text): Bool := match line with
  | "hello ${name}" => True
  | _ => False
