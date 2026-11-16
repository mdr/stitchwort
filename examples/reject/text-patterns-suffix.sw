-- expect-error: E-TEXT-PATTERN
-- A prefix pattern takes only a fixed start: matching how a text ends needs
-- a search, so it's a guard's job (`t.endsWith ".sw"`).
def isSource (path: Text): Bool := match path with
  | name ++ ".sw" => True
  | _ => False
