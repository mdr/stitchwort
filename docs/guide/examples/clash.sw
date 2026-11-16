-- begin qualified
type Token = | Str (text: Text) | Name (text: Text)
type Doc = | Str (text: Text) | Line

def Token.label: Token → Text
  | Token.Str text => text
  | Name text => text

def Doc.width: Doc → Nat
  | Doc.Str text => text.length
  | Line => 0
-- end qualified

test "qualified" := (Doc.Str "ab").width == 2
