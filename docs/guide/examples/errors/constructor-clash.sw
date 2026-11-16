type Token = | Str (text: Text) | Name (text: Text)
type Doc = | Str (text: Text) | Line

def Doc.width: Doc → Nat
  | Str text => text.length
  | Line => 0
