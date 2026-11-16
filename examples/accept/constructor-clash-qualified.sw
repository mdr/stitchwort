-- expect-warning: W-CTOR-HIDES
-- A constructor name means one thing in a file (D3615). Two types that
-- share one are used by qualifying it with the type, `Doc.Str`, and a file
-- that declares a constructor named like the prelude's warns where it does;
-- the prelude's is still reached as `Option.None`.
type Token = | Str (text: Text) | Name (text: Text)

type Doc = | Str (text: Text) | Line

def width (d: Doc): Nat := match d with
  | Doc.Str t => t.length
  | Line => 0

def token (t: Token): Text := match t with
  | Token.Str s => s
  | Name n => n

type Cell = | Wall | None

def get (o: Option Nat): Nat := match o with
  | Some n => n
  | Option.None => 0

def free (c: Cell): Bool := match c with
  | None => True
  | Wall => False
