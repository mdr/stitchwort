-- `Plain` is a constructor of `Tok`, matched in two places.
namespace N

type Tok = | Plain | Other

def isPlain (t: Tok): Bool := match t with
  | Plain => True
  | Other => False

def notPlain (t: Tok): Bool := match t with
  | Plain => False
  | Other => True
