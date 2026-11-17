-- `App`'s own `closerAhead` is declared in another file of the namespace,
-- and still wins over the one `import Lib (..)` brings (D3671).
namespace App
import Lib (..)

def next (xs: List Nat): Bool := closerAhead xs
