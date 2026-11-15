--| Formatting a Sprig source: parsed, then printed by the rules. This is
--| what the `toyfmt` driver calls for each file.

namespace Toy.Fmt
import Toy.Syntax (..)
import Std (Result, Text)

--| The source laid out afresh at `width`, or the parse error as "line 3,
--| column 9: expected ',' or ')', got 'b'".
def format (source: Text) (width: Nat): Result Printed Text := parse source |> .map (file => file.print width)
