--| Formatting a Sprig source: parsed and printed by the rules. The output
--| depends on the source only through its tree, and it parses back to that
--| tree (`printParses`).

namespace Toy.Fmt
import Toy.Syntax (..)
import Std (Option, Result, Text)

--| What `format` answers: the file formatted (`Stable`), or why there is
--| no answer: the parse error as "line 3, column 9: expected ',' or ')',
--| got 'b'".
type FormatResult = | Stable (printed: Printed) | Refused (message: Text)

--| The answer as an `Option`: the printed file if there is one.
def FormatResult.toOption: FormatResult → Option Printed
  | Stable printed => Some printed
  | Refused _ => None

--| The source laid out afresh at `width`. The rules read the parsed tree
--| and nothing else, so the output depends on the source only through its
--| tree, and the output parses back to that same tree (`printParses`).
--| Both theorems about `format` (`formatRoundTrip`, `formatIdempotent`)
--| rest on that.
def format (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => Refused message
  | Ok tree => Stable (tree.print width)
