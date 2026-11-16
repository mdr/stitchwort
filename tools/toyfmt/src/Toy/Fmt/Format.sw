--| Formatting a Sprig source: parsed and printed by the rules. The output
--| depends on the source only through its tree, and it parses back to that
--| tree (`printParses`).

namespace Toy.Fmt
import Toy.Syntax (..)
import Std (Option, Result, Text)

--| What `format` answers: the file formatted (`Formatted`), or why there is
--| no answer: the source isn't valid toy syntax, a lex or parse error
--| (`ParseError`), the only case with no answer, as "line 3, column 9:
--| expected ',' or ')', got 'b'".
type FormatResult = | Formatted (text: Text) | ParseError (message: Text)

--| The answer as an `Option`: the formatted file if there is one.
def FormatResult.toOption: FormatResult → Option Text
  | Formatted text => Some text
  | ParseError _ => None

--| The source laid out afresh at `width`. The rules read the parsed tree
--| and nothing else, so the output depends on the source only through its
--| tree, and the output parses back to that same tree (`printParses`).
--| Both theorems about `format` (`formatRoundTrip`, `formatIdempotent`)
--| rest on that.
def format (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => ParseError message
  | Ok tree => Formatted (tree.print width)
