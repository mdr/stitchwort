--| Formatting a Sprig source: parsed and printed by the rules
--| (`formatDirect`, what the `toyfmt` driver calls for each file), or
--| that with the output checked at run time (`format`, which the tests
--| use: it answers the same, `formatAgrees`).

namespace Toy.Fmt
import Toy.Syntax (..)
import Std (Option, Result, Text)

--| What `format` answers: the file formatted, only after the output was
--| checked to read back as the same tree (`Stable`), or why there is no
--| answer: the parse error as "line 3, column 9: expected ',' or ')', got
--| 'b'", or a failed check (a bug in the formatter, never in the source).
type FormatResult = | Stable (printed: Printed) | Refused (message: Text)

--| The answer as an `Option`: the printed file if there is one.
def FormatResult.toOption: FormatResult → Option Printed
  | Stable printed => Some printed
  | Refused _ => None

--| The source laid out afresh at `width`. The rules read the parsed tree
--| and nothing else, so the output depends on the source only through its
--| tree; and the answer is `Stable` only if the output parses to that same
--| tree. Both theorems about `format` (`formatRoundTrip`, `formatIdempotent`)
--| rest on that check.
def format (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => Refused message
  | Ok tree =>
    let printed := tree.print width
    if parse printed.text == Ok tree then Stable printed
    else Refused "internal error: the formatted text doesn't read back as the same tree"

--| `format` without its re-parse: the source parsed and its tree printed.
--| Nothing is checked at run time, and nothing needs to be: the printed
--| text of a parsed file parses to the same file (`printParses`), so this
--| answers what `format` does on every source (`formatAgrees`), and
--| formats again to itself (`formatDirectIdempotent`). The `toyfmt` driver
--| calls this.
def formatDirect (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => Refused message
  | Ok tree => Stable (tree.print width)
