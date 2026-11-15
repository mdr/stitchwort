--| Probes for the sketch's findings: what the parser does where the
--| open goals' statements have to change (SKETCH.md, "Statements that
--| must change").

namespace Toy.Sketch.Tests
import Toy.Syntax (..)
import Std (Result, Text)

def sameTree (first second: Text): Bool := match parse first, parse second with
  | Ok one, Ok other => one == other
  | _, _ => False

test "an else at its block's column ends the block, as one to the left does" :=
  sameTree "let x = if a then\n    b\n    c\n    else d\n" "let x = if a then\n    b\n    c\n  else d\n"

test "a then at the column of the block before it ends the block" :=
  sameTree "let x = if if a then b else\n    c\n    d\n    then e else f\n"
      "let x = if if a then b else\n    c\n    d\n  then e else f\n"
