--| Blocks by indentation: a deeper line continues its statement, a line at
--| the block's column starts the next one, and a shallower line ends the
--| block. Inside brackets line starts don't matter.

namespace Toy.Syntax.Tests
import Toy.Syntax (..)
import Std (Result, Text)

def dumped (source: Text): Result Text Text := parse source |> .map (file => file.dump)

test "a deeper line continues its statement" :=
  dumped "fn f() =\n  let x = 1\n    + 2\n  x"
    == Ok "(fn f () (body (let x (body (bare (+ (number 1) (number 2))))) (bare (var x))))\n"

test "a shallower line ends the block" :=
  dumped "fn f() =\n  x\nlet y = 1" == Ok "(fn f () (body (bare (var x))))\n(let y (body (bare (number 1))))\n"

test "a branch's block ends at its else" :=
  dumped "fn f() =\n  if a then\n    b\n    c\n  else d"
    == Ok "(fn f () (body (bare (if (var a) (body (bare (var b)) (bare (var c))) (body (bare (var d)))))))\n"

test "inside brackets a line may start anywhere" :=
  dumped "let x = f(a,\nb)\nlet y = 2"
    == Ok "(let x (body (bare (call (var f) (item (var a)) (item (var b))))))\n(let y (body (bare (number 2))))\n"

--| Whether both sources parse, to the same tree.
def sameTree (first second: Text): Bool := match parse first, parse second with
  | Ok one, Ok other => one == other
  | _, _ => False

test "an else at its block's column ends the block, as one to the left does" :=
  sameTree "let x = if a then\n    b\n    c\n    else d\n" "let x = if a then\n    b\n    c\n  else d\n"

test "a then at the column of the block before it ends the block" :=
  sameTree "let x = if if a then b else\n    c\n    d\n    then e else f\n"
      "let x = if if a then b else\n    c\n    d\n  then e else f\n"
