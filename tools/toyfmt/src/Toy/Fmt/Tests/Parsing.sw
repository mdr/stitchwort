--| The goldens through the parser: each source parses to its tree, the
--| source and the formatted text both format to the formatted text, and so
--| does every disturbed copy of it.

namespace Toy.Fmt.Tests
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (List, Option, Result, Text)

def Golden.formats (golden: Golden) (text: Text): Option Text :=
  format text golden.width |> .toOption |> .map (printed => printed.text)

def Golden.parsesToTree (golden: Golden): Bool := parse golden.source == Ok golden.tree

test "each golden's source parses to its tree" := goldens.all Golden.parsesToTree

test "each golden's source formats to its formatted text" :=
  goldens.all (golden => golden.formats golden.source == Some golden.formatted)

test "each golden's formatted text formats to itself" :=
  goldens.all (golden => golden.formats golden.formatted == Some golden.formatted)

test "each golden survives 50 disturbances" := goldens.all (golden => golden.survivesDisturbance golden.formats)
