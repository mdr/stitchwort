-- Start-up only: read the input and print its length.
namespace Scratch.Hello
import Std (IO, Text)

def main(): {IO} () :=
  let input := IO.readAll()
  IO.print "Read ${Text.length input}"
