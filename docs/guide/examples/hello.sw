-- Chapter 1: a first program. Run it with
--   stitchwort run hello.sw < hello.input
import Std (IO, List, Text)

def main(): {IO} () :=
  let names := IO.readAllLines()
  names.map (name => IO.print (greeting name))
  IO.print "Greeted ${names.length} people"

def greeting (name: Text): Text := "Hello, ${name}!"

test "greeting" := greeting "Ada" == "Hello, Ada!"
