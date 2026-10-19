-- `Aoc` here is this namespace's own type, not the project's namespace Aoc.
namespace N

type Aoc: Type =
  | MkAoc

def x: Aoc := Aoc.MkAoc

test "x" := x == Aoc.MkAoc
