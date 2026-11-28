-- A type in another namespace, and a function that returns it.
namespace Outer

type Shape =
  | Circle (r: Nat)
  | Square (s: Nat)

def make (n: Nat): Shape :=
  if n == 0 then Circle 1 else Square 2
