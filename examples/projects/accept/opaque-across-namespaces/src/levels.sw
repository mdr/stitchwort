-- Opaque definitions, one unfolding another, and their equations.
namespace Levels
import Std (List, Nat)

opaque def Code: Type := Nat

opaque def start: Code
    unfolding Code
:=
  0

opaque def depthOf (code: Nat): Nat := code + 1

opaque def size: List Nat -> Nat
  | [] => 0
  | Cons _ rest => 1 + size rest
