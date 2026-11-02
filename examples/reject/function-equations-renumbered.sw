-- expect-error: E-UNKNOWN-NAME
-- `size` has two arms, so `size.eq3` is a name an earlier version of the
-- definition had (arms are numbered, and adding or removing one renumbers
-- the rest): the error says which equations exist and points at `doc`
-- (docs/proposals/function-equations.md, stage 1c).
import Std (List, Nat)

def size: List Nat → Nat
  | [] => 0
  | Cons _ rest => size rest + 1

theorem sizeOfThree (xs: List Nat): size (Cons 3 xs) = size xs + 1 := size.eq3 3 xs
