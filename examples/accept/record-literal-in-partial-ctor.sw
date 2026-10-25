-- A record literal given to a partially applied constructor takes its type
-- from the function type expected (SW-195): in `xs.map (Cons { … })` the
-- missing field (the tail) fixes the list's element type before the given
-- field (the literal) is checked.

import Std (List)

type Hit = { row: Nat, column: Nat }

def prefixAll (c: Nat) (xs: List (List Hit)): List (List Hit) :=
  xs.map (Cons ({ row = 0, column = c }))

def paths (r: Nat) (c: Nat): List Bool → List (List Hit)
  | Nil => [Nil]
  | Cons b rest =>
    if b then
      List.append
        (match c with
          | Zero => [[{ row = r, column = c }]]
          | Succ k => (paths (r + 1) k rest).map (Cons ({ row = r, column = c })))
        ((paths (r + 1) (c + 1) rest).map (Cons ({ row = r, column = c })))
    else paths (r + 1) c rest
