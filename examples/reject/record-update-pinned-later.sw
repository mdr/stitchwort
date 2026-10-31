-- expect-error: E-TYPE-MISMATCH
-- A replaced field of a record update that waits: `r.x` waits for `r`'s
-- type, which only `set p` fixes, and fails once it is known, after the
-- update has been checked. It still gets the note on the parameter the kept
-- field pins, as when `r` is annotated (`annotated`): the check carries the
-- field's error frame (docs/proposals/postponement.md, step 4.1, D2091).

import Std (List, Nat, Text)

type P = { x: Text }

type Box (a: Type) = { items: List a, first: a }

def later (b: Box Nat) (p: P): Box Nat :=
  let set := r => { b | first = r.x }
  set p

def annotated (b: Box Nat) (p: P): Box Nat :=
  let set := (r: P) => { b | first = r.x }
  set p
