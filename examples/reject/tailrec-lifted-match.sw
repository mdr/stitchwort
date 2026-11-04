-- expect-error: E-TAILREC
-- A `match` lifted out of the definition is part of it, but here its result
-- is added to, so the calls in it are not tail calls.
import Std (List, Nat, Option)

def halve (n: Nat): Option Nat := if n == 0 then None else Some (n / 2)

@[tailrec]
def count: List Nat → Nat
  | [] => 0
  | [x, ..rest] =>
    1 + match halve x with
      | None => count rest
      | Some _ => count rest
