-- expect-error: E-TAILREC
-- A call inside `handle … with` is under a handler that waits for its
-- result, so each call adds a handler.
import Std (Nat)

ability Counter where
  bump: () → {Counter} ()

@[tailrec]
def f: Nat → Nat
  | 0 => 0
  | Succ n =>
    handle (bump(); f n) with
      | return x => x
      | bump u, k => k()
