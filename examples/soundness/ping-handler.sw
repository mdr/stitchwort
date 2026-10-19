-- expect-error: E-TERMINATION
-- `Ping` (DESIGN.md §8): a clause that handles the original computation
-- again, instead of resuming it, loops forever. It's an ordinary recursive
-- call on the same argument, so the termination checker refuses it.
ability Ping where
  ping: () -> {Ping} ()

def bad (prog: () -> {Ping} a): a :=
  handle prog() with
    | return x     => x
    | ping u, k    => bad prog
