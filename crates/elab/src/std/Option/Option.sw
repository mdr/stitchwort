-- Helpers for `Option`. These were in the core (docs/proposals/prelude-slim.md
-- stage 3); only the text readers needed them there.

def Option.flatMap (f: a -> Option b): Option a -> Option b
  | None => None
  | Some x  => f x

def Option.map (f: a -> b): Option a -> Option b
  | None => None
  | Some x  => Some (f x)
