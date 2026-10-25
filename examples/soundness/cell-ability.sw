-- expect-error: E-ABILITY
-- Landin's knot (DESIGN.md §8): an operation that stores a computation
-- using the same ability could loop forever.
ability Cell where
  write: (() → {Cell} ()) → {Cell} ()
