-- expect-error: E-NOT-EMPTY
-- `()` matches an equation only of two different constructors: `Robot =
-- Robot` has a proof.

type Tile = | Wall | Robot

theorem bad: Robot = Robot -> Void
  | ()
