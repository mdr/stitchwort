-- expect-error: E-UNKNOWN-NAME
-- `?hole` reads as the hole `?` applied to `hole`, since a proof's hole has
-- no name. The note says to write `?` alone and that named holes belong to
-- search patterns (SW-4274).

import Std (Nat)

theorem t (n: Nat): n = n := ?hole
