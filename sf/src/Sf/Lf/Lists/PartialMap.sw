-- Software Foundations, Volume 1: Logical Foundations, Lists.v, section
-- "Partial Maps" (module `PartialMap`), ported to Stitchwort. Copyright
-- and licence: sf/LICENSE-SF. Exercises are stated as in Basics.sw: a
-- statement with `?` for the reader to fill in.

namespace Sf.Lf.Lists.PartialMap
import Sf.Lf.Nat (Nat)
import Sf.Lf.Lists (..)
import Sf.Lf.Lists.NatList (..)

-- The book's module starts with `Export NatList`, to use `natoption`
-- here; the imports above do the same, and bring in Lists.sw's `Id`.
--
-- The type of partial maps:

type PartialMap =
  | Empty
  | Record (i: Id) (v: Nat) (m: PartialMap)

-- "There are two ways to build a `PartialMap`: the constructor `Empty`,
-- for the empty map, or `Record` applied to a key, a value and an
-- existing `PartialMap`, for a map with one more key-to-value entry."
--
-- `update` overrides the entry for a key by shadowing it with a new one
-- (or adds an entry, if the key isn't there yet).

def update (d: PartialMap) (x: Id) (value: Nat): PartialMap := Record x value d

-- `find` looks a key up. It gives `None` if the key isn't there, and
-- `Some v` if the key is mapped to `v`. If the key is mapped to more than
-- one value, it gives the first one it finds.

def find (x: Id) (d: PartialMap): NatOption := match d with
  | Empty => None
  | Record y v d' => if eqbId x y then Some v else find x d'

-- Exercise: 1 star, standard (update_eq)

theorem updateEq ∀ (d: PartialMap) (x: Id) (v: Nat): find x (update d x v) = Some v := ?

-- Exercise: 1 star, standard (update_neq)

theorem updateNeq ∀ (d: PartialMap) (x y: Id) (o: Nat) (h: eqbId x y = False): find x (update d y o) = find x d := ?
