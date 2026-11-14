-- Software Foundations, Volume 1: Logical Foundations, Lists.v ("Lists:
-- Working with Structured Data"), ported to Stitchwort. Copyright and
-- licence: sf/LICENSE-SF. Exercises are stated as in Basics.sw: a
-- statement or a function with `?` for the reader to fill in. The
-- numbers are the book's own, from Nat.sw (see README.md).
--
-- The book puts most of this chapter in a module `NatList`, which is
-- NatList.sw next to this file: pairs, lists, bags, reasoning about
-- lists and options. Read it first. This file is the chapter's last
-- section, which is outside that module, and the module `PartialMap`
-- that follows it is PartialMap.sw.

namespace Sf.Lf.Lists
import Sf.Lf.Nat (Nat)
import Sf.Lf.Basics (..)
import Sf.Lf.Induction (..)

-- # Partial Maps
--
-- As a last example of defining data structures, here is a simple
-- *partial map* type, like the maps or dictionaries of most programming
-- languages.
--
-- First, a type of identifiers, to be the keys of the maps:

type Id = | MkId (n: Nat)

-- Internally an `Id` is just a number. Wrapping each number in the tag
-- `MkId` makes definitions more readable, and lets us change the
-- representation later.
--
-- The book names the constructor `Id`, like the type. In Stitchwort
-- that makes every later use of `Id` as a type ambiguous
-- (`E-AMBIGUOUS`), so the constructor is `MkId`, as in Basics' `Grade`.
--
-- An equality test for `Id`s:

def eqbId (x1 x2: Id): Bool := match x1, x2 with | MkId n1, MkId n2 => eqb n1 n2

-- Exercise: 1 star, standard (eqb_id_refl)

theorem eqbIdRefl ∀ (x: Id): eqbId x x = True := ?

-- The partial maps themselves are in PartialMap.sw.
