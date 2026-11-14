-- Software Foundations, Volume 1: Logical Foundations, Poly.v, module
-- `MumbleGrumble` (an exercise in the section "Polymorphic Lists"),
-- ported to Stitchwort. Copyright and licence: sf/LICENSE-SF. Read it
-- after `repeat` in Poly.sw.

namespace Sf.Lf.Poly.MumbleGrumble
import Sf.Lf.Nat (..)

-- Exercise: 2 stars, standard, optional (mumble_grumble)
--
-- Consider these two data types. (The book's constructors are `a` to
-- `e`; in Stitchwort a constructor's name starts with a capital.)

type Mumble = | A | B (x: Mumble) (y: Nat) | C

type Grumble (a: Type) = | D (m: Mumble) | E (x: a)

-- Which of these are well-typed elements of `Grumble a`, for some type
-- `a`? Answer YES or NO for each.
--
-- - `D (B A (ofNat 5))`
-- - `D Mumble (B A (ofNat 5))`
-- - `D Bool (B A (ofNat 5))`
-- - `E Bool True`
-- - `E Mumble (B C O)`
-- - `E Bool (B C O)`
-- - `C`
--
-- The answers aren't the book's. In Rocq, `d` and `e` here take the type
-- `X` as their first, explicit argument (the book hasn't made it implicit
-- for `grumble`), so `d mumble (b a 5)` is fine and `d (b a 5)` isn't. In
-- Stitchwort a constructor never takes its type's parameters as
-- arguments (Poly.sw, "Polymorphic Lists"). To check an answer, give the
-- expression a type and run `stitchwort check`:
--
--     def check1: Grumble Bool := D (B A (ofNat 5))
