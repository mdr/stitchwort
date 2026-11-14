-- Software Foundations, Volume 1: Logical Foundations, Poly.v, module
-- `OptionPlayground` (section "Polymorphic Options"), ported to
-- Stitchwort. Copyright and licence: sf/LICENSE-SF. Read it after `split`
-- in Poly.sw.

namespace Sf.Lf.Poly.OptionPlayground

-- Polymorphic options generalise the last chapter's `NatOption`:

type Option (a: Type) = | Some (x: a) | None

-- The book then makes the constructors' type argument implicit
-- (`Arguments Some {X}`); in Stitchwort it always is.
--
-- This is the same type as the library's `Option`, which the book's
-- definition is kept apart from, as Rocq's library already has one. The
-- rest of the chapter uses the library's.
