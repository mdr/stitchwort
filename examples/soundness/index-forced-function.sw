-- expect-error: E-TERMINATION
-- Agda issue #6654, in `Prop`: `f` is a field of `B`, but its declared type
-- returns `p`, not `Bad`, so `f (Bad idP) bad` isn't smaller than the proof
-- matched, even though the index equation solves `f` as `x`. Accepting it
-- would prove `Void` (D143). Pairs with `leTrans` in
-- accept/indexed-families.sw, structural recursion on a proof
-- (docs/proposals/indexed-families.md §6.7, test 12).
def IdP: Prop := (p: Prop) -> p -> p

type Bad: IdP -> Prop =
  | B (f: IdP): Bad f

def idP: IdP := p h => h

def bad: Bad idP := B idP

theorem noBad [x: IdP]: Bad x -> Void
  | B f => noBad [x := idP] (f (Bad idP) bad)
