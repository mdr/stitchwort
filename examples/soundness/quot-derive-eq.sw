-- expect-error: E-INSTANCE-NONE
-- R4 (docs/proposals/map-equality.md §7.6): `==` is never derived for a
-- quotient by comparing the values it was made from, which would say
-- `Quot.mk False` and `Quot.mk True` differ although they're equal. So a
-- record with a quotient field has no `==` unless the quotient's is written;
-- the message names the field. Pairs with accept/quot-deceq.sw (A10), which
-- writes one.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

type Box = { q: Q }

def same (b: Box): Bool := b == b
