-- expect-error: E-INSTANCE-NONE
-- `Ord` isn't derived for a type whose field has no `Ord` instance
-- (docs/proposals/interfaces.md §5.11), and the error says why. `Tagged`'s
-- field `tag` is a `Secret`, which has its own `==` but no ordering: its
-- field is a quotient, which has none.

import Std (Eq, List)

def AllSame (x: Nat) (y: Nat): Prop := Unit

type Secret = { code: Quot Nat AllSame }

theorem Secret.codeSame (p: Quot Nat AllSame) (q: Quot Nat AllSame): p = q :=
  Quot.ind [p := p' => p' = q]
    (x => Quot.ind [p := q' => Quot.mk x = q'] (y => Quot.sound Trivial) q)
    p

theorem Secret.same: (x: Secret) → (y: Secret) → x = y
  | { code = a }, { code = b } => Eq.cong (c => ({ code = c }: Secret)) (Secret.codeSame a b)

instance Secret.instDecEq: DecEq Secret := { decide = x y => Yes (Secret.same x y) }

type Tagged = { name: Text, tag: Secret }

def sortTagged (xs: List Tagged): List Tagged := List.sort xs
