-- expect-error: E-INSTANCE-NONE
-- `Ord` isn't derived for a type whose field has no `Ord` instance
-- (docs/proposals/interfaces.md §5.11), and the error says why. `Tagged`'s
-- field `tag` is a `Secret`, which has its own `==` but no ordering.

import Std (Eq)

type Secret = | Hidden (code: Nat)

instance Secret.instDecEq: DecEq Secret := { decide = (x y => Secret.decide x y) }

def Secret.decide: (x: Secret) -> (y: Secret) -> Decidable (x = y)
  | Hidden m, Hidden n => if h: m = n then Yes (Eq.cong Hidden h) else No (e => h (Eq.cong Secret.code e))

def Secret.code: Secret -> Nat
  | Hidden n => n

type Tagged = { name: Text, tag: Secret }

def sortTagged (xs: List Tagged): List Tagged := List.sort xs
