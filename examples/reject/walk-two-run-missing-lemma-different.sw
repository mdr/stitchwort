-- expect-error: E-WALK
-- A two-run walk needs a lemma for each pair of calls. Here the runs call
-- different functions, `here` and `there`; none is registered or named.
-- The message names both, shows both runs' calls and the goal there.

import Std (Parse, Nat)

def SameNat (x y: Nat): Prop := x = y

def here(): {Parse Nat} Nat := Parse.mark().offset

def there(): {Parse Nat} Nat := Parse.mark().offset + 1

def hereOnce(): {Parse Nat} Nat := here()

def thereOnce(): {Parse Nat} Nat := there()

theorem followsHereThere: Parse.Follows SameNat SameNat (() => hereOnce()) (() => thereOnce()) := byWalking []
