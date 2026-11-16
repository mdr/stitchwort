-- expect-error: E-TERMINATION
-- A squash: `MkSquash` has one data field, but `Squash` is a proposition,
-- so every `Squash (List Nat)` is the same proof to the kernel, and
-- `MkSquash r` isn't smaller than `MkSquash [x, ..r]`. The wrapper rule
-- needs `C`'s type to be data.
import Std (List, Nat, Unit)

type Squash (a: Type): Prop = | MkSquash (x: a)

def f: Squash (List Nat) → Unit
  | MkSquash [_, ..r] => f (MkSquash r)
  | MkSquash [] => Trivial
