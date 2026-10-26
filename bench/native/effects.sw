-- The N4 effects benchmark (native-compilation.md, "N4 as built"): a
-- state-passing handler counting, each `bump` an operation the handler
-- resumes with the state plus one, and a reader handler answering `ask`.
-- 1,000 operations of each here; the speed measurements use 1,000,000.
import Std (IO, Nat)

ability Counter where
  bump: () → {Counter} Nat

def Counter.from (init: Nat) (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return x => s => x
      | Counter.bump u, k => s => k s (s + 1)
  run init

def bumps: Nat → Nat → {Counter} Nat
  | 0, acc => acc
  | Succ n, acc => bumps n ((acc + Counter.bump()) % 1000000007)

ability Env where
  ask: () → {Env} Nat

def Env.give (value: Nat) (prog: () → {Env | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

def asks: Nat → Nat → {Env} Nat
  | 0, acc => acc
  | Succ n, acc => asks n (acc + Env.ask())

def main(): {IO} () :=
  IO.print "${Counter.from 0 (() => bumps 1000 0)} ${Env.give 3 (() => asks 1000 0)}"
