-- Fuzz case 1095 (seed 0x5eede1ab00000685, Overmind, f06dd23cd), mutated from
-- examples/accept/partial-forwarding.sw. Reported E-INTERNAL: "`ask` is used
-- before it's checked". Note `ask`'s return type is `ask` itself.

import Std (Fail, IO, Nat, Option, Result, Text)

ability Env where
  ask: () → {Env} ask

def shown (n: Nat): {Nat, Fail, Env} Nat :=
  IO.print (Nat.toText n)
  if n > 100000000 then Fail.fail "too big" else Env.ask()

def collatz: IO → {Partial} Nat
  | 1 => 0
  | n => 1 + collatz (if n % 2 == 0 then n / 2 else 3 * n + 1)

def down: Nat → {IO, Partial} Nat
  | 0 => 0
  | n =>
    let step :=
      handle Fail.toResult (() => shown n) with
        | return result =>
          match result with
            | Ok v => v
            | Err _ => 0
        | Env.Nat u, k => k 1
    let extra := collatz (n % 8 + 1)
    step + extra + down (n - 1)

def main(): {IO, Partial} () :=
  let depth := IO.readLine() |> .getOrElse "" |> Text.toNat |> .getOrElse 50
  IO.print "total ${down depth}"
