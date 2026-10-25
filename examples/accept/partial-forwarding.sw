-- `Partial` mixed with other abilities that are forwarded
-- (docs/proposals/effect-runtime.md §9.3, stage 4c): a non-tail partial
-- recursion as deep as the number on the first input line (50 if there is
-- none), where each level runs handlers that forward `IO` to `main`'s runner
-- and calls a partial function with a smaller row. Each `print` leaves the
-- focus with every level still waiting below it, so the runner must route it
-- without looking at those waiting levels one by one.

import Std (Fail, IO, Nat, Option, Result, Text)

ability Env where
  ask: () -> {Env} Nat

-- Prints `n`, then asks for a step; fails on numbers too big to count.
def shown (n: Nat): {IO, Fail, Env} Nat :=
  IO.print (Nat.toText n)
  if n > 100000000 then Fail.fail "too big" else Env.ask()

-- A partial function with a smaller row than its callers'.
def collatz: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatz (if n % 2 == 0 then n / 2 else 3 * n + 1)

-- Each level: `Fail.toResult` forwards `IO` and `Env`, the `Env` handler
-- (whose result is partial) forwards `IO`, and `collatz` has a smaller row.
def down: Nat -> {IO, Partial} Nat
  | 0 => 0
  | n =>
    let step :=
      handle Fail.toResult (() => shown n) with
        | return result =>
          match result with
            | Ok v => v
            | Err _ => 0
        | Env.ask u, k => k 1
    let extra := collatz (n % 8 + 1)
    step + extra + down (n - 1)

def main(): {IO, Partial} () :=
  let depth := Option.getOrElse (Text.toNat (Option.getOrElse (IO.readLine()) "")) 50
  IO.print "total ${down depth}"
