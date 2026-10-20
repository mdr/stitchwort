-- Pure exports that mention partial functions without running them
-- (docs/proposals/partial.md §7.6). Generated code can't run a partial
-- computation, so every one is the same token, `$Delay`: nothing total can
-- tell two apart. A partial function itself can't be exported (E-JS-PARTIAL,
-- reject/export-partial.sw).
--
-- run: answer 3
-- run: answer 0
-- run: kept 5

import Std.Effect (Delay)

def collatzSteps: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def discard (f: Nat -> {Partial} Nat): Nat := 0

def firstOf: Pair Nat (Nat -> {Partial} Nat) -> Nat
  | MkPair n f => n

-- `collatzSteps` is passed bare, applied under a lambda, and stored in data;
-- none of it runs.
export def answer (n: Nat): Nat := discard collatzSteps + discard (\m => collatzSteps (m + n)) + n

export def kept (n: Nat): Nat := firstOf (MkPair n collatzSteps)
