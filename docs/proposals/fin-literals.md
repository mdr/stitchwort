# Checked `Fin` literals

**Status:** built, 23 October 2026 (D1073, from the AoC Day 3 review). User
documentation: [syntax.md, "`Fin` literals"](../syntax.md#fin-literals).

**Problem.** `maxJoltage 2 [2, 7, 5, 7, 3]`, where a `List (Fin 10)` is
expected, was refused: "expected `Fin 10`, but this has type `Nat` … a numeral
can only be the prelude's `Nat` or `Int`". Tests built digits from text
(`Bank.parse "27573"`) or with `Fin.ofNat`.

**Rule.** A numeral `k` *checked against* `Fin n` (after unfolding, so
`Battery = Fin 10` counts) is decided by n:

| n | result |
|---|---|
| computes to a number, `k < n` (`Fin 10`, `Fin Ten`, `Fin (2 * 5)`) | `Fin.ofNatLt n k rfl` |
| computes to a number, `k >= n` | `E-FIN-LITERAL`: "7 isn't below 5, so it can't be a `Fin 5`" |
| a variable or stuck term (`Fin n`, `Fin (Succ n)`) | `E-FIN-LITERAL`, note: build it with `Fin.ofNatLt` |
| an unsolved metavariable (`Fin.toNat 3`) | `E-FIN-LITERAL`, note: annotate, `(3: Fin 10)` |

A negative numeral at `Fin` is `E-FIN-LITERAL` too. n is read with
`native::as_nat` (it forces the value, so definitions and native arithmetic
compute). The term is compact whatever k is: the kernel checks the `rfl`
against `Nat.leq (Succ k) n = True`, which the native `Nat.leq` decides, and
`Fin.ofNatLt` reduces to `FSucc`s around `FZero` when something looks inside
(so `(2: Fin 5) = FSucc (FSucc FZero)` is `rfl`). No `decide`/`auto` search
is involved. `Fin`, `FZero`, `FSucc` and `Fin.ofNatLt` become *library*
built-ins in the registry (as `Float` is), reached with `loaded_data`, so a
program that never loads `Std.Fin` is unaffected.

**Not changed.** Nothing defaults to `Fin`: the rule only runs in
`check_literal`'s "some other type" branch, after `Nat`, `Int`, `Float` and an
unsolved type (which still becomes `Nat`). Every program accepted before
elaborates to the same terms, so no existing hash moves. Arithmetic groups are
unchanged (`Fin` has no `Add`, so `i + 1` at `Fin` is still refused, by design:
[fin-arithmetic.md](fin-arithmetic.md)); in a comparison beside a `Fin`
(`d < 9`, `d == 9`) the numeral is checked against the `Fin`, as any bare
literal operand is against the group's type. Not done: `Fin (Succ n)` with n
unknown, where `0` could still be `FZero` (the bound is not a number); a
postponed check when n is a metavariable solved later.

**Patterns: in.** A number pattern on a column whose type is `Fin n` is
`FZero`, or `FSucc` around the pattern for `k - 1` (in `pattern_ctor`, beside
the `Int` case; such a column is split by constructor, not compared as
numbers). So patterns mix with `FZero`/`FSucc`, coverage is the indexed-family
coverage (`| 0 | 1 | 2` on `Fin 3` is complete, `| 0 => … | FSucc _ => …`
works for `Fin (Succ n)`), and a pattern at or above a known n is
`E-FIN-LITERAL` ("2 isn't below 2, so it can't match a `Fin 2`"). Known gap:
a missing case is reported in constructor terms (`no arm matches FZero`, one
level down), not as the missing number.
