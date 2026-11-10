# SW-2572 review: `*` shortcut and head check first (Opus, 10 Nov 2026)

Commit `2b93499d1` on `lane/SW-2572`. A paper review. The only things run
were `natives::shortcuts_with_unknowns_agree_with_the_definitions` and
`resources::remainders_of_long_numbers_check_in_linear_time`. Both pass
(0.3 s and 1.8 s).

## Verdict

**Sound. Merge after one small fix (F1).** The shortcut gives exactly the
value that `k` steps of `Nat.mul`'s case tree, plus `add`'s native, give. It
is the same value, not just an equal one, so conversion, hashes and
read-back can't tell the two apart. F1 is a resource regression, not a
soundness one: for `x * n` with `x` plainly stuck, the new arm forces `n`,
which the definition never does. F2 and F3 are small follow-ups.

## Agreement with the definition

`Nat.mul` (`std/core/Data.sw`) recurses on its **first** argument:
`Zero, n => 0` and `Succ m, n => n + Nat.mul m n`.

- **Steps.** Take `k` steps on `k + m`, with `n` a number `N` and `m`
  neither a number nor `Zero`/`Succ`. The result is
  `N + (N + … + mul m n)`. Each `add` has a number on its left, so `add`'s
  native folds the sum into `NatAdd(k·N, mul m n)`. Here `mul m n` is
  `stuck_tree`'s `Neutral(Head::Def(mul), [m, n])`, with the spine as the
  case tree bound it. `view_keeping` returns the same `m` in every case:
  the stored base of a `NatAdd` (which is what `split_value` binds), the
  unforced `fields[0]` of a `Succ` constructor, a glued `Value::Call`, or a
  solved meta left unforced. `n` is the unforced argument both times.
  `add`'s `view` returns the forced stuck call, but forcing a `Head::Def`
  neutral does nothing. So the values are **identical**, and the lane's
  "different but equal" caveat is more cautious than it needs to be.
- **Orientation.** The residual is `mul m n` (stuck part first), which is
  what the case tree leaves. `n * (k + m)` (number first) never reaches the
  arm, since `as_nat(n)` fails on the `NatAdd`, and it unfolds as before.
- **`k = 0`.** Excluded (`!k.is_zero()`), so the case tree runs.
- **`N = 0`.** `from_view(0, Some(call))` is the call itself. By the
  definition, `0 + mul m 0` is `mul m 0` by R1. They agree.
- **`m` a variable, an unsolved meta, or a stuck call.** In each case the
  result is the same neutral the case tree gets stuck on. If a meta inside
  it is solved later, it is re-read exactly as the step-by-step value would
  be.
- **`m` a folded call.** The case tree unfolds a folded scrutinee
  (`Frame::Scrutinee`); `view_keeping` doesn't. That matters only if a
  folded call of type `Nat` can unfold to a number or a `Succ`, and none
  can: `folds_mul` unfolds to `x + (k-1)*x`, stuck on `x`; dictionaries and
  theorems aren't `Nat`; a `lift_leaf` definition is a neutral only once
  its tree is stuck on the lift. The stuck call keeps the original spine,
  so the values are identical here too. `add`'s existing shortcut
  (`NatAdd(k, folded)`) relies on the same invariant. If a new folding rule
  ever folds a `Nat`-valued call that can compute, it must revisit both.
- **Large `N`.** Correct, but see F2.

**Conversion.** The values are identical, so conversion can't accept or
reject anything differently, except through the budget. With large `k`, a
check that used to run out of steps now succeeds. That is the intended kind
of change, the same as every native.

## Head check first (`native::run`)

The head check forces a later argument only when an earlier one has a
number or `Succ` head. A `NatAdd` head fails `number_head`, so the check
stops at once on that argument. In each native's definition, a `Succ` (or a
number) in the first argument leads to the second argument's head being
forced anyway:

| Native | Where the second argument's head gets forced |
| --- | --- |
| `sub`, `leq`, `equal`, `decEq`, `equalSound` | their case trees match on it |
| `add` | R3/R4 |
| `mul` | `n + …`, through `add`'s native |
| `divFuel` | `leq divisor n`, evaluated as an argument of `divStep` |

So `run` itself forces nothing new. The cost is that each number argument
is forced twice. That is cheap for a `Call`, whose unfolding is kept, but a
solved meta's solution is applied again each time. This affects step counts
only.

## Findings

**F1 (medium; resources, not soundness): the `Mul` arm forces `n` when `m`
is plainly stuck.** `as_nat_with(g, n, force)` runs before anything looks
at `m`. For `x * t`, with `x` a variable, meta or stuck call (`k = 0`), the
old code returned `None` and the case tree got stuck on `x`. `t` was never
forced. Now `t` is forced, and walked if it is a chain of `Succ`s. While
checking, a non-native call `t` is a glued `Value::Call` whose unfolding is
lazy, so this computes work the definition never does. It can use up the
budget where none ran out before, which changes whether a program is
accepted. Expected input (from reading the code, not run):

```
def count: (n: Nat) → Nat
  | Zero => 0
  | Succ n => Succ (count n)
def f (x: Nat): Nat := x * count 100000000
theorem t (x: Nat): f x = x * count 100000000 := rfl
```

Before the change, `f x` is stuck at once on `x`. After it, `count 10^8`
is computed. Fix: before `as_nat_with(n)`, force `m` once. Unless its head
is a `NatAdd` or a `Succ` constructor, return `Ok(None)`. That is O(1),
keeps the linear behaviour, and forces `n` only where the definition would
(through `add`). Add the input above, or a step-count version of it, as a
regression test.

**F2 (low): `k * times` isn't charged to the budget.** The all-numbers path
charges `number_words` before multiplying. The shortcut multiplies two
bignums uncharged, and both can be huge: `k` comes from a `NatAdd` literal,
`times` from any number. Charge `number_words(Native::Mul, &[k, times])`
first. The `add`, `sub`, `leq` and `equal` shortcuts are linear, so this is
the first quadratic operation left uncharged.

**F3 (low; test strength): the agreement test compares with `conv`.** It
can't check the identity claim that read-back and hashes depend on. For
`Mul`, also assert that the folded read-back (or `quote`) of `fast` and
`slow` are equal. Add bases the test lacks:

- a stuck call (`f x`), not just a variable
- a folded `mul 3 x` base
- a mixed chain, `Succ (k + x)`
- a glued call
- for F1, an argument that must stay unforced (a `Call` whose forcing would
  be observable, or a step count)

`k1 = 0` and `k2 = 0` are covered, as are both shapes of `m`, a `Succ`
chain and a `NatAdd`.

**F4 (info; docs/core.md).** The new sentence is accurate. To be complete
as a rule, it should say:

- it applies only when the first argument isn't a number and has `k > 0`;
- `n = 0` gives `m * 0`;
- it is a native shortcut, switched off with the natives, unlike R3/R4;
- the residual `m * n` is the call the case tree would be stuck on, the
  same value, so read-back and hashes are unchanged.

The head-check change needs no kernel-spec text, since it changes no rule.

**F5 (info; worth a ticket).** The quadratic walk "took no steps":
`as_nat_with` and `view_with` walk `Succ` chains and force kept unfoldings
without charging the budget. That is why SW-2570 needed a wall-clock
deadline, and why the new resources test asserts on time (10 s, release
only). Charging one step per `Succ` walked, or per forced kept unfolding,
would let the step budget bound time again and allow a step-count test in
place of the timing one.

**F6 (info).** `a_batch_the_checker_cannot_finish_stops_at_the_deadline`
now relies on seed 1794200310 taking more than 1 s to check (about 4 s
now). A further speed-up would break it for the wrong reason. Consider a
batch that is slow by construction, or a smaller override.
