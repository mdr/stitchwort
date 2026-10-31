# Division on numbers with an unknown part

*SW-922 (D2077), 31 October 2026. A design note with a measured prototype.
Measured on `main` at `68d09151` (release build, M-series Mac, other lanes
running, so wall times are rough; user times are steadier). The prototype is
on branch `worktree-agent-aa5219c3981af5a43`, commit `bf47f1d3` (reverted by `ad6bcb34`, so the branch itself changes nothing);
it is not for merging as it stands (§9).*

*Status: D2080 (Matt): yes. Stage 1 (§8.1) built: `Nat.divStep`
(`std/core/Division.sw`), printed as `/` where it reads back
(`pretty.rs`), `Float`'s pins and the runtimes' natives re-pinned (nine of
them: `Nat.toText` and eight `Int` operations, which the prototype hadn't
noticed), `crates/driver/tests/pinned_hashes.rs` failing if any binding by
hash stops applying, `crates/driver/tests/division.rs`, and the R4
exclusions gone from the differential test. Stage 2 not started (D2081).*

Labels: **[measured]** I ran it; **[read]** I read it in the source named;
**[inferred]** my reasoning from measured or read facts; **[unverified]**
from memory, not confirmed, and not used to support a conclusion.

## Summary in plain words

- **The issue.** Since 29 October, `x + 12345` computes to "12345 steps of
  `Succ` around `x`" (rule R4). Division counts down its dividend one step at
  a time, so `(x + 12345) % D` with `x` unknown now takes 12345 steps, and
  each step leaves an undecided `if` with the next step inside it. Anything
  that writes the whole result out (printing, full normalisation, comparing
  two such terms the long way) builds a term that grows with the square of
  the constant.
- **The impact.** Four `Float.Theory` theorems and the `lcg` example can't
  be written out (over 4 GB), so the full-tier differential test skips them;
  one proof shape about `lcg` takes 30 s to check instead of 0.2 s (SW-920).
  Ordinary checking mostly avoids it.
- **The options.** (a) Change how division is defined. (b) Make R4 do less.
  (c) Make printing and normalisation lazier. (d) Make division a kernel
  primitive that never unfolds on unknowns.
- **What others do.** Agda and Rocq count down the dividend with a counter
  and no `if`, so on this case they stop after a small term; Lean uses the
  same fuel scheme as ours and hides it by marking division irreducible
  (forced open, it is worse than ours); Idris 2 uses our scheme too. Agda
  with *our* definition blows up exactly as we do: the definition is the
  cause, not the checker.
- **Recommendation.** (a), in its smallest form: one line of
  `Nat.divFuel` moves its comparison into a helper's first argument, so a
  step whose comparison is undecided stays one folded call. Measured: the
  term at K = 12345 is 132 characters instead of too large to show; the
  SW-920 proof drops from 29.8 s to 0.21 s; all 2,328 std, 1,363 AoC and
  190 rogue theorems still check, with two std lemma statements changed;
  the skipped differential cases pass again. Keep R4 as it is.

## 1. The problem, with evidence

`Nat.div n d` is `Nat.divFuel n n d`, and `Nat.mod n d` is `n - (n / d) *
d` (`crates/elab/src/std/core/Division.sw`) **[read]**:

```
def Nat.divFuel: Nat → Nat → Nat → Nat
  | Zero, n, divisor => 0
  | Succ fuel, n, divisor => if Nat.leq divisor n then Succ (Nat.divFuel fuel (n - divisor) divisor) else 0
```

R4 (SW-787, `crates/core/src/nat_add.rs` `stuck`) makes `m + k`, with `m`
stuck and `k` a number, compute to `k + m`: `k` `Succ`s around `m`
**[read]**. So in `(x * 3 + K) / D` the fuel is `K + x * 3`: the case tree
takes its `Succ` branch `K` times. Each time, `Nat.leq D (n)` is stuck on
`x * 3` (when `K < D`), so the `if` is stuck, and its `then` branch holds
the next step with a subtraction one longer than the last. Checking only
needs the head of a value (weak head normal form), which stops at the first
stuck `if`. Printing, full normalisation and structural comparison go into
both branches and build all `K` levels **[inferred]**, as the printed forms
show:

```
x => if 96 <= x * 3 then Succ (if 100 <= x * 3 - 96 then Succ (if 100 <= x * 3 - 96 - 100 then …
```

(that is `(x * 3 + 4) / 100`, `stitchwort eval` on `main`) **[measured]**.

Size of the normal form of `(x * 3 + K) / 2147483648` as `stitchwort eval`
prints it on `main`, and the wall time of the whole command **[measured]**:

| K | characters | time |
|---:|---:|---:|
| 0 | 37 | 0.6 s |
| 4 | 355 | 0.6 s |
| 16 | 2,497 | 0.6 s |
| 64 | 29,785 | 0.6 s |
| 256 | 438,457 | 0.6 s |
| 1,024 | 6,865,465 | 5.6 s |
| 2,048 | 27,362,361 | 41.7 s |
| 4,096 | `E-RESOURCE`, "a value was too large to show" | 1.2 s |

Size grows as K² (×4 from 1,024 to 2,048) **[measured]**. `%` gives the
same sizes (it contains the quotient) **[measured]**.

Where it bites (from SW-922 and commit 817c3ad7):

- std `Float.Theory`: `magUnits m` is `Nat.divFuel m m 2^52`, and four
  theorems (`magUnitsFieldNext`, `magUnitsWholeAt`, `magUnitsWhole`,
  `magUnitsCarry`) have types about `magUnits (e * 2^52 + 2^52 + …)`.
  Quoting such a type passes 4 GB; the reference evaluator's `conv`
  overflows its stack. They are left out of the differential test.
- `examples/accept/partial-handlers.sw`: `lcg seed = (seed * 1103515245 +
  12345) % 2^31`. Its normal forms pass 4 GB; two tests took about a minute
  each in conversion. Left out of the differential test.
- SW-920: `theorem t (seed: Nat): lcg seed < 2147483648 := Std.Nat.modLt (_
  * 1103515245 + 12345) 2147483648` takes **29.8 s user** (76.9 s wall
  under load) on `main` **[measured]**: the unifier descends into both
  sides' unfoldings (cause found by the SW-917 lane).
- SW-917 was the same unfolding through `rewrite` (fixed separately).

The same proofs written without the unknown inside the lemma's argument
check in 0.2 s on `main` (`lcgLt`, `lcgLt2`, and `rfl` between two
spellings of the dividend, `scratch kernel.sw` below) **[measured]**. So it
is the full-unfolding paths, not checking as such.

Before R4, `x * 3 + 12345` was a stuck call (`+` counted down its first
argument only), so `divFuel` had no fuel to take and stopped at once. That
these cases passed before 1ed90886 is **[inferred]** from that and from the
differential test passing before then; I did not rebuild the old commit. On
`main` today the same blow-up happens to anyone who writes the constant
first (`12345 + x * 3`), as it did before R4 (nat-add-recursion.md §10)
**[read]**.

## 2. How we work today

**Numbers.** `Nat` is `Zero | Succ Nat` and means exactly that; numbers are
stored as one big integer, and `k + x` with `x` unknown as `NatAdd(k, x)`
(`crates/core/src/native.rs`) **[read]**.

**Arithmetic.** In `core/Data.sw` **[read]**: `+` counts down its first
argument (R1, R2); `-` counts down both; `*` counts down its first
(`Succ m * n = n + m * n`); `Nat.leq` counts down both. In
`core/Division.sw`: `divFuel` above, `div`, and `mod = n - (n / d) * d`
(quotient on the left of `*` on purpose, so `*` doesn't unfold on it).

**Kernel rules R3 and R4** (SW-787): when `m + n` is stuck on `m`, the
evaluator looks at `n`: `m + 0 → m`, `m + Succ n → Succ (m + n)`, taken `k`
times at once for a number `k`. Both evaluators, natives on or off. They
exist because specs write `x + 1` far more than `1 + x` (273 to 20 in AoC,
161 to 4 in std), and before R4 `x + 1` was stuck: AoC days 4, 12, 15 and
24 needed `Nat.addComm` rewrites or worse programs, `Vec a (n + 1)`
indices were stuck (`E-INDEX-STUCK`), and std had an instance only because
`most + 1` was stuck (nat-add-recursion.md §1, §10) **[read]**. R4 is also
used with a large constant: `Float.Theory.keyHigh` proves
`Float.keyOf (m + 2^63) (Nat.leq 2^63 (m + 2^63)) = NegSucc m` by `rfl`
(`std/Float/Theory.sw` line 1077), which needs `Nat.leq 2^63 (m + 2^63)`
to compute **[read]**, and fails without R4 for constants that large
(§5 (b)) **[measured]**.

**Natives.** `Nat.add`, `sub`, `mul`, `leq`, `equal`, `divFuel`, `decEq`
and two proofs run natively when all their arguments are numbers
(`native.rs` `run_numbers`; `divFuel fuel n d` is `min(fuel, n / d)`), and
`add`, `sub`, `leq`, `equal` take shortcuts for `NatAdd(k, x)` (take the
shared `k` off in one step, `run_partial`) **[read]**. `divFuel` has no
shortcut for partly known numbers **[read]**. The runtimes (`crates/rt`
`prims.rs` `div_fuel`, the native backend `n1.rs`, JS `crates/js`) all
implement `Nat.divFuel` natively **[read]** (grep), so `Nat.div` costs one
machine division at run time.

**Who else knows about `divFuel`.** `omega` reads `Nat.divFuel x x k` as
`x / k` and uses `Std.Nat.divFuelLe` and `divFuelBound`
(`crates/elab/src/omega.rs`); the printer shows `divFuel n n d` as `n / d`
(`pretty.rs`); `decreasing.rs` keeps `n / 2` folded **[read]**. In std,
`divFuel` is named 18 times in `Nat/Arith.sw`, 53 in `Float/Theory.sw`, 9 in
`Float/Model.sw`, and a few elsewhere **[measured]** (grep).

**When the checker unfolds `divFuel`.** Weak head evaluation unfolds a call
whose case tree can take a branch: `divFuel` on fuel `Succ …` always can,
whatever `n` is; on a stuck fuel the call stays folded (`value.rs`
`stuck_tree`) **[read]**. Then the `if` (a call of `Bool.ifThenElse` with
two lambdas) is stuck on `Nat.leq`. Quote/normal form and the reference
`conv` go under the two lambdas; the machine's `conv` compares same-head
calls by arguments first and only unfolds when they differ **[inferred]**
from SW-917/920's analysis and the timings above.

## 3. Other systems

What each defines, and what it does on this case: an open dividend with a
constant exposed as successors (in Lean `x + K`, since its `+` counts down
the second argument; in Agda, Rocq and Idris `K + x`, since theirs count
down the first; `x + K` is simply stuck there, as in our pre-R4 world).

| system | definition of div / mod | native support | open dividend, constant exposed | source |
|---|---|---|---|---|
| **Stitchwort** (`main`) | fuel = dividend, `if` on `leq` per step | natives on numbers; runtimes native | K² term; 27 MB at K = 2,048; too large at 4,096; SW-920 proof 29.8 s | §1 **[measured]** |
| **Lean 4.34.1** | `Nat.div`: `go (succ x) x`, structural on fuel, `dite (y ≤ x)` per step — our scheme; `@[irreducible]`. `Nat.mod`: special cases `0 % m` and `n % (m+n+1)`, else `Nat.modCore` (fuel, `@[irreducible]`) | elaborator `whnf` computes `div`/`mod` on two literals with GMP (`Meta/WHNF.lean` `reduceNat?`); `@[extern]` at run time | default transparency: `/` stays folded (66 chars at K = 4); `%` unfolds to its `Decidable.rec`, 975 chars at K = 12345 (2.0 s). `transparency := all`: 89,369 chars at K = 4, 127,271 for `%`; K ≥ 16 hits `maxRecDepth` even at 200,000. Proofs (`Nat.mod_lt _`, transparent `lcg`, `rfl` between two spellings): 0.28 s for the file | **[read]** `Init/Prelude.lean` 2161–2295, `Init/Data/Nat/Div/Basic.lean` 1–62, `Lean/Meta/WHNF.lean` 1005–1050; **[measured]** `lean/Div.lean`, `lean/Kernel.lean` |
| **Agda 2.8.0** | `div-helper k m n j` and `mod-helper`: recursion on the dividend `n` with a countdown `j` and accumulator `k`, no `if`; `m / suc n = div-helper 0 n m n` (stdlib) | `BUILTIN NATDIVSUCAUX` / `NATMODSUCAUX`: helpers computed natively on literals | `(12345 + x*3) % 2^31` → `mod-helper 12345 2147483647 (x*3) 2147471302` (101 chars), at once; `(2^52 + x*3) / 2^31` passed 4 GB (it steps 2^52 times unary). With **our** `divFuel` transcribed: 975, 318,851, 18,519,798 chars at K = 4, 64, 256; K = 1,024 didn't finish (592 s for the run). `refl` proofs on both definitions: 0.5 s | **[read]** `Agda/Builtin/Nat.agda` (in full); **[measured]** `agda/Div.agda`, `agda/cmds.txt` |
| **Rocq 9.1.1** (unary `nat`) | `divmod x y q u`: recursion on the dividend with a countdown, no `if` (Agda's scheme); `div x (S y') = fst (divmod x y' 0 y')`; `modulo = y' - snd (divmod …)` | none in the kernel for `nat` [unverified: `vm_compute`/`native_compute` exist, not tried]; unary literals | `(5000 + x*3) / 1000` → `fst (Nat.divmod (x*3) 999 5 999)`, 0.015 s (`compute`), 9.7 s (`cbn`). `mod` writes `999 - snd …` as a 1,000-way match (size grows with the divisor) | **[read]** `Init/Nat.v` 47–63, 274–295; **[measured]** `rocq/Div.v` |
| **Rocq 9.1.1** (binary `N`) | `pos_div_eucl`: recursion on the dividend's bits, `if leb b r'` per bit | binary representation | `x*a + 12345` and the division stay folded under `cbn`. `12345 + x*a`: `Pos.add` with a known first argument splits on each bit of the unknown: 81,927 lines under `cbn`; `2^52 + x` passed 4 GB (2^52 bits' worth of carries) | **[read]** `BinNums/NatDef.v` 1–90, `PosDef.v` (`add`, `mul` signatures); **[measured]** `rocq/Bin.v` |
| **Idris 2 0.8.0** | `div' fuel centre right`: fuel = dividend, `if lte centre right` per step — our scheme (`divNatNZ left (S right) = div' left left right`) | Nat compiled to integers at run time | REPL normal form (`:set eval normalise`) of `divNatNZ (K + x*3) 1000`: one level, then stops (`if lte (mult x 3) 935 then 0 else S (div' (S…) …)`), 127/217/601 chars at K = 4/16/64. `Refl` between two spellings: fast for `div` at K ≤ 64, D = 1000; did not finish in 100 s for `mod` at K = 64, D = 2^31 (cause not isolated) | **[read]** `libs/base/Data/Nat.idr` and `libs/prelude/Prelude/Types.idr` at v0.8.0, through a fetch tool that quoted excerpts; **[measured]** `idris/Norm.idr`, `idris/Small.idr`, `idris/Proof2.idr` |

What this says **[inferred]**:

- The blow-up comes from the **shape of the definition**: fuel taken from
  the number, plus an undecided test whose branch holds the next step.
  Agda runs our definition into the same K² growth; Agda's own helper, on
  the same checker, stops after a constant-size term. Lean and Idris 2
  share our shape. Lean avoids it in practice by making `Nat.div` and
  `Nat.modCore` irreducible; forced open, it is worse than ours. Idris 2's
  normaliser stopped after one level in my runs; why is not established
  (perhaps it doesn't force `if`'s lazy branches **[unverified]**).
- A **counter scheme** (Agda, Rocq `nat`) gets stuck with a small term
  after K steps: each step is a plain tail call, nothing undecided. It
  still takes K steps, so a huge K (2^52) needs a shortcut that takes many
  steps at once; Agda has none for partly known numbers and ran out of
  memory.
- **Binary** representations (Rocq `N`) don't expose a constant as
  successors at all, but normalising `known + unknown` splits on the
  unknown's bits instead, which is its own blow-up. Not a fit for a
  language whose `Nat` is defined unary.
- Nobody **runs division natively on open arguments**; Lean's kernel
  accelerations apply to literals [the kernel's list is **[unverified]**;
  the elaborator's is read], and Agda's builtins to literal arguments.

## 4. Options

### (a) A division whose stuck step stays folded

**(a1) P1, the guarded step (prototyped).** Keep `divFuel`'s meaning and
signature; move the comparison into the first argument of a helper, so the
case tree itself is what gets stuck:

```
def Nat.divFuel: Nat → Nat → Nat → Nat
  | Zero, n, divisor => 0
  | Succ fuel, n, divisor => Nat.divStep (Nat.leq divisor n) fuel n divisor

@[noReceiver]
def Nat.divStep: Bool → Nat → Nat → Nat → Nat
  | False, fuel, n, divisor => 0
  | True, fuel, n, divisor => Succ (Nat.divFuel fuel (n - divisor) divisor)
```

A step whose comparison is undecided is now one folded call
`Nat.divStep (stuck) …`, as any case tree stuck on its argument is
(`stuck_tree`); there is no `if` with the next step inside. A decided
step still computes. `divFuel` keeps its native (same function, same
arity and type), and every `divStep True` step hands back to `divFuel`, so
natives re-engage at once on numbers. The runtimes need nothing: they run
`divFuel` natively. Two std lemma statements change (`Nat.divFuelLeStep`,
`Nat.divFuelBoundStep` said `if b then Succ (…) else 0`; now
`Nat.divStep b fuel n d`), their proofs unchanged.

**(a2) Agda's counter helper.** `Nat.div n (Succ m) = divHelper 0 m n m`,
recursion on the dividend with a countdown. Mentions the dividend once, so
it would also fix SW-554 (`a / 2` is `divFuel a a 2`, two copies of `a`,
×4 per halving in `Random.xorBits`). Prototyped only as a user definition
(`scratch helper.sw`): `(x * 3 + 12345) / 2^31` → `divHelper 0 2147483647
(x * 3) 2147471302` (60 chars), six halvings 126 chars and linear; but
`(x * 3 + 2^52) / 2^31` didn't finish in 120 s (2^52 unary steps), so it
needs a new native with a many-steps shortcut **[measured]**. Cost
**[inferred]**: a new native in the kernel and all three runtimes (or
`Nat.div` keeps calling `divFuel` at run time, two definitions to keep in
step), `omega`'s recognition and facts, the printer, and the 80-odd std
uses (`Nat/Arith`, `Float/Model`, `Float/Theory`) re-proved against the
new definition.

### (b) Narrow R4

Prototype (env `SW922_R4_MAX`): R4 only for constants up to a limit, above
it the sum stays stuck. With the limit at 64 and `main`'s std
**[measured]**: the SW-920 repro checks in 0.13 s; AoC (1,363) and rogue
(190) pass; std **fails**: `Float.Theory.keyHigh` (`rfl` needs R4 with
2^63, §2), and `Float.neg`/`Float.sub` elaborate to different terms, so
their pinned hashes no longer match. Any limit is arbitrary: the blow-up is
K² for every K (64 already gives 30 kB), and the real uses need R4 for any
K. "Don't commute when the sum feeds fuel" is not something the evaluator
can see locally **[inferred]**. Conversion would also lose `x + 100 =
Succ (x + 99)`, which the rules promise (nat-add-recursion.md §9)
**[inferred]**.

### (c) Lazier unfolding, or a cap, in normalisation and printing

Keep a call folded when its unfolding gets stuck below the top (Rocq's
`cbn` refolding; Lean's "smart unfolding" **[unverified]** in detail), or
stop normalising under an undecided `if` past a depth. Related:
`docs/proposals/folded-calls.md` (SW-251). It would need glued values (the
folded call kept beside its unfolding) in quote and in the reference
evaluator, would change normal forms of every definition with an `if` in
its body (hashes, snapshots), and would not by itself fix the unifier path
(SW-920), which walks values, not printed terms **[inferred]**. A cap
already exists ("too large to show"). Not prototyped: (a1) is this idea
applied to the one definition that needs it, by its shape alone.

### (d) A kernel primitive that never unfolds on unknowns

Lean's route: division irreducible to the checker, computed natively on
numbers, reasoned about through lemmas. It removes the unfolding everywhere
but also every proof that unfolds division: the std lemmas behind
`modLess`, `divMulLe` and `omega`'s facts, and `Float.Theory`'s proofs
about `magUnits` **[inferred]**. Lean's own numbers above show it only
hides the shape: forced, it is bigger than ours. Not prototyped.

## 5. Measurements of the options

`main` against P1 (option a1) and option (b) at 64. User seconds; wall
times were 1.5–3× under other lanes' load **[measured]**.

| check | `main` | P1 | (b), limit 64 |
|---|---:|---:|---:|
| normal form `(x*3+12345) % 2^31` | too large to show | 132 chars, 0.7 s | (stuck sum, as before R4) |
| normal form `(x*3+2^52) % 2^31` | too large | `E-RESOURCE`, recursion depth (2^21 decided steps, §9) | – |
| SW-920 repro (`sw920.sw`) | 29.8 s | 0.21 s | 0.13 s |
| `lcgLt`, transparent `lcg`, `rfl` spellings (`kernel.sw`) | 0.19 s | 0.22 s | – |
| `audit Std --no-search` (2,328 theorems) | all pass, 5.3–5.6 s | all pass, 5.6–6.1 s | `Float.Theory` fails |
| `aoc check --no-cache` (135 namespaces) | 43.0 s | 43.1 s | 46.5 s |
| `aoc audit --no-search` (1,363) | all pass, 44.3 s | all pass, 43.9 s | all pass, 42.5 s |
| rogue check / audit (190) | 4.5 s / all pass | 4.5 s / all pass | 3.9 s / all pass |
| differential test, `partial-handlers` and `float-playlist` with the R4 exclusions removed (full tier) | killed at 15.6 GB (817c3ad7) | **passes**, 26.9 s with the prelude | – |
| merge tier (911 tests) | – | 906 pass; 5 snapshot tests change (below) | – |

The merge tier's five failures under P1 **[measured]**: three are hash
snapshots (`hash_stability` prelude, examples, projects), expected when
`divFuel`'s hash changes. The other two have one cause: the runtimes bind
their text natives by content hash (`crates/rt/src/natives.rs`
`TEXT_NATIVES`, "A native is only used for a definition with exactly that
hash"), and `Nat.toText` depends on `divFuel`, so its native silently
stopped being used: the JS extraction snapshot (`extract
generated_code_is_stable`) now writes out `Nat.digitsOnto` with `Nat.div`
calls where it had `(n) => n.toString()`, and the runtime allocation trace
(`alloc_trace a_mapped_list_is_reused_in_place_and_freed`, which prints
`0,1,2`) has 18 allocations instead of 12 **[measured]**; that the extra
allocations are the digit loop is **[inferred]**. Stage 1 must re-pin those
hashes like `Float`'s; nothing here is a wrong answer.

P1's normal form at K = 4, 1,024, 12,345: 120, 129, 132 characters; on
`main` 355, 6.9 M, too large **[measured]**. P1 prints
`12345 + (x * 3) - (Nat.divStep (2147471303 <= x * 3) (12344 + (x * 3))
(12345 + (x * 3)) 2147483648 * 2147483648)`; the printer should show the
`divStep` as `(12345 + x * 3) / 2147483648` (stage 1).

## 6. Soundness and the kernel

- **P1** changes a library definition, not the kernel. `Nat.divFuel` computes
  the same function (same equations on `Zero` and `Succ` fuel, with
  `divStep` unfolded), so its native stays exact: the natives tests compare
  natives with definitions and would catch a difference **[inferred]**.
  Mutual recursion is checked by the termination checker as usual (fuel
  decreases through `divStep`). Hashes of `divFuel` and everything above it
  change (including the pinned `Float` natives, re-pinned mechanically;
  Matt: hashes don't matter, re-pin).
- **(a2)** adds a native: trusted base grows by one function and its
  shortcut (DESIGN.md §13).
- **(b)** weakens the evaluator relative to the rewrite relation of
  nat-add-recursion.md §9: still sound, less complete.
- **(c)** changes quote and conversion strategy in both evaluators.
- **(d)** makes division opaque to the checker: a new kind of builtin.

## 7. Recommendation

(a1) now. It is a two-definition change that removes the blow-up at its
cause (an undecided step with the next step inside it), costs nothing
measurable on std, AoC or rogue, needs no kernel or runtime change, and
fixes SW-920's 30 s case as a side effect. It matches what the comparison
shows works (Agda's and Rocq's steps get stuck cleanly) while keeping our
natives, our lemmas and `omega` as they are. Keep R4: it is what
SW-787 was for, and std uses it with constants up to 2^63.

Not now: (a2) (SW-554's duplication is real but has a different cause, and
(a2) is much more work); (c) and (d) (large changes whose benefit here
(a1) already gets).

## 8. Plan

1. **Stage 1 (one lane, Sonnet or Opus).** P1 as prototyped; `pretty.rs`
   prints `Nat.divStep (Nat.leq d n) f n d` (with `f + 1 = n`) as `n / d`;
   re-pin `Float`'s native hashes (`crates/core/src/float.rs`, the test
   prints them) and the runtimes' text natives that depend on division
   (`crates/rt/src/natives.rs` `TEXT_NATIVES`: at least `Nat.toText`), then
   check the JS and allocation-trace snapshots go back to what they were; remove the R4 entries from `differential.rs`'s three lists
   and check the full-tier differential run on the two examples; take
   `lcg`/`Dice.upTo` out of `opaque` in the roguelike if Matt wants (they
   were made opaque for this, nat-add-recursion.md §10); re-measure SW-920
   (it may close as a duplicate; the unifier lane's `identical` fix stays
   useful). Lane tier, then merge tier, `task audit`, snapshots re-pinned.
2. **Stage 2 (only if a case needs it).** A `run_partial` shortcut for
   `divFuel fuel (K + t) d` with `d ≤ K` that takes `⌊K/d⌋` decided steps
   at once. It needs a new native outcome ("`q` `Succ`s around a call to
   continue with"), since today's `Again` can't put `Succ`s on top. No
   measured case needs it: `magUnits` takes one decided step (2^52 against
   2^52) and then stops **[inferred]**, and its differential cases pass
   under P1 **[measured]**.
3. **SW-554** stays in the backlog with (a2) as its candidate fix, decided
   on its own evidence.

## 9. Limits of the prototype

- Built with the `Float` pins switched off by an environment variable
  (`SW922_NO_FLOAT_PIN`) instead of re-pinned; `differential.rs` has a
  prototype filter (`SW922_ONLY`) and the R4 entries removed; `nat_add.rs`
  has option (b)'s limit (`SW922_R4_MAX`). All marked `PROTOTYPE (SW-922)`.
- A decided step still costs one step: `(x*3 + 2^52) / 2^31` takes 2^21
  decided steps and runs out of recursion depth under P1, as it ran out of
  size on `main` (stage 2).
- P1 does not change SW-554: `a / 2` still mentions `a` twice.
- Timings ran beside other lanes; the user-time comparisons are within
  noise of each other.

## 10. Decisions for Matt

- **D2080: adopt P1 as stage 1 (§8.1), and keep R4 unchanged?** [rec: yes]
  Assumptions: that `Nat.divFuel`'s exact unfolding shape (`if … then Succ
  … else 0`) is not something users' proofs depend on outside std (AoC and
  rogue passed unchanged, but other projects were not checked); that
  changing hashes of `Nat.div`, `Nat.mod` and everything using them is
  acceptable (Matt said so for SW-787); and that printing `divStep` as `/`
  is enough for readable goals.
- **D2081: stage 2's many-steps shortcut: build it now, or only when a
  measured case needs it?** [rec: only when needed] Assumption: that no
  current std, AoC or rogue proof divides an open number with a known part
  much larger than the divisor (none failed or slowed under P1).
- **D2082: SW-554 (the dividend written twice): leave in the backlog with
  Agda's helper (a2) as its candidate fix?** [rec: yes] Assumption: that
  `Random.xorBits`'s large normal forms only affect the differential test
  and printing, not proofs anyone is writing (true of the tickets I read,
  not checked further).

## 11. Sources

Read in full (1): Agda 2.8.0 `lib/prim/Agda/Builtin/Nat.agda`.

Read in part (8): Lean 4.34.1 `src/lean/Init/Prelude.lean` lines 2150–2300
(`Nat.div`, `Nat.modCore`, `Nat.mod`, `Nat.mod_lt`); `Init/Data/Nat/Div/Basic.lean`
lines 1–62; `Lean/Meta/WHNF.lean` lines 1005–1050 (`reduceNat?`). Rocq
9.1.1 `theories/Init/Nat.v` (`add`, `mul`, `divmod`, `div`, `modulo`);
`theories/BinNums/NatDef.v` lines 1–120; `theories/BinNums/PosDef.v`
(declaration list). Idris 2 v0.8.0 `libs/base/Data/Nat.idr` (`divNatNZ`,
`modNatNZ`, `div'`, `mod'`, `lte`, `Integral Nat`) and
`libs/prelude/Prelude/Types.idr` (`plus`, `minus`, `mult`, `compareNat`),
both through a web fetch tool that returned quoted excerpts, not the files.

Repository (read in part): `docs/proposals/nat-add-recursion.md` (§1,
§9.1, §10), `crates/core/src/native.rs`, `nat_add.rs`, `float.rs`,
`registry.rs`, `crates/driver/tests/differential.rs`, `std/core/Data.sw`,
`std/core/Division.sw`, `std/Nat/Arith.sw`, `std/Float/Theory.sw`; tickets
SW-922, SW-787, SW-554, SW-920, SW-917.

Not read, so supporting nothing here: Lean's kernel source (its list of
GMP-accelerated `Nat` operations), the Lean reference manual on
irreducibility and smart unfolding, Rocq's reference manual on `cbn`, Idris
2's evaluator source, F* and Isabelle/HOL (not covered).

Scratch files (not committed; under the session scratchpad `div/`):
`sweep.sh`, `kernel.sw`, `sw920.sw`, `helper.sw`, `lean/Div.lean`,
`lean/Kernel.lean`, `agda/Div.agda`, `agda/cmds.txt`, `rocq/Div.v`,
`rocq/Bin.v`, `idris/*.idr`. Their contents are summarised in §1 and §3;
the important ones are reproduced in the appendix.

## Appendix: the repros

Our size sweep (`sweep.sh`): `def f (x: Nat): Nat := (x * 3 + K) / 2147483648`,
then `stitchwort eval --no-cache k.sw '(x: Nat) => f x' | wc -c`.

SW-920 (`sw920.sw`):

```
def lcg (seed: Nat): Nat := (seed * 1103515245 + 12345) % 2147483648
theorem t (seed: Nat): lcg seed < 2147483648 := Std.Nat.modLt (_ * 1103515245 + 12345) 2147483648
```

Lean (`lean/Div.lean`): a command running `Meta.reduce` under
`withTransparency` on `fun x : Nat => (x * 3 + K) / 2147483648` and
printing the length. Agda (`agda/Div.agda`, via `--interaction-json` and
`Cmd_compute_toplevel`): `_/_` and `_%_` as the standard library defines
them from the builtin helpers, and `divF n d = divFuel n n d` transcribing
ours. Rocq: `Eval compute`/`cbn`/`lazy` on `Nat.div (5000 + x * 3) 1000`,
and on `N` with `Pos.add`/`Pos.mul` and `N.pos_div_eucl`. Idris 2:
`:set eval normalise` then `\x => divNatNZ (K + x * 3) 1000 ItIsSucc`.
