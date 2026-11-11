# SW-2874 review: G2 reads a stuck sum in `+`'s second argument

Fable paper review (D3473) of commit 66a8ef630 on `lane/SW-2874`, 11 Nov 2026.
Read-only: no builds or tests were run. Costs and step-count effects below
are reasoned from the code and marked "unmeasured" where a run should
confirm them. Line numbers are the lane branch's.

The change: `nat_add::reread` (`crates/core/src/nat_add.rs:128-182`) now
recurses when the base of `+`'s second argument is itself a stuck sum
(`:168-174`), checks each level against the operation's stack (`:154`), and
leaves a folded `k * x` alone (`:163-167`).

## Verdicts

| # | Verdict | Finding |
|---|---|---|
| 1 | OK | Sound: every new conversion is an equality by unfolding, R3 and R4; distinct values are still told apart |
| 2 | OK | The machine, the reference evaluator and the unifier agree: all three get the change through the one shared function |
| 3a | OK | Termination: the lane's argument is complete |
| 3b | OK | The `k * x` exemption is sound and loses nothing; it never changes an answer the old code gave |
| 3c | SHOULD-FIX (follow-up ticket, measure first) | A long right-nested chain is now walked to the bottom at every comparison level: quadratic, and for a chain with no folded call the walk costs no steps at all |
| 3d | NOTE | A folded call other than `k * x` that unfolds to a long chain: E-RESOURCE past the stack's depth where the old code answered after one unfold |
| 4a | OK | Results don't depend on evaluation order; hashes are untouched |
| 4b | NOTE | "Step counts unchanged" is not exactly true: steps go down for `m + k * x`, visits go up for every stuck sum read |
| 4c | NOTE | The new stack check makes "answer or E-RESOURCE" depend on frame size (build profile) for deep chains, as `same_spines` already does |
| 5a | OK | `docs/core.md` rule E and the G2 row say what the code does |
| 5b | SHOULD-FIX | `nat_add.rs`'s module comment (`:34-38`) is stale and now contradicts the function below it |
| 6 | SHOULD-FIX | Tests miss: a rejection, the `k * x` exemption, a long chain, a number `match` |
| 7 | NOTE | The error reads "the program is nested too deeply for the conversion" |

No MUST-FIX. The change can merge; 5b and 6 are small and could go in the
same lane, 3c is a ticket.

## 1. Soundness (OK)

`reread_with` returns a value only by these steps, each an equality that
holds for all values of the free variables:

- `unfold(&base)` (`:168`): the evaluator's own unfolding of a folded call,
  definitional unfolding of a total function.
- `reread_with(&base)` (`:170`): equal to `base` by induction on the
  recursion.
- `from_view(k, Some(next))` (`:175`): puts back the `k` `Succ`s that
  `view_with` took off `n`, around the replaced base. The recursion is given
  the base under `n`'s `Succ`s and its result goes back under the same `k`,
  so each level reads the right thing.
- `stuck_value(g, id, m, &n, force)` (`:181`): R4 `k` times and then R3 or
  nothing, as before the change.

`None` is returned whenever the sum's head stays stuck, even if something
below was unfolded on the way (`x + (y + f 1 y)` with `f 1 y` reading to
`y`): the caller then keeps the original value, which is the same as before
the change, and nothing is claimed.

Telling values apart is unchanged, since the number comparison is the same
code. `x + (y + two 0)` reads to `2 + (x + y)`; `x + y + 3` evaluates to
`3 + (x + y)`; `native::compare` takes off the two shared `Succ`s and hands
`x + y` against `1 + (x + y)` to `assign` (`value.rs:3643-3655`), where
`unfold_folded` and `reread` both give `None`, so the answer is "different".
The `Int` route compares the same `Nat` fields under the `Int` constructors.

With unknowns (the unifier): `x + (?m + two 0)` reads to `2 + (x + ?m)`,
which holds whatever `?m` turns out to be, since R4 is an equation for all
`m`. A stuck sum whose first argument is an unknown solved since the value
was built is read the same way and is still equal once forced.

## 2. The three callers agree (OK)

All of them call the one function, so the recursion and the exemption can't
differ between them:

- Machine: `reread_sum` (`value.rs:2325`), used by `branch` for a `case`
  (`:2303`) and a `NumCase` (`:2247`), and by `conv_step` at the top
  (`:3621-3629`) and in the number comparison's `assign` (`:3643-3648`).
- Reference: `reread_sum` (`reference.rs:560`), used by `scrutinee` (`:552`),
  `number_view` (`:586`) and `conv_in` (`:842`, `:845`, `:860`).
- Unifier: `unify.rs:1362`, at the top (`:1363-1370`) and in `assign`
  (`:1396`).

Points I checked for a split:

- `reference::scrutinee` rereads once where the machine's `branch` loops.
  One call is enough: `reread_with` loops inside until nothing more reads,
  and when it returns `m` itself (`n` read to 0), `m` is the first argument
  `add`'s own case tree was stuck on, which had already been reread.
- The exemption uses `native::folds_mul`, not the reference's plain-aware
  `folds_mul` (`reference.rs:155`). In plain mode `k * x` is never left
  folded, so the test never fires on a value the plain evaluator built. On
  one handed over from the machine, the unfold closure gives `None`
  (`is_folded` is false) and the recursion gives `None` (not a sum), so the
  loop breaks with or without the exemption.
- Machine and reference pass different `unfold` closures, as before the
  change; the recursion passes the same closure down, so no level mixes them.
- The unifier only gains equalities the kernel gains too (same function, and
  the kernel has no unknowns), so it can't accept what the kernel rejects.

## 3. Termination, bounds and cost

**3a (OK).** The loop continues only after `unfold` returned `Some` or a
nested call did. A nested call returns `Some` only with `unfolded` set, so
by induction every `Some` contains at least one successful `unfold`, and
each of those runs the machine (`value.rs:1353`, a step per transition) or
`eval_tree` under the budget. So continuing iterations are bounded by the
operation's work. A nested call that returns `None` without unfolding goes
down a proper part of a finite value. Each level of Rust recursion is
checked against the stack floor by `budget.nesting` (`budget.rs:687-700`),
which also fails once the operation has run out. Outside an operation
`work_limit` starts at `u64::MAX` and the floor at 0, so `nesting` passes.

**3b (OK).** The exemption only ever makes `reread` do less, and answering
"stuck" is always sound: the comparison goes on to compare the two sums by
their parts, where `k * x` against anything else is still unfolded by the
folded-call rule (`value.rs:3605-3617`). It's complete because `folds_mul`
(`native.rs:634`) requires `k > 0` and a second argument headed by a
variable: the full reading of `k * x` is `x + (x + … + x)`, rigid, never
`Zero` or a `Succ`. It also never changes an old answer: before the change
`m + k * x` unfolded once to `x + (k - 1) * x` (or to `x` for `k = 1`),
found nothing more, and returned `None`. The test is made on every loop
iteration, so a `k * x` reached by unfolding something else is caught too.

**3c (SHOULD-FIX, as a follow-up ticket; unmeasured).** Before, `reread` on
a sum whose second argument was a plain stuck sum cost O(1). Now it walks
the right spine to the bottom, and `conv_step` calls it again on each
sub-sum as it compares the two spines part by part (`Nat.add` is recursive,
so two stuck sums are compared by their arguments). Two effects:

- A chain with no folded call in it, `x + (x + (… + x))` of depth D:
  D²/2 levels of walking per side, none of which is a budget step (only
  `nesting`, which counts visits). Hand-written sums are a few deep and
  cost nothing. Computed ones are not: a structurally recursive `rep k x =
  x + rep (k - 1) x` at a numeral, or `List.sum` of a replicated variable,
  evaluates to a chain of depth `k`. At D = 10,000 that's about 10⁸ level
  visits per comparison that the step count doesn't show, where it was
  20,000. The plain evaluator meets this for every `k * x`, which it never
  folds.
- A `decreasing` `f (Succ m) y = y + f m y` at a numeral K: each level
  unfolds the rest of the chain again, K²/2 unfolds where it was K. These
  are steps, so the budget sees them.

Options, cheapest first: charge `budget.step()` on each recursive level
(not the top one, so flat sums' counts don't move), which at least puts the
cost in the deterministic counts; or make the walk iterative and have the
comparison skip `reread` on a sub-sum whose parent's walk already found
nothing to read. Measure a depth-10,000 chain first; if it's milliseconds,
close the ticket.

**3d (NOTE).** For that `decreasing` `f` at a K deeper than the stack
allows, `x + f K y` against an equal `x' + f K y'` is now E-RESOURCE where
the old code stopped after one unfold and the folded-call rule found the
arguments equal. The stack guard makes it an error and not a crash.
`k * x` was the only instance in std (Float.Theory); a user's would need a
numeral in the hundreds of thousands. Not worth a rule of its own.

## 4. Determinism

**4a (OK).** `reread` is a function of the value and the unknowns' solutions
only; nothing depends on the order values are met in. No `step()` was added.
Content hashes are of terms, which conversion's work doesn't touch. Elaborated
terms can change only where a unification that failed now succeeds, which
needs a nested sum over a folded call.

**4b (NOTE).** Two counters do move, so the verifier should expect it:

- Steps go down where a comparison or `case` reads `m + k * x`: the old
  loop unfolded `k * x` once before finding nothing, and the exemption now
  skips that unfold. Float.Theory and anything with `ring`-shaped goals.
- Steps go up where a nested sum has a folded call below it (the new
  unfolds), which is the case being fixed.
- `total_visits` goes up by one for every stuck sum read and each level
  below it (`nesting` at `:154` is also on the top-level call).
  `bench/baseline.toml` records visits with a tolerance.

**4c (NOTE).** `nesting` compares the stack position with the operation's
floor, so the depth at which a chain becomes E-RESOURCE depends on frame
size, larger in a debug build. It's never a different answer, only no
answer, which is the budget's contract (`budget.rs:314-325`), and
`same_spines` already recurses under the same guard. An iterative walk
(3c) would remove it.

## 5. Docs

**5a (OK).** Rule E's new sentences (`docs/core.md:322`) and the G2 row
(`:354`) match the code. "Its head is never `Zero` or a `Succ`" is right
for the reason in 3b.

**5b (SHOULD-FIX).** `nat_add.rs:34-38` still says that looking at the
second argument "does not unfold a call left folded by name. The only such
call of type `Nat` is `k * x` … so nothing is missed". That's true of
evaluation (`stuck`) but false as a statement about folded calls since
SW-2260: every `decreasing` definition is folded, which is why `reread`
exists. Say that evaluation leaves them, and that comparisons and
eliminations read them with `reread`. Also `reread_with`'s doc (`:137-140`)
says the recursion is "on a proper part of `value`"; add that the walk goes
to the bottom of a right-nested chain, with the `k * x` exemption as the
one cut.

## 6. Tests (SHOULD-FIX)

What's there is right: the two matrix contexts run every kernel mode and
the plain evaluator, and the probe goes through the unifier and the kernel
for `Nat`, a `case` and `Int`. Missing, each a few lines in the probe file
or beside it:

- A rejection: `x + (y + two 0) = x + y + 3 := rfl` is a type error, not
  accepted and not E-RESOURCE.
- The exemption: `x + (y + 9007199254740992 * z) = x + (y + 9007199254740992 * z)`
  built two ways (so the values aren't shared) checks quickly. This is the
  Float.Theory regression, which nothing in this lane's tests would catch.
- A chain: a `decreasing` `f (Succ m) y = y + f m y` with `x + f 200 y`
  against `x + f 200 y` and against something different: an answer in
  both, within a stated step count.
- A number `match` with numeral arms (`match x + (y + two 0) with | 0 => … |
  1 => … | _ => …`), for the `NumCase` path (`value.rs:2247`,
  `reference.rs:586`); `isPos` matches on `Zero` and `Succ`.

## 7. Other

**NOTE.** The stack error is `ResourceError::Nesting("conversion")`, shown
as "the program is nested too deeply for the conversion". The program
needn't be nested: the chain can come from unfolding. `Depth` ("it recursed
more deeply than allowed") is what `step()` gives for the same condition in
`same_spines`. It's also raised from a `case` and from the unifier under
the same label. Wording only.
