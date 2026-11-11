# SW-2253 review: omega reads through folded calls

Opus paper review (D2364) of commit 697ac5cfe on `lane/SW-2253`, 11 Nov 2026.
Read-only: no builds or tests were run, so the findings marked "probe" are
reasoned from the code and need a run to confirm.

The change: `Quoter::quote` and `Quoter::quote_int` (`crates/elab/src/omega.rs:2133`,
`:2236`) call `stitchwort_core::value::unfold_folded` (`crates/core/src/value.rs:2770`)
before the `recomputed` fallback, so `two 0` is quoted as `NLit 2` and not as
an atom.

## Verdicts

| # | Verdict | Finding |
|---|---|---|
| 1a | OK | The final check for the example's shapes rests on conversion's folded-call rule and G2 only |
| 1b | MUST-FIX (probe first) | Nested sum `x + (y + two 0)`: `nat_add::reread` doesn't reread an inner stuck sum, so the kernel check probably fails where the old atom made it syntactic |
| 2 | SHOULD-FIX | `unfold_folded` runs to the declaration's budget, with no attempt cap, on every folded call in every arithmetic fact in scope; exhaustion is a sticky E-RESOURCE |
| 3 | SHOULD-FIX | The snapshot churn comes from calls stuck on variables now being atomised as their unfolding: no gain, worse messages, and new reliance on conversion |
| 4 | OK | The example's five statements say what they claim |
| 5a | SHOULD-FIX | Module doc's "Quoting" section doesn't mention folded calls |
| 5b | NOTE | Tests missing: nested sum, a call stuck on a variable, a large folded call in an unrelated fact |

## 1. The final check

The proof is `Std.Omega.prove env facts goal cert rfl proofs`, whose type is
the denotation of the quoted goal; the elaborator and kernel convert it to
the goal as written. Before the change `two 0` was atom `a` with `env[a] :=
two 0`, so the denotation was the goal syntactically. Now the denotation has
`2` where the goal has `two 0`, so the check relies on conversion.

**1a (OK).** For each shape the example covers, conversion is guaranteed by
rules that don't depend on a cap:

- `two 0` against `2` as an argument (`h: x = two 0`, `two 0 + x`, `Nat.leq x
  (two 0)` stuck on `x`, `OfNat (two 0)`): the folded-call rule (`unify.rs:1353`
  and its `conv` twin, `value.rs:3612`) unfolds the call. This rule predates
  SW-2260.
- `x + two 0` against `Succ (Succ x)`: G2, `nat_add::reread` (`nat_add.rs:126`,
  called from `value.rs:2326` and `unify.rs:1362`).
- `Nat.sub`, `max`, `min`, `/`, `%` with a folded argument: their case trees
  scrutinise the argument, and the machine unfolds a folded call it takes apart,
  so no stuck form keeps `two 0`. Only `+` keeps it stuck (R3/R4 read `n` with
  `force` only), which is why G2 was needed.
- `x * two 0`: `native::view` doesn't unfold, so it's still a product atom of
  the raw value, as before.

None of these conversions is under a scoped attempt: they run within the
declaration's operation budget, and they recompute what omega computed, so
the kernel's extra cost is about the cost of omega's unfolding. With an
attempt cap on omega's side (finding 2) that's bounded by the cap; without
one, a call that just fit in the budget for omega can push the check over.

**1b (MUST-FIX, probe first).** `reread` (`nat_add.rs:126-155`) peels the
`Succ`s off `n` and unfolds `n`'s head only if it's a folded call. When `n`
is itself a stuck sum with a folded second argument, it stops:

```text
theorem nested (x: Nat) (y: Nat): x + (y + two 0) = x + y + 2 := omega
```

omega now quotes the left side as `NAdd x (NAdd y (NLit 2))`, which denotes
`x + (y + 2)` and computes to `Succ (Succ (x + y))` (R4 twice). The goal's
`y + two 0` is stuck (evaluation reads `two 0` with `force` only), so `x + (y +
two 0)` is stuck on a second argument that is a stuck sum, not a folded call.
`reread` on it: `view_with` gives base `y + two 0`, `unfold_folded` of a
`Nat.add` call is `None`, so `unfolded` stays false and it returns `None`. The
number comparison then has `2 + (x + y)` against `0 + (x + (y + two 0))`, and
I see no path that reads the inner sum again. So conversion says no, and an
`omega` that checked before (atom `two 0`, syntactic denotation) now gives a
type error. The same shape arises under `Int`: `OfNat (x + (y + two 0))`.

docs/core.md's rule E says R3 and R4 read the head of `+`'s second argument
where a comparison reads a stuck sum. The head of `y + two 0` under that rule
is `Succ`, so by the spec these terms are equal and `reread` is incomplete:
a G2 gap, not omega's. Two fixes:

- In `reread`, when `n`'s base is a stuck `Nat.add`, reread it recursively
  (then rule E holds for nested sums in every mode). This is core, so Opus,
  with a `proof_equivalence` case and a core.md gaps-table line.
- Or, in omega, keep the folded call as the atom whenever its unfolding
  would sit under a stuck sum's second argument. This is narrower and leaves
  the conv gap in place.

I'd do the first, and make this lane wait for it, as step 1 waited for
SW-2260. Probe first: if the theorem above checks, downgrade to NOTE.

## 2. Cost of `unfold_folded`

`unfold_folded` runs the call's case tree in the global machine and loops
while the result is another folded call (`value.rs:2770-2820`); omega then
forces the result and `native::view` walks it. For a call with concrete
arguments, that's the call's whole value: `fib 30` or `ack 3 5` in a
`decreasing` definition is computed in full. Nothing caps it below the
declaration's operation budget: unlike `Quoter::atom`'s conversions
(`omega.rs:2438`, `:2460`), the new calls aren't inside `budget.attempt`.

What makes this worse than conversion's own unfolding:

- omega quotes every arithmetic fact in scope, not just the goal, so an
  unrelated `h: r = slowFn 40` in context is now computed by every `omega`
  below it, including the speculative ones: `prove_case` (`cases.rs`),
  `prove_for_auto` and `prove_premise` (`rewrite` side conditions, `decreasing`
  obligations).
- A `Work`, `Depth` or `Deadline` error is E-RESOURCE, which `undo::fatal`
  passes through those speculative callers (`omega.rs:303`, `:327`) and which
  is sticky for the operation. So a declaration whose `omega` used to succeed
  (treating `slowFn 40` as an atom it never needed) can now fail with "ran out
  of resources", and so can one where `auto` merely tried `omega`.

This is the same class as SW-2843 (zonk reading back fully unfolded whenever
it meets an unknown): deep computation in a place that only wants a shape.
Fix: run the unfolding as an attempt with a small work cap, as `atom` does
(something like `work: 20_000`, `size: 10_000`, frames as there), and treat
`Work` or `Size` running out as "keep the folded call as an atom". Pass
`Depth`, `Deadline` and `Cancelled` on, as the attempt contract
(`budget.rs:314-325`) requires. The cap also bounds the kernel's recomputation
in finding 1a.

## 3. The two changed snapshots

`decreasing-lex` (`ackAbove` and its helpers) and `decreasing-match-fact`
(`drain`, `drainBelow`, `drainLet`, their `unfold`/`eq`/`induct` and the
theorems over them) changed hash. The ticket note says "omega proofs inside
decreasing obligations now read folded calls". That's expected from the
code, but not for a good reason:

- Every `decreasing` definition is marked folded (`decreasing.rs:1195`), as
  are definitions with a `Quot.lift` leaf. In these examples the calls omega
  meets (`ack k 1`, `ack (Succ k) j`, the `Set.size` measures) have variable
  arguments, so the unfolding never reaches a number: `unfold_folded` returns
  the glued `%go` call (or the next stuck form), not `None`, because its stuck
  test (`value.rs:2788`) only catches a result that is the same call again.
  omega forces it and makes an atom of the fuelled internal form instead of
  the call.
- So nothing new is proved here; the atoms are just different terms. The
  check now goes through conversion (`ack k 1` against `ack.%go …`), which
  costs a recomputation, and an omega failure message names atoms with
  `cx.show(&atom.value)` (`omega.rs:3553`), so it would show the `%go`
  internals (or a stuck lift) where the user wrote `ack k 1`. I haven't seen
  such a message, since I ran nothing, but the code path is direct.

I don't see an obligation that would now fail outright, apart from
findings 1b and 2: atoms are identified by `same` on quoted terms and by
`conv` within an attempt, and both sides of each comparison go through the
same unfolding. "Slower" is likely but small for these examples: one extra
case-tree run per folded call per omega, plus the recomputation in the check.
Across `decreasing` obligations everywhere (every recursive call with
`omega` or `auto` discharging it), it hasn't been measured.

Fix (SHOULD-FIX): use the unfolding only when it gives omega something more
to read: a number, `k + base` with `k > 0`, or a shape `quote` takes apart
(`+`, `*`, `-`, division). When it would only become a fresh atom, make the
atom of the original folded value, as before. Then the two snapshots should
return to their old hashes, which also tests the fix.

## 4. The example

`examples/accept/omega-folded-call.sw`: `two` returns 2 for every input
(`two Zero = 2`, `two (Succ m) = two m`), so `two 0` is 2. `aboveX` (`x + two 0
> x`), `fromFact` (`x = two 0` gives `x = 2`), `intoFact` (the converse),
`sumOf` and `asInt` (the `Int` path through `OfNat`) each say what their names
claim, and between them they cover G2 (`aboveX`, `sumOf`, `asInt`) and the
folded-call rule (`fromFact`, `intoFact`). OK.

## 5. Other

**5a (SHOULD-FIX).** The module doc's "Quoting" paragraph (`omega.rs:49-67`)
lists how each shape is quoted. Add a sentence: a call folded by name (a
`decreasing` definition, a dictionary field) is quoted as what it unfolds to
when that is arithmetic, and otherwise is an atom. Name the cap from finding
2.

**5b (NOTE).** Tests to add with the fixes: the nested sum from 1b; a
`decreasing` call stuck on a variable in a failing `omega`, with its message
snapshotted to show the call as written; and a fact in scope with an
expensive folded call that the goal doesn't need, which must still check.

**5c (NOTE).** `cases` and `ring` are later steps of this ticket. They will
meet the same three questions (where the check relies on G2, the cost cap,
and whether a stuck unfolding is worth taking), so the fixes here should
be shared rather than repeated per tactic.
