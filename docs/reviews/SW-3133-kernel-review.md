# SW-3133 (kernel's check takes less stack on deep terms): soundness review

Reviewed: commit `4f6898d2d` on `lane/SW-3133`, by reading the diff against
its parent. `crates/core/src/check.rs` is unchanged between that commit and
the branch head (`ac22a2f0e`). Paper review: nothing was built or run.

## Verdict: SOUND

The kernel accepts and rejects the same terms, with the same error codes,
messages and spans, and returns the same checked terms, with one intended
exception and one benign one:

- **Intended:** a term whose application spines are long no longer runs out
  of stack in the type checker, so some terms that failed with `E-RESOURCE`
  now check. No type error becomes an acceptance.
- **Benign:** on a resource error while computing a lambda's body type, the
  context is now left unbound instead of bound (finding 3).

No fixes are needed for soundness. Two robustness findings and a test gap
follow; the test gap is the one worth closing before or soon after merging.

## What was compared

### Applications (`infer_spine`, `check.rs:277`)

The old arm for `App(f, a, icit)` was uniform: no head was treated
specially (constructors, data types and quotient forms carry their
arguments in vectors, not in `App`; recursors and case trees are
definitions). So there are no special heads for the loop to miss. Per
argument, the old code did five things, and the loop does the same five in
the same order:

| Step | Old (recursive arm) | New |
|---|---|---|
| Function's type to weak head normal form | `force(&g, f_ty)?` | `function_type`, `check.rs:303` |
| Must be a `Pi` of the same implicitness, else `E-NOT-A-FUNCTION` showing the forced type | `Value::Pi(_, pi_icit, dom, cod) if pi_icit == *icit` | same guard, `check.rs:304`; message in `not_a_function` is word for word |
| Argument checked against the domain | `check(cx, a, &dom)?` | `check.rs:292` |
| Argument evaluated only if the codomain mentions it | `cod.body.mentions(0)`, `cx.eval(&a)?` on the *checked* argument | `result_type`, `check.rs:311`, also given the checked argument |
| Codomain applied; application rebuilt | `cod.apply`, `Term::app_icit(f, a, *icit)` | same |

The domain of argument k comes from the codomain closure applied to
argument k-1's value, exactly as before: nothing is cached or keyed on the
whole application, and the spine is not split anywhere a check could fall
between. The loop stops at the first head that isn't directly an `App`, so
`App(Loc(App(..)), a)` hands the `Loc` to `infer`, which sets and restores
the span as before; error spans are therefore unchanged.

**Order of effects.** The old recursion called `budget.nesting` for each
application from the outermost in, then inferred the head, then checked the
arguments first to last. The loop calls `nesting` for every application but
the first on the way down (the caller has counted that one), then
`infer(head)`, then the arguments first to last. I counted visits for
`infer` and for `check` of spines of one and two arguments: 2 and 3 for
`infer`, 3 and 4 for `check`, old and new. So `total_visits` is unchanged,
and a budget that is already exhausted fails at the same call.

### `check` (`check.rs:506`)

- Old order for an application: `nesting`, `force_ref(expected)`, fall to
  the last arm, `infer` (`nesting` again), `conv`, `mismatch`. New
  `check_app`: `nesting` (in `check`), `force_ref`, `nesting`,
  `infer_spine`, `conv`, `mismatch` with the forced expected type. Same.
- No old arm could match an application before the last one (the arms were
  `Loc`, `Lam`, `Ctor`, `Refl`, `Let`, `Case`, `NumCase`), so sending every
  `App` to `check_app` skips nothing.
- `check_form` reorders the arms (`Let` before `Refl`, `Case`), but each
  arm matches on a different term form, so order doesn't matter. `Lam`
  against a matching `Pi` is tried first, and every other `Lam` reaches
  `check_other`'s mismatch error, as before.
- `check_ctor` (`check.rs:584`) keeps the three old arms in order: unknown
  constructor, then expected type is this data type, else mismatch. The
  index comparison and both messages are unchanged.
- `check_other`'s `unreachable!` (`check.rs:712`) is unreachable: it is
  called only from `check_form`, with `Lam`, `Refl`, `Case` or `NumCase`,
  and has an arm for each.

### `infer_data` (`check.rs:337`)

Line for line the old inline arm: unknown data type, the arity message
(moved to `data_arity_error`, same text), the telescope of parameters then
indices, each argument checked against its type evaluated in the earlier
arguments' values, a value computed only when `later_types_mention`, and
`Value::Sort(data.sort)`.

### `infer_other` (`check.rs:384`)

The remaining arms are the old ones, untouched. Its first two arms
(`Loc`/`App`/`Data` and an in-scope `Var`, sent back to `infer`) can't be
reached, since `infer` handles those forms before calling it.

### The spec

`docs/core.md` describes the typing rules, not how the checker recurses,
and no rule changed, so it needs no update (D3210 doesn't apply). I searched
it for the application rule and the depth guard rather than rereading it
whole.

### Elaboration side (light review)

- `lift::go_replace` (`crates/elab/src/lift.rs:381`): equivalent. Along a
  spine, each inner application gets its `nesting` call and is offered to
  the hook outermost first; a hook result replaces that part and the outer
  arguments are still rebuilt; a variable head is annotated only when the
  function part, with `Loc` stripped, is a variable, as before
  (`Loc(App(..))` goes through `go`, as before). Head first, then arguments
  in order.
- `unify::rename_in` (`crates/elab/src/unify.rs:2644`): equivalent. Moving
  `Data`, `Ctor` and variable- and definition-headed neutrals ahead of the
  other arms is safe, because no earlier old arm matched them (the guarded
  `Head::Meta` arm is the only one near). `rename_call` returns `None`
  exactly where the old code fell back to the unfolding (`Fail::No`).
  `Term::Data(d, all(..))` builds what `Term::data` did.
- `268822645` (printer): glanced at its size only; not reviewed.

## Findings

### 1. Low (test gap): the new kernel test covers only the accepting path

`kernel::a_long_spine_is_inferred_in_a_loop`
(`crates/core/tests/it/kernel.rs:2147`) is a good positive test: 20,000
arguments would need about 28 MB in the old recursion, so it fails without
the loop; the function's type is a call (`Args n`) that must be forced at
every step; and the first argument's value flows into the type. It is the
only kernel test the commit adds, and it never takes an error path through
the loop. The existing rejections (`kernel.rs:213`, `:694`, `:1209`) use
one or two arguments. Since the risk in this change is a check skipped
mid-spine, these would pin it down, each a few lines with the same `Args`
setup:

1. **Ill-typed argument deep in a long spine.** `f 1000 0 0 … true … 0`
   with a `Bool` constructor at position 500: expect `E-TYPE-MISMATCH`.
   Also once with the bad argument last.
2. **Later domain depends on an earlier argument.** `g : (n: Nat) → (v:
   Vec n) → …` (or `(A: Type) → A → …`) applied as `g 2 (v: Vec 3)`: expect
   a mismatch; and `g 2 (v: Vec 2)` accepted with result type mentioning 2.
   The current test's later domains are all `Nat`, so a loop that
   instantiated a domain with the wrong argument would still pass it.
3. **One argument too many.** `f 3 0 0 0 0`: expect `E-NOT-A-FUNCTION`,
   with the message showing `Nat` (the type after three arguments, not
   `Args 3`).
4. **Implicitness mismatch mid-spine.** An implicit argument at position k
   of an explicit `Pi`: expect `E-NOT-A-FUNCTION`.
5. **`check_app`'s comparison.** `check` of a long, well-typed spine
   against the wrong expected type: expect `E-TYPE-MISMATCH`. The new test
   only calls `infer_closed`, so `check_app` is exercised by it only
   through arguments, none of which is an application.
6. **A `Loc` inside the spine.** `App(Loc(s, App(f, a)), b)` with `b`
   ill-typed: the error carries the outer span, not `s`.
7. **Visit count.** `total_visits` after inferring a three-argument spine
   equals a number written in the test, so the "same visits" claim is held
   by a test and not only by reading.

### 2. Low (robustness, playground only, not soundness): more calls per KiB of guarded stack

`crates/web/build.rs` explains that the 320 KiB guard counts stack in
linear memory, while the browser's own call stack overflows first, as a
`RangeError` the compiler can't recover from; the margin was measured per
pass (the printer overflowed V8 at 500-550 KiB, the elaborator at
790-1050 KiB). This commit makes the type checker's frames smaller and adds
call levels (`check` → `check_form` → `check_other`; `infer` →
`infer_app`/`infer_other`; `function_type`, `result_type`, `body_type`). So
the checker now makes more WebAssembly calls for each KiB the guard counts,
and its real overflow point, in guard bytes, has moved down by an unknown
amount. The note says the new peaks are "not yet measured in the browser".
Suggested: rerun the `STITCHWORT_STACK_PROBE` stress page for the type
checker (a deeply nested non-application term, such as lambdas or lets
nested until the guard trips) and confirm the guard still trips before V8
does. A crash here restarts the playground's worker; it can't accept a bad
proof.

### 3. Info: a lambda's context on a resource error

Old: `cx.bind(..)` and then `cod.apply(..)?` inside the call's argument, so
a resource error from `apply` returned with the variable still bound. New
(`check.rs:546`): `body_type` runs before `bind`, so the context is left
clean. The value is the same either way (the variable's level is taken
before the bind in both). The only place `check.rs` catches an error and
continues is `Eq(None, ..)` on `E-CANNOT-INFER`, which a resource error
isn't, so nothing observes the difference. An improvement.

### 4. Info: the checker no longer bounds spine length for later passes

Before, a spine of n arguments cost the checker over 1 KiB of stack each,
so any term it accepted had spines short enough for every later pass. Now
spine length is bounded only by the term's size. I looked at the passes
that walk a checked term: evaluation is a stack machine, `mentions` and
`subterms` use a work list, `Term`'s `Drop` is iterative, and hashing,
shifting and the termination checker call `nesting`. The reference
evaluator (`crates/core/src/reference.rs:228`, `:382`) recurses on the
function part without a guard; if it only runs in tests and cross-checks
that is fine. Worth a ticket only if some production pass after the kernel
turns out to recurse on spines unguarded; I didn't sweep the JS backend or
erasure.

## Not done

- Nothing was built or run: equivalence is by reading the old and new code
  side by side.
- No measurement of stack use natively or in the browser (finding 2).
- The printer commit `268822645` and the pretty-printer tests.
