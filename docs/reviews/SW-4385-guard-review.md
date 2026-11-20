# SW-4388: review of lane/SW-4385 (guard refinement, D3701)

Reviewer: Opus, paper only (no builds or tests), 20 Nov 2026. Read
`git diff main...lane/SW-4385` (one commit, e4ca5b6f5), the branch's
`matching.rs`, `check.rs`, `lib.rs` (`check_guard`, `check_leaf_in`,
`Tree::shifted`), `rewrite.rs`, `undo.rs`, the design note
(docs/proposals/guard-refinement.md) and D3701 on SW-4375.

**Verdict: merge after named fixes.** The term construction is sound (the
kernel sees nothing it can't check, and the let-binding and motive are
right), programs are untouched, and the warning never hides an error. But
the design's promise, on which D3701 rests ("with both mitigations, every
proof that checks today still checks", §6 and §8), does not hold: the
fallback covers only a motive that fails to build, not arms that fail
after a successful generalisation, and there are ordinary proof shapes
where that happens. That is a D3688-style loss and needs a fix (or Matt's
explicit decision) before merging.

## 1. Can a guarded proof arm prove something false, or hand the kernel an ill-typed term?

No to the first: every term is still checked by the kernel, and nothing
here changes the kernel. No to the second, as far as reading can tell:

- **The motive.** `refined_guard` reuses `bind_generalised` and
  `motive_checks_now` from `generalised_now`, tries the plain motive then
  the `Transport` one, and builds the same `Case` on `x` that
  `match g:`'s arms do, lifted by `lift::draft_with` with
  `(vec![x], vec![Some(equation)])`. Any failure while preparing (blocked on
  an unknown, too large to read back, a type read as written, a motive that
  doesn't check, a non-fatal error) restores the snapshot (`Snapshot`
  includes `cx.mark()`, so the bound variables and the `rebind` scope
  entries go too) and returns `None`. Fatal errors propagate. Correct.
- **The let-binding.** `Term::let_(name, ty_term, fact, body)`: in the
  elaborator the fact is bound with `cx.bind` as an opaque variable of type
  `ty`; in the kernel it is a transparent `let` with the same type, so the
  body only gains definitional equations. Anything typed under the opaque
  variable is typed under the `let`. `ty` is read from the refined
  `cx.types[equation]` (`scrutinee = True`/`False`) for a `Bool` test, and
  `prop`/`¬prop` shifted by `cx.level() - base` for a decided proposition,
  with values `d.sound eq` and `refute d eq`. The guarded and the unguarded
  arm of a proposition guard both build a let whose value the kernel checks
  even when the name is hidden, and `clampAtMost`, `lessOrAtLeast` and
  `zeroOrPositive` exercise both, so the projection index and `refute`'s
  argument order are confirmed by the kernel, not just by reading.
  One assumption: when `comparison_in` gives the direct comparison
  (`Nat.leq …`) instead of `holds d`, `d.sound eq` needs `holds d ≡ that
  comparison` by computation. That is what `match g:` already relies on
  (matching.rs:559-573), and `clampAtMost` covers it.
- **The shift** (below) can only produce wrong variable references, which
  the elaborator or kernel rejects as type errors; it can't produce a
  wrong proof.
- **The fallback** calls `proof_if` with the `prop`/`decision` elaborated
  before `refined_guard`'s snapshot, so they are still valid. Correct.

## 2. The shift in `check_guard` (lib.rs)

`otherwise` is compiled for `split_at + 1` variables (the context plus the
`if`'s fact). In the refined path the arms below run at `split_at + k + 1`
(`x`, the copies and the equation from `bind_generalised`, then the fact
from the closure), and `otherwise.shifted(split_at, k)` moves every level
≥ `split_at` up by `k`. On paper:

- **Guard then catch-all** (`| c if … => a | c => b`): the leaf's aliases
  are below `split_at`, unchanged; correct.
- **Guard then arms that split and bind fields** (`| xs if c => a | [] => b
  | [x, ..r] => e`): the `Case` node's `depth` is `split_at + 1`, moved to
  `split_at + k + 1`, where the fields are now bound; correct.
- **Chain of two guards** (`| p if c1 => a | q if c2 => b | rest`): the
  inner `Guard`'s leaf and otherwise are shifted recursively
  (`Tree::shifted` recurses into `Guard`); the inner `check_guard` then
  takes `split_at = cx.level()` afresh, and its own `otherwise`, already
  moved by `k1`, expects `split_at2 + 1`. Correct, and the shifts compose.
- **Text-pattern rests** (`lets_from..split_at`) are shifted before
  `split_at` is taken; correct.
- **Nested matches**: a guard in an inner tree takes its own `split_at`;
  an inner `match` in an arm compiles its own tree at its own level.
  Correct.
- **Unrefined paths** (`proof_if`, and `check_if_in` for programs) bind
  exactly one variable before checking the branch (the only `.check(cx`
  sites are check.rs:7642, 7671, 7740), so `added` is 0 and nothing
  changes. If a future path ever calls the branch with no variable bound,
  `cx.level() - (split_at + 1)` underflows (panic in debug, a huge shift in
  release): worth a `checked_sub` with an `expect` naming the invariant.

**But the shift is only a shift, not the renaming the refinement needs.**
`bind_generalised` copies every variable whose type mentions the condition
and `rebind`s names to the copies, and the goal is generalised over the
copies. The tree below still refers to the *original* levels: a leaf below
that aliases a copied column binds its name to the original (unrefined)
variable, and a `Case` below on a copied column splits the original, which
the generalised goal no longer mentions. Neither is unsound; both are
"checks on main, fails now" (see 3).

None of the committed examples exercises a shift that matters: in every
guarded proof arm in the repo and in the new examples, what is below the
guard is a leaf with aliases below `split_at` (or an unguarded leaf whose
`match` splits in `in_tree`, at check time). The `split_at` arithmetic is
right on paper but untested.

## 3. D3688: can a proof that checks on main stop checking?

**Yes.** The fallback runs only when the generalisation fails; once it
succeeds, an arm that fails is an error. Cases, in order of how likely they
are:

**3a. A condition the arms below then split on (must fix).** The plainest:
a `Bool` guard on a column, with later arms matching that column.

```
theorem eitherWay ∀ (n: Nat) (b: Bool): b = True ∨ b = False := match n, b with
  | 0, c if g: c => Inl g
  | _, True => Inl byComputing
  | _, False => Inr byComputing
```

On main this checks: under `n = 0` with the guard false, the tree splits
`b`, and the `True` case's goal is `True = True ∨ True = False`. On the
branch, the condition's normal form is the variable `b`, so
`refined_guard` generalises `b` itself (unlike `match g: b`, which would
split the column): the goal below is `False = True ∨ False = False` for
every case, the tree's split on the original `b` no longer touches it, and
`| _, True => Inl byComputing`, checked again under `n = 0` (a case the
hidden equation, now `True = False`, rules out), fails with `E-REFL`. I
predict this from the code and couldn't run it; it should be the first
test the fix lane writes. The same happens with a computed condition and a
later arm on its column (`| xs if xs.isEmpty => … | [] => byComputing`
when the goal's function tests `isEmpty`): the arm below is checked, in a
case the guard rules out, against a goal with `False` where main had the
computed `True`. Arms checked in an impossible case are *checked*, not
dropped (`check_leaf_in` only notes the case for `W-UNREACHABLE`), which is
also where the lane's "new W-UNREACHABLE" comes from.

**3b. `rewrite … at h` (must fix, or covered by 3a's fix).** Design §6.1
lists `rewrite g at h`; the implementation handles only the goal form
(`rewrite_goal`). `rewrite_at` (rewrite.rs:170) has no `refined_by_guard`
path, so `rewrite g at h` where `h` was copied and refined finds nothing
and fails with `E-REWRITE-NOTHING`, where it checks on main. Same for the
inferred form (`infer_rewrite`).

**3c. Leaves below that alias a copied variable.** `| n, h if c => a |
n, h => b` where `h`'s type mentions the condition: in `b`, `h` aliases the
original level (unrefined type) while the goal is refined. Transport along
the equation (`along_match_equation`) may rescue uses of `h` as a proof
argument, not every use. Rarer than 3a.

**3d. The fact below changed form.** A `Bool` guard's arms below now get
`c = False` instead of `¬(c = True)` (intended, D3699). It is hidden, so
only `cases`, `auto` and `arithmetic` see it; a proof relying on one of
them handling the old form but not the new one stops checking. Probably
none, but nothing checks it.

**3e. Unification against the refined goal.** A lemma applied with an
argument the goal used to determine (`foo _ g` where `?b` is solved from
the goal as `c`, now `True`) then mismatches `g : c = True`. Transport may
or may not cover it.

**The fix I recommend (one change covers 3a to 3e):** in
`check_guard_if`, if `refined_guard` returns `Err` from an arm (not fatal,
budget not exhausted), restore a snapshot taken before it and run
`proof_if` unrefined; if that checks, use it; if it fails too, report the
refined errors (they match the documented rule). To keep the cost at 2×
on failing proofs rather than 2^k along a chain of k guards, set a
"no refinement" flag on `Ctx` during the retry so that inner guards go
straight to `proof_if`, and don't retry inside an attempt already under
that flag. This makes §8's claim true by construction, at no cost to
proofs that check refined. A warning when the unrefined retry is what
checked (say `W-GUARD-UNREFINED`, pointing at the guard) would tell users
why `byComputing` doesn't see the refinement there; optional, a
follow-up.

A narrower complement (follow-up, not instead): for a condition whose
normal form is a variable, split that variable as `match g: b` does
rather than generalising it; and rename copied levels to their copies in
`otherwise` (not only shift), so that arms below see what `match g:`'s
arms see. Both make refinement succeed more often; the retry is what
guarantees D3688.

If the orchestrator would rather not retry, this is Matt's: D3701 was
approved on the claim that no proof stops checking, and 3a is a natural
shape (a guard on a `Bool` parameter, then arms on it).

**Errors in arms below a failing guarded arm.** `refined_guard` checks
both arms and reports all failures (`branch_errors`), where `proof_if`
stopped at the first. That only adds diagnostics; it changes no verdict.
With the retry, those extra errors must be dropped by the snapshot restore
when the unrefined attempt succeeds (they live in `cx.e.attempt`, which
`Snapshot` covers).

## 4. Does the warning's loose test hide a real error?

No. `refined_by_guard` decides only whether to *try* without the rule; the
rule is dropped only if `close_rewrite` then succeeds with the remaining
rules and body, and on failure the snapshot is restored and the rule's own
`E-REWRITE-NOTHING` is returned. A later rule's error still wins
(`outcome?` runs first). The result is kernel-checked either way. The
looseness only widens which proofs warn instead of erroring: any rule whose
computed left side contains a refined condition (the `clamp.eq2 limit n _`
case in the example, on the arm *below* the guard, is one) and that turns
out to be unnecessary now warns, where on main a pointless rewrite of that
kind would have been `E-REWRITE-NOTHING` with "checks without this
rewrite". That's a widening, not a hidden error. The warning's text says
"the guard above already replaced its condition", which is true in those
cases.

Small things: the warning is pushed to `attempt.lambda_warnings`, so an
attempt that is undone drops it (good); it is deduplicated by span (good,
since tree arms are checked once per path).

## 5. Do programs stay unchanged?

Yes. `check_guard_if` calls `check_if_in` when `!proof_expected`, which is
exactly what `check_if_with` did; `check_if_with` itself is unchanged for
plain `if`. `added` is 0 on that path. The hash snapshots change only
theorems (`zeroOrPositive`, `afterGuard`, `lessOrAtLeast` gain a
`%match` helper); no `def`'s hash moves, so std's native pins are
unaffected. Programs inside theorem statements (`Parse.Gives (() => match
… if …)`) have data goals and take the program path.

## 6. Docs

Accurate, with two corrections once 3a/3b are fixed or not:

- docs/syntax.md says `| p if c => a | rest` *is* `| p => match g: c with
  | True => a | False => rest`. Not exactly: for a variable condition
  `match g: b` splits the column while the guard generalises it, and arms
  below keep the original variables (2, 3c). After the retry fix, add
  "where refining makes a proof fail, the guard splits as before", or
  soften "is" to "refines as".
- docs/proving-guide.md: "A `rewrite g` … finds nothing to rewrite: drop
  it (`W-REWRITE-GUARD-REFINED`)" is true for the goal only; `rewrite g at
  h` is `E-REWRITE-NOTHING` today (3b). Say so, or extend the warning.
- docs/guide/10-proofs.md and its `capAtMost` snippet are correct (`cap`
  is guard-defined at proofs.sw:188; the goals stated are right).

## 7. Missing tests

Before merging (all small, accept examples or single named tests):

1. **3a's `eitherWay`** (above) in examples/accept: fails today by my
   reading; passes after the retry fix.
2. **A guard followed by arms that split and bind fields**, so the shift's
   `Case depth` path runs: e.g. `| xs if xs.isEmpty => … | [] => … | [x,
   ..r] => …` where the last arm uses `x`.
3. **A chain of two guards in a proof** followed by a catch-all, each
   computing through a program's matching `if`, so the composed shifts run.
4. **`rewrite g at h` in a refined arm** (3b): accept, with or without a
   warning depending on the fix.

Follow-ups (file, not blocking): a guard on a text-pattern rest in a proof
(shift past `text_lets`); a column whose type mentions the condition (3c);
the `checked_sub` assertion in `check_guard`.

## Lane's listed risks, judged

| risk | judgement |
|---|---|
| shift (`split_at`) has no committed test | correct on paper for chains, catch-alls, field-binding splits and nested matches; untested in any case that matters: tests 2 and 3 |
| facts bound with `Term::let_` | sound (transparent let ⊇ opaque variable); kernel-checked in both arms by existing examples |
| warning's loose test | never hides an error (4) |
| pattern variable's copy visible by name below | real but harmless: `rebind` pushes scope entries after `aliased.end`, so `suspend_names` in the `rest` closure doesn't hide them, and a name the guarded arm bound, if its type mentions the condition, is visible below as the copy. It can shadow an outer name of the same name in the arms below (a contrived D3688 case). Follow-up: suspend those entries too |
| failing guarded arm reports arms below too | only more diagnostics; and some of them spurious (3a's dead cases) until the retry fix |
| new W-UNREACHABLE | yes, from the `%guard` equation becoming `True = False` in cases the guard rules out; warnings only, and accurate, but the arm body is still checked there, which is 3a |

## Must fix before merging

1. **crates/elab/src/check.rs, `check_guard_if`:** when `refined_guard`
   returns a non-fatal `Err` from an arm, restore a snapshot and retry with
   `proof_if` unrefined, under a `Ctx` flag that makes inner guards skip
   refinement (cost ≤ 2× on failing proofs); report the refined errors if
   both fail. Covers 3a to 3e and keeps D3701's "no proof stops checking".
   (Alternative: take 3a/3b to Matt as a D question; I recommend the fix.)
2. **examples/accept:** add tests 1 to 4 of section 7 (the `eitherWay`
   case, a field-binding split below a guard, a chain of two guards,
   `rewrite g at h`).
3. **docs/syntax.md and docs/proving-guide.md:** the two corrections in
   section 6, matching whatever the fix does.

## Follow-ups (file as tickets)

- Rename copied levels to their copies in the `otherwise` tree (not only
  shift), and split a variable condition as `match g: b` does, so
  refinement succeeds in 3a/3c instead of falling back (Opus, elab).
- `W-REWRITE-GUARD-REFINED` for `rewrite … at h` and the inferred
  rewrite, as design §6.1 listed (Sonnet).
- Suspend the `rebind` scope entries for the guarded arm's own names in
  the `rest` closure of `check_guard`, so arms below can't see them
  (Sonnet, small).
- `checked_sub` with an invariant message for `added` in `check_guard`
  (Sonnet, one line).
- Optional: a warning when a guard falls back to the unrefined split
  (design §6's "a later W- warning"), so users can see why it didn't
  refine.
- SW-4376 (show unnamed guard facts) still stands, as D3701 said.

## Erratum (20 Nov, from SW-4391 and SW-4402)

- §2 and §3a: `eitherWay` does not break. The compiler splits `b` above the guard (the arms below a guard are always flat), so it refines on main. The retry fix (must-fix 1) still stands for its other cases (the `rewrite ... at h` break).
- §6: `match g: b` on a variable generalises the condition; it does not split the column (a named scrutinee is never treated as a variable column).
