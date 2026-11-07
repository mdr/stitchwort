# SW-2108: review of the SW-2095 merge (applied stuck fields of calls)

Reviewed by reading only (no builds or runs): merge `6f77603fe`, against
`docs/proposals/match-call-field.md` stage 1, `crates/core/src/value.rs`,
`check.rs`, `machine.rs`, `inert.rs`, `reference.rs`,
`crates/elab/src/matching/as_written.rs` and
`crates/driver/tests/proofs/proof_equivalence.rs`. Opus, 7 Nov 2026.

## Summary

The change is sound and does what stage 1 asks, but its central claim is
wrong: **the kernel does reach the new path.** The kernel checks every
definition's body and signature with gluing on (`check.rs:1828`,
`check.rs:1882`; `machine.rs:24-29` says so), so `apply_field` and the `J`
arm run inside the kernel, and `conv-call-field-applied.sw`'s `twoWays` is
almost certainly accepted by the kernel because of them. That is still
sound: the path unfolds only a body `body_seen` allows (transparency
respected, the group being checked has no body yet), inside the same step
and frame budget, with the ordinary delta, case, projection and beta rules.
It brings the glued kernel in line with the unglued one, which already
computes `f x` eagerly, so it adds no trust. The `ptr_eq` stuck test is
right. Two real defects remain. The `J` arm hands `JForced` an unforced
value, which can panic on a glued call. And for a definition with a
`Quot.lift` leaf, the glued path now computes through the lift where the
unglued one and the reference evaluator stay folded, which breaks
glued/unglued agreement and the display policy of map-equality §7.2. The
hot-path cost is negligible.

Top five recommendations:

1. Correct the "kernel unchanged" claim in `computes_field`'s doc
   (`value.rs:2249-2254`) and in the proposal (`match-call-field.md:49`,
   `:304`). State the actual soundness argument (F1).
2. In the `J` arm of `Frame::FieldOf`, push `Frame::JProof`, not
   `Frame::JForced`, so the field is forced before `J` looks at it (F2).
3. Give `unfold_field_for` the stuck flag `true`, so a `Quot.lift` leaf
   leaves the call folded, as unglued evaluation and the reference do (F3).
4. Add the missing tests: `J` on a stuck field (stuck, and computing to a
   call), gluing off, an opaque call's field, the lift leaf, and
   `proof_equivalence` matrix terms for applied fields of calls (F4).
5. Leave the hot path alone. The guard costs one load and a compare (F5).

Findings: high 0, medium 2 (F1, F2), low-medium 1 (F3), low 3 (F4-F6).

## Findings

| # | Where | What | Severity | Confidence | Fix |
|---|---|---|---|---|---|
| F1 | `value.rs:2249-2254`, `match-call-field.md:49,304` | The kernel reaches `apply_field`/`FieldOf`. The claim and the comment say it doesn't. Sound all the same | medium (trust doc) | high | S |
| F2 | `value.rs:1794` | `J` arm pushes `JForced` with an unforced field: `Value::Call` hits `panic!("internal error: J applied to …")` | medium | medium-high | S |
| F3 | `value.rs:2287` (flag `false`) | A lift-leaf call's applied field computes through the lift while gluing, but stays folded unglued and in `reference.rs`: the modes disagree, and goals show the lift | low-medium | medium | S |
| F4 | tests | No unit test for `J`, gluing off, an opaque call, the lift leaf; no matrix terms | low | high | M |
| F5 | `value.rs:963`, `1097` | `ends_in_field` on every neutral `Def` application | low (none) | high | none |
| F6 | `value.rs:1766-1805` | The case tree runs twice for a field `CallField` already found stuck | low | high | none now |

## Details

### F1. The kernel reaches the new path. It is sound.

**Reachability.** `in_kernel_modes` (`machine.rs:64-76`) turns gluing off
on entry. Then `admit_group` turns it on to check every body
(`check.rs:1828`), and `declare_def` turns it on to check every signature
(`check.rs:1882`). The validator's `not_a_proof` (`reference.rs:1061`) and
`inert::candidates` (`inert.rs:90`) also evaluate glued. With gluing on,
`glues` (`value.rs:2137`) keeps calls as `Value::Call`, a field of one is a
`project_call`, and `Frame::CallField` names a stuck field as
`Neutral(Def f, [args.., Proj])` (`value.rs:1694-1719`). Applying that is
`apply_field` with `computes_field` true. `conv-call-field-applied.sw`'s
`twoWays` is a theorem, and the kernel checks it glued. Before the merge the
glued left side was the stuck `tiled cave .level n`, named by the outer
call, which no conversion rule looks inside: `is_folded` needs the spine to
end in a projection. So the kernel's acceptance of that example very likely
depends on the new path.

**Soundness.** The path computes nothing the kernel couldn't already
compute. Check each point:

- It unfolds only when `is_folded` holds, which requires `body_seen`. A
  hidden opaque definition stays neutral. So does a member of the group
  being checked, which has no body yet, so the path can't recurse into the
  definition under check.
- It runs the definition's case tree in the same machine, so the budget
  counts every step, and `push` counts every frame.
- It takes the field with `ProjOf` and applies it with `AppTo`, the
  ordinary rules. `(f x).i a` is `(unfolding of f x).i a` by delta.
- Unglued, the kernel already computes this: `f x` unfolds when it's
  built (`unfold_now`, stuck flag `true`), so `.i a` is taken of the
  unfolding. The new glued path gives the same value, except at lift leaves
  (F3).

It adds no new trust. But the kernel's soundness argument now runs through
`FieldOf`, `CallField` and `apply_field`, and the comment and proposal tell
the next reader that it doesn't. That is why this is rated medium.
**Change:** rewrite `computes_field`'s doc to say that it runs in the kernel
too (bodies and signatures are checked glued) and why that is sound: the
four points above. Fix `match-call-field.md:49` and `:304` the same way.
Size S.

### F2. `J` on a computing field can panic.

In `Frame::FieldOf`'s computing branch (`value.rs:1787-1805`), the `J` case
pushes `Frame::JForced`, then the `ProjOf` frames. `ProjForced` returns
`project(d, i, value)` without forcing the field. `JForced` expects a forced
value: its normal producer is `JProof`, which forces first
(`value.rs:1622-1625`). A field that is a glued `Value::Call` matches
neither guard (`folded_call` and `computes_field` match only `Neutral`).
It falls to `other => panic!("internal error: J applied to …")`. The same
happens when the unfolding is itself a call (`f x := g x`): `ProjOf` on a
`Value::Call` returns `project_call`, another `Value::Call`. A solved
metavariable's neutral would also be treated as stuck rather than replayed.
The `App` case is fine, because `apply_step` sends a `Value::Call` on to
`apply_call`.

**Reaching it** needs a stuck field call whose call can step now. That
happens when the field was named while the call was stuck on a metavariable
since solved (elaborator), or when it was made under a narrower
transparency set (the kernel's unglued `ty_value` with opaque definitions
hidden, then used in a body that sees them). Then `J` on it: `rewrite`
with a record's equation field, or a cast. That is rare, but the result is
an internal-error panic, possibly inside the kernel. **Change:** push
`Frame::JProof { term, env }` there. Add a unit test where the call's leaf
is another definition's call returning a record with an `Eq` field. Size S.

### F3. Lift leaves: glued and unglued now disagree.

`unfold_field_for` runs the tree with the stuck flag `false`
(`value.rs:2287`), as `unfold_for` does, so a `Quot.lift` leaf is evaluated
instead of leaving the call folded. Take a definition `f` with
`Def::lift_leaf` whose result is a record with a function field:

- *Glued:* `CallField` names `(f x).i` (its `unfolded: true` branch gets a
  `Quot` neutral and names it). Then `apply_field` reruns the tree. The
  result is not `ptr_eq`, so the value is `(Quot.lift … q).i a`.
- *Unglued:* `f x` folds on the lift (`unfold_now`, flag `true`), then
  `.i`, then `a`. `computes_field` is false, so the value stays
  `f x .i a`. `reference.rs` (`eval_tree` with `fold_lifts = true`, and
  `is_folded` only at full arity) gives the same.

So `rfl : (f x).i a = (Quot.lift F h q).i a` holds glued, but not unglued or
in the reference. The kernel checks glued, so the kernel accepts it. That's
still sound, since both sides really are equal. But it breaks the invariant
that `proof_equivalence` asserts (glued = unglued = reference for every
pair). And goals now show the lift rather than `f x`, which is what
map-equality §7.2's policy exists to avoid. This is the lane's unsure
`Quot.lift` case: it's not a loop and not unsound, but it is a disagreement.

**Change (call I made):** pass `true` as the flag in `unfold_field_for`.
The lift leaf then returns `Neutral(f, call)` with the same `Rc`, the
`ptr_eq` test takes the stuck branch, and all three modes give
`f x .i a`. Completeness for such pairs, in every mode, is then a separate
question with no current user. Add the matrix term. Size S. Confidence
medium: I didn't trace every arm of `conv` for a `Def`-headed neutral
against a `Quot`-headed one.

### F4. Missing tests

The merge adds three `examples/accept` files, all glued and all with
transparent definitions and an `App`. Nothing covers:

- `J` on a stuck field: the stuck branch (`JReady`), and the computing
  branch with a call-valued field (F2).
- Gluing off: an applied stuck field stays `f x .i a` and the machine
  doesn't loop. This is cheap to assert in `crates/core/tests/it/glue.rs`
  with `g.machine.glue.set(false)`.
- An opaque call's field: hidden, so `is_folded` is false, and it stays
  stuck. With the definition in the transparency set, it computes.
- The lift leaf (F3).
- `proof_equivalence.rs` matrix terms: an applied field of a call stuck in
  its own tree, of a call whose leaf is another call, and of a lift-leaf
  call. That is the test that keeps the glued and unglued kernels
  agreeing. Add them there, not just as examples.

Size M (one lane, together with F2 and F3).

### F5. Hot-path cost: none worth acting on

`apply_step`'s new guard (`value.rs:963`) runs on every application of a
neutral `Def`, which includes each curried argument of a partly applied
definition, so it is the hot path. But `ends_in_field` reads only the
spine's `Option<Rc>` and, if present, its last element's tag. The
`spine.push` that follows touches the same memory anyway. The `run` arm
(`value.rs:1097`) is on `Control::Apply`, which only boxed (cold)
applications reach. Unglued, a field call applied takes one extra boxed
round trip through `apply_later`, but that is rare. 69.4 s against 68 s
under load is within noise. No change. (Per the 1 Nov review §4.5: no
speculative rewrites.)

### F6. The case tree runs twice for a field already found stuck

When `CallField` has just found `f x` stuck and named `(f x).i`, applying
it reruns `f`'s case tree in `FieldOf` only to find it stuck again (the
scrutinees are values, so this is cheap). That's the price of not marking
the name. Not worth a flag unless a profile shows it.

## Checked and sound

- **The `ptr_eq` stuck test** (`value.rs:1777`). `unfold_field_for` gives
  the same `call` `Rc` to the `Stuck` tuple and to `FieldOf`. `stuck_tree`
  returns exactly that spine, so a stuck tree is recognised. A tree that
  steps can't return `Neutral(f, call)` with that `Rc`: a leaf builds a
  new spine, and `f x` reducing to itself is ruled out by termination. The
  Nat.add R3/R4 values aren't `f`-headed records. Arity 0 gives
  `Spine(None)` on both sides (`From<Vec>`), but an arity-0 definition
  whose body evaluates to itself can't pass termination either. It can't
  loop: the stuck branch's `Control::Unfold` gets a spine ending in `App`,
  so `ends_in_field` is false, and `unfold_now` returns it neutral, short
  of arity. In the computing branch, a nested field call goes through
  `CallField` then `apply_field` on a different (inner) call. Each step
  descends into an admitted definition's unfolding, and the budget bounds
  it. This is the same idiom as `Frame::Unfolding` and `unfold_folded`.
- **The `App` branch.** `AppTo` receiving an unforced field is fine:
  `apply_step` sends a `Value::Call` on to `apply_call`, and a solved
  metavariable's neutral is replayed when it's forced.
- **`Replay`** (proposal §5 lists it) reaches the new path through
  `apply_step`'s arm. No separate change was needed.
- **Erasure.** `computes_field` doesn't check `program_running`, but gluing
  is never on while a program runs (`machine.rs:28`), and `glues` refuses
  then too.
- **`reference.rs` needs no mirror**, except for F3. The reference never
  glues (`reference.rs:574`) and computes `f x` eagerly, which is what the
  new glued path now matches. Its `glue.replace(true)` at line 1061 is the
  inert validator calling `value.rs`, not the reference evaluator.
- **`Finder::agree`'s `Proj` arm** (`as_written.rs:764`): it is structural,
  consistent with the other arms, and binds no variable, so `under` is
  unchanged. Correct.
- **2021 day 15.** The removed `tiledIsTiles` and the restored
  `let (Both height width)` are exactly the workarounds the comments
  attributed to SW-1913.

## The 1 Nov review's findings in scope

- §4.1 (manual save/restore of gluing, not panic-safe): **still open**, and
  more relevant now that F2 is a panic path inside a glued region. The
  pattern is at `check.rs:1828`, `check.rs:1882`, `inert.rs:90` and
  `reference.rs:1061`. A panic leaves `glue` on. That only matters if a
  host reuses the session after catching it (the LSP?).
- §4.4 (large files): `value.rs` is 4,717 lines and still growing. It is
  **unchanged as a finding**. This merge adds about 150 lines, cleanly
  outlined as cold functions.
- §2.2/§3.4 (the reference as an independent oracle): F3 is exactly the
  kind of disagreement it exists to catch, but nothing in its matrix
  exercises it yet (F4).

## Calls I made

- I rated F1 medium, not high: the behaviour is sound, and only the stated
  reason is wrong.
- I recommend the stuck flag `true` for F3 (consistency and the display
  policy) over making unglued evaluation and the reference compute through
  lifts too.
- No action on F5 or F6.

## Questions for Matt

- **D3030:** Should "glued and unglued evaluation agree on what's equal"
  (the `proof_equivalence` matrix) be a rule for every evaluator change, so
  that any divergence like F3 is a bug to fix rather than an accepted
  extra? The kernel checks glued, so this rule is what keeps its verdicts
  independent of gluing. [rec: yes]

## Tickets to file

One lane, **Opus** (`core/value.rs`, the kernel path), about 60 min:

- F1: correct `computes_field`'s doc and `match-call-field.md` §1 and §4
  (kernel reached; why it's sound).
- F2: `FieldOf`'s `J` branch pushes `JProof`. Add a unit test with a
  call-valued `Eq` field.
- F3: stuck flag `true` in `unfold_field_for`. Add a lift-leaf unit test.
- F4: unit tests in `crates/core/tests/it/glue.rs` (gluing off, opaque
  hidden and visible, `J` stuck and computing). Add `proof_equivalence`
  matrix terms for applied fields of calls (stuck in its own tree, a leaf
  that is a call, a lift leaf). Tests:
  `task test:one -- glue`, `task test:one -- proof_equivalence`, the three
  new examples.

Backlog, not a lane: the 1 Nov review's §4.1 (guard-based restore of
`Machine::glue` in `check.rs`, `inert.rs` and `reference.rs`), Sonnet, about
30 min, if the LSP reuses a session after a panic.
