# Review: export validators read the one view (SW-3948)

Fable, 18 Nov 2026. Reviews branch `lane/SW-3936` at `26cd1c836` against
`main`: SW-3936 (the export validators read `erase::def_telescope` and are
checked under the definition's transparency set, glued; js `boundary`
forces a type first) and SW-3935 (`retype_def` checks a signature glued).
It follows [SW-3911](SW-3911-glued-kept-types.md) and
[SW-3931](SW-3931-glued-kept-types-diff.md).

Done by reading the diff and the code around it, and by running the lane's
release binary on four small files, extracting them to JavaScript and
calling the wrappers under node. Nothing was built and no test was run: the
lane's test results, and its claim that no hash moved, are its own report.

## Verdict

**Merge as is.** No required fixes. The four questions all come out in the
lane's favour; three small findings (§5) are optional or older than the
lane.

## 1. Can a validator be accepted that doesn't decide the real proposition?

No.

- **Which proposition.** `add_validator` takes parameter `param`'s type
  from `def_telescope`: `Def::ty` evaluated under `Def::transparent`. That
  is the type `admit_group` checked the body against, so it is the
  proposition the body assumes at that lambda. The view `main` used (every
  opaque definition hidden) is the same term evaluated with fewer
  unfoldings, so where both show a parameter, its two types are equal
  once the set is unfolded.
- **How the decision is compared.** The earlier parameters are bound in
  order to the telescope's types, so the decision's variables are the
  telescope's levels, and the decision is checked against `Decidable P`
  built from that same value. Nothing is compared across two views.
- **Which set.** The check runs under `Def::transparent`, the set the body
  was checked under. Unfolding an opaque definition is always sound:
  `opaque` hides a body, it doesn't change what is true. So a decision that
  checks under the set has type `Decidable P` in the full theory, and its
  `sound` field gives the proof the body wants. The runtimes run with every
  body visible, so they compute what the kernel checked.
- **Modes line up.** `def_telescope` makes the telescope's glued calls
  under the set, with gluing on and `Machine::kernel` set (it is called
  inside `in_kernel_modes`), and the check then runs in those same modes, so
  `Kept::fits` lets it use them; any other reader recomputes. `glue.set(true)`
  without a put-back is right: `in_kernel_modes` restores the caller's mode
  on every path.
- **The elaborator's set** is `transparency_set(id, &[id])`, not
  `Def::transparent`. They are equal for a final definition: the group
  argument only feeds the `E-UNFOLDING-GROUP` check, and the set is built
  from the `unfolding` list alone. If they ever differed, the kernel would
  refuse the decision, not accept a wrong one.

**Nothing accepted before is refused,** resources aside. The hidden view's
parameters are a prefix of the new view's. A parameter erased in the hidden
view is erased in the new one (a proposition stays one when unfolded, and a
visible type former stays a type former), and a comparison that succeeded
with a definition stuck succeeds with it unfolded.

Probes, all behaving as they should:

| File | Result |
|---|---|
| `Rest n` hides `[ok: n ≠ 0] → (m: Nat) → [ok2: m ≠ n] → Nat` after a visible `n` | both checks made; `f(0n, 2n)` refused for `n != 0`, `f(6n, 6n)` for `m != n`, `f(6n, 2n)` is `3n` |
| precondition `Good n`, `Good` opaque and unfolded by the export | accepted; `g(0n)` refused, `g(5n)` is `2n` |
| the same without `unfolding Good` | `E-EXPORT`, as on `main` |
| parameter of type `Code` (opaque, unfolded, `Nat` inside) | refused: "`Code` can't cross the JS boundary yet" |

The last is `boundary`'s `force` at work: the caller's set is empty, so the
call is recomputed there and stays stuck. That is the safe answer.

## 2. Do positions line up?

Yes. `Validator::param`, `exportable`'s `Check::position` and
`param_positions`, and the definition's erasure mask (`erase::of_def`) all
index the one `def_telescope`. The wrapper compiles a decision with an
environment of `position` entries, proofs erased and data decoded as
`v{i}`, which matches the order `add_validator` bound them in. The first
probe shows it with hidden parameters on both sides of a check: the second
check reads `v2` and `v0`, and the call is `f(v0, v2)`.

Before this lane the two sides read different views (js the new one since
SW-3933, the validators the hidden one). Where both showed a parameter the
index agreed, so the only symptom was the refusal the lane fixes.

## 3. Is gluing `retype_def`'s signature check safe?

Yes, by `declare_def`'s argument, word for word. The lines are the same
three: gluing on around `check_type`, put back before the `?`. The values
made are dropped with the context, and the kept value comes from
`kept_type`, glued already. The term that is stored and hashed is rebuilt
from the input or read back with `quote`, which writes unfoldings, so it is
the same term either way. The transparency set stays empty, as in
`declare_def`.

## 4. Is `docs/core.md`'s list of glued checks exactly right?

Yes. `check.rs` switches gluing in seven places, and the sentence names
those seven: `declare_def`, `retype_def`, `assume`, `admit_group`,
`set_run_body`, `add_validator`, `kept_type`. The `Refl` clause matches the
code (the type is evaluated unglued under the definition's set; the check
itself is glued). The readers' bullet is right to add the validators and to
say a validator's position is its argument's position.

## 5. Findings

None blocks the merge.

1. **`add_field_validator` is the one validator check left unglued and
   under the empty set.** That is correct, as a record's field types
   belong to no definition, and core.md's "(`add_validator`)" is literally
   accurate. A reader could take "an export's validators" to include
   record fields; "a parameter's validator" would remove the doubt.
   Optional wording.
2. **Older than the lane: `add_validator` asks only that the parameter is
   erased, not that it is a proof, and doesn't refuse a second validator
   for one parameter** (`add_field_validator` refuses a second). Neither is
   a soundness problem: each validator is checked, js takes the first, and
   `exportable` refuses a type parameter before it looks for one. Worth a
   small ticket: refuse both as `E-MALFORMED`.
3. **The elaborator rebuilds the transparency set** where it could read
   `Def::transparent`. Equal today (§1); reading the stored set would make
   that true by construction. Optional.
