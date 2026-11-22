# SW-4642 review (Opus): a proof stuck past its own case tree kept as the lemma's call

Branch `lane/SW-4642`, commits `b3cd1a3db` (code, example, pins, perf log) and
`e950e543f` (board). Read-only paper review; no builds or tests run. Line
numbers are on the branch.

## Verdict

**Merge with changes.** It's sound, and the kernel's evaluation really is
unchanged. But conversion can now fail in the elaborator where it used to
succeed. The new arm hands on a theorem call whose unfolding is not itself.
Once a `J` (or, through `FieldOf`, an application) is put after that call,
conversion can no longer unfold it, and one elaborator path still builds the
unfolded shape for the same term. The elaborator would then accept less.
This needs a real but uncommon setup (finding 1). Fix it before merging,
or merge and file the fix at once. The orchestrator decides which.

## 1. Elaborator only? Yes

- `names_folded_fields` is `glue && !kernel` (`crates/core/src/value.rs:2538-2540`).
- `Machine::kernel` is set to true only by `machine::in_kernel_modes`
  (`crates/core/src/machine.rs:80-87`) and `determined.rs`'s `KernelModes`
  (`crates/core/src/determined.rs:158-175`). Every public admission function
  in `crates/core/src/check.rs` runs inside `in_kernel_modes`: `define_def`
  2428, `define_group` 2448, `declare_def` 2627, `assume` 2770, `retype_def`
  2835, `admit_trusted_*` 3776-3908, the data declarations 3180-3449 and the
  validators 4757/4821. The kernel's later `glue.replace(true)` for bodies
  and signatures (`check.rs:2594`, 2656, 2739, 2813, 2855, 2899, 4777)
  happens inside those calls, with `kernel` still true. So the kernel's
  checking and conversion never take the arm.
- The public `check::infer`/`check`/`check_type` (`check.rs:246`, 523, 874)
  don't set the flag. When the elaborator calls them they can take the arm,
  but that doesn't matter for trust: what counts is the admission, and that
  re-evaluates the term in kernel mode.
- The kernel accepts the new terms. The arm builds
  `Neutral(Head::Def(id), spine)` from the frame's own `call` spine
  (`unfold_for` 2870-2884, `unfold_field_for` 2918-2938): all the
  arguments, implicit ones included. Read back, it's `id args`, whose type
  is the theorem's type instantiated, convertible by delta with the type of
  the unfolding it replaces. Kernel evaluation of `J m b (id args)` reaches
  the same unfolded value as before.
- Other places that turn glue on without setting `kernel` (`erase.rs:203`
  `in_own_view`, `inert.rs:90` `candidates`, `reference.rs:1422`) take the
  arm when called from the elaborator. `in_own_view` says its answers must
  not depend on the caller's modes (SW-3916), and the arm adds a dependence
  on `kernel`. It only changes the shape of a stuck proof or a transport,
  never how many `Pi`s a type shows, so telescope lengths and erasure masks
  are unaffected. Low risk, and the same is already true of
  `FoldedField`/`eta_fields`. Noted, not a finding.

## 2. Correctness in the elaborator

### Finding 1 (medium): the call with a `J` or application after it can't be unfolded by conversion, and `ReplayElim` still builds the unfolded shape

Before this change, a theorem call reached a frame only when it was stuck
in its own case tree, and then the call *is* its unfolding. So
`Neutral(Def(T), args ++ [J m b])`, which `JBase` builds by pushing the `J`
onto the neutral's spine (`value.rs:2016-2040`, 2132), was a normal form.
The new arm produces the same shape for a `T` whose unfolding `U` is a
*different* stuck neutral. Conversion only opens a folded call in
`conv_step`'s `Stage::Unfold` (`value.rs:4130-4157`), which needs
`is_folded` (`value.rs:2940-2962`): either a bare call (`folded_call`,
`spine.len() == arity`, 2968-2973) or a call followed only by projections
(`is_call_field`, last elim a `Proj`). A call followed by a `J` or an
`App` is neither. So `(T args)+J` and `U+J` fall through. Their heads
differ, `opens_by_tree` is false for a theorem (`!folds`, 4654-4668), and
the result is `push_eta`, which gives false for non-functions. Before the
change both sides were `U+J` and compared equal.

One path in the same mode still produces `U+J`. `Frame::ReplayElim`
(`value.rs:2279-2320`) handles a `J` replayed onto a solved metavariable:
`unfolded = unfold_folded(value)`, which runs `T`'s tree directly rather
than through `Frame::Unfolding`, so it returns `U`, and `J` is pushed onto
`U`. The `Proj` arm right above it was given the matching "keep it as the
call's" rule (2297-2304, "as `Frame::FoldedField` keeps it"). The `J` arm
wasn't.

**Failure scenario.** Take a term `J m b ?p` whose motive's result is data
(a `rewrite … at v` transporting a value, or a cast), with the proof `?p`
filled later, by an `{auto}` argument or a hole solved by unification, to
`T a`. `T` is a lemma whose body computes past its case tree and stops on
a variable or a projection, like `stepIs` in the new example. The copy of
the term evaluated before `?p` was solved replays to `U+J`. A copy
evaluated after it's solved goes through `JForced` → `unfold_for` → the new
arm and gives `(T a)+J`. Unifying or converting the two (a goal against a
hypothesis, or an expected type against an inferred one) now fails with a
type mismatch where it used to succeed. Positions where conversion ignores
proofs (constructor proof fields, a data type's `Prop` parameters, inert
definition arguments) are safe. The exposure is transports of data and
proofs compared by shape at non-inert positions.

The same gap opens on smaller routes, each needing a less common setup:

- **Two calls that unfold the same.** `(T a)+J` against `(T' a')+J`, or
  against `(T a2)+J`, where `a` and `a2` differ only in an argument `T`
  ignores, used to be equal through `U` and are now compared spine by
  spine (`spine_pairs`, 4523-4567). This is the comment's own analogy
  ("as one stuck in its own tree is"): that case already behaves this way.
  It's lower risk, but the analogy doesn't make it free.
- **Glued unfoldings read unglued.** A glued `Kept` unfolding serves a
  reader with glue off (`Kept::fits`, `value.rs:327-339`: `m.glue ||
  !glue`). So an unglued elaborator reader can find `(T a)+J` inside a
  stored unfolding while its own evaluation builds `U+J`.
  `same_unglued` (`crates/elab/src/check.rs:7241`) and `decide_unglued`
  (`crates/elab/src/auto.rs:1221-1246`) re-evaluate read-backs, which is
  consistent within itself. I didn't trace every unglued reader, so I
  haven't settled this one.
- **`FieldOf`.** For a field of a theorem call (`(lemma x).mp h`,
  `unfold_field_for`), the arm hands `FieldOf` a call that passes its
  stuck-in-own-tree test (`s2.ptr_eq(&call)`, `value.rs:2197`), because the
  arm reuses the frame's `spine` `Rc`. So the result is now
  `(lemma x).mp h` (spine `args ++ [Proj, App h]`) instead of `U.mp h`.
  Conversion can't unfold that either, since an `App` comes last. The
  result is usually a proof, where conversion ignores it, but the same gap
  applies. This interaction isn't mentioned in the comment. I think it's
  intended (it's what saves the read-back size), but it should be said.

**Suggested fix.** The robust option: in `conv_step`'s unfold stage (and
the unifier's matching rule, which I haven't read), treat a neutral whose
head is a folded definition applied to exactly `arity` arguments, followed
by any `J`/`Proj`/`App` elims, as unfoldable. Unfold the prefix with
`unfold_folded`, then replay the suffix. That closes every route above,
whatever mode made each side, and makes the comment's "Conversion unfolds
it again" true for the shapes the arm actually produces. The narrower
option: mirror the arm in `ReplayElim`'s `J` arm, keeping the `J` on the
innermost theorem call whose run ends stuck past its tree. That fixes only
the replay route, and it needs a helper because `unfold_folded` follows
chains of calls.

**Test.** Either fix needs a small elaborator test like the scenario: a
data transport whose proof is a hole solved to a past-tree-stuck lemma,
compared with the same transport written with the lemma directly. Per
D3608, show it failing on the branch as it stands. I haven't built this
reproducer, so the failure is reasoned from the code, not observed.

### Things checked and fine

- **The case "stuck straight away" (`value.rs:2151-2153`).** It's the same
  value shape with the same `Rc` spine, so every `next` frame already
  handles it: no new loop. A `next` that might unfold again (`Scrutinee`,
  `JForced`, `ProjForced`) isn't reached, because `unfold_for` always
  pushes the `…Ready` form (`JReady`, `ScrutineeReady`, `ProjReady`/
  `FoldedField`, `LiftReady`, `CallField{unfolded: true}`).
- **Record eta on a proof scrutinee.** `branch` → `eta_fields`, non-`Call`
  path (`value.rs:2600-2613`). `named` is true both before and after (the
  forced value is a neutral that isn't an unknown), and the base is the
  unforced `T a` because `folded_call` holds. So the fields are
  `(T a).i` either way: no change.
- **Fields (`FoldedField`, 2059-2065).** A projection of the call gives
  `(T a).i`, the same as before. With the non-eta `ProjReady` it's now
  `(T a).i` instead of `U.i`. That form *is* `is_folded`, so conversion
  bridges the two.
- **Matching's blockers.** `cases.rs` `blocker` (3558-3616) and
  `Finder::walk`/`chain` (2930-2950, 3000-3015) call `unfold_folded` on any
  folded call they meet, so they still see `U`. `matching.rs` `blocker`
  (1480+) looks for unknowns in read-backs. A theorem's body is closed, so
  every unknown in `U` is in `T`'s arguments, and the read-back of the call
  shows it.
- **`rewrite`'s `Refl` test.** `U` is a non-meta neutral, so not `Refl`;
  the `J` is stuck either way. When an argument later becomes concrete, the
  term (now `J … (T a)`) is evaluated again and unfolds again.
- **Metavariables solved through the unfolding.** Excluding an unknown head
  keeps the one case where the unifier could solve through `U`. For an
  unknown deeper in `U` (stuck on `f ?m` with `f`'s head a `Def`), the
  call is *better* than `U`: a bare `T a` unfolds afresh once `?m` is
  solved, while a stale `U` wouldn't. The `J`-suffixed form is no worse
  than `U+J` was.

## 3. Determinism and caches

- The arm is a pure function of the value and the modes, so it's
  deterministic.
- `CallMemo` (`value.rs:3973-4016`) is keyed by the addresses of glued
  `Value::Call` unfolding cells, and a theorem call is a folded `Neutral`,
  never a `Call`, so it isn't affected. `TreeMemo` (4817) is per comparison
  and hashes values, so new shapes just hash differently.
- `Kept` unfoldings record `glue` and `kernel` in their modes (`Modes::now`,
  `fits`, `value.rs:300-339`). The kernel never uses an elaborator-made
  unfolding, and the elaborator never uses a kernel-made one. The one
  crossing that's allowed (glued made, unglued read) is in finding 1.
- The check cache's compiler fingerprint includes the build
  (`crates/driver/src/check_cache.rs:82-87`), so elaborated output cached
  before this change isn't replayed after it. No cold-against-cached hash
  split.
- Pins: three `Float` native pins moved (`crates/core/src/pins.rs:125`,
  129, 161). The definitions are unchanged in source; their hashes cover
  proof terms they depend on (the log names `Int.divFloorNonneg`'s `J`).
  That's plausible, but I didn't trace the dependency. The verifier's pin
  test confirms the new values.

## 4. The condition

- **Excluding unknowns:** right, and consistent with `FoldedField`
  (2063), `eta_fields` (2602, 2617) and `ReplayElim`'s `Proj` (2302). An
  unknown head is the one stuck value that may still be solved through the
  unfolding (`needs_forcing` above already handles a *solved* one).
- **A variable head** (`Head::Var`, with any `Apart`): the main intended
  case (the new example is stuck on `pos`). Fine.
- **An axiom head or a sealed or opaque definition** (no body, hidden,
  a stand-in for a failed declaration, a member of the group being
  checked): a neutral `Def` head that doesn't fold, so the call is kept.
  It's equal by unfolding, the same as for a variable. Fine. The theorem
  `id` itself always has a body here (`folded_call` and `unfold_for`
  require `body_seen`), so a stand-in can't be `id`.
- **`Head::Quot`** (a stuck `Quot.lift`, or `Quot.sound`/`Quot.ind` as a
  proof): kept as the call. I found no rule that takes apart a `J` on
  `Quot.sound`, so it's equally stuck. Fine.
- **`g.def(id).theorem`:** dictionaries (`def.fold`) are rightly left out.
  `folds` (2834-2837) is false while a program runs, and glue is never on
  then (`machine.rs` doc), so the arm can't fire during a run.
- **Unfolding chains.** A theorem whose body is another theorem's call
  goes through the `folded_call` arm (2154) first, which pushes a new
  `Unfolding` for the inner call. So the arm keeps the *innermost* theorem
  whose own body is stuck past its tree, not the name written at the use
  site. That's fine, but it's worth one sentence in the comment, since the
  log says "the call is what was written".

## 5. The new example

`examples/accept/proof-unfolding-kept-folded.sw` does reach the arm.
`stepIs`'s tree takes the record `match` on `s` by eta (rule 2: no stuck
`case`). Its projection `let` is `(stepParts k pos).0`, which unfolds
through `unfold_field_for` to the variable `pos`. Then `rewrite notZero at
stepped` is a `J` on `pos`, which isn't a `case` in `stepIs`'s tree. So
`stepIs`'s unfolding ends as a `Var`-headed neutral past its tree, and each
`rewrite stepIs …` in `threeSteps` meets the arm. The lane's measurement
(`threeSteps` 23,341 to 18,019 steps, largest read-back 87 to 26 nodes)
agrees.

The example passed before the change too ("What checks is unchanged"). So
what distinguishes it is the hash snapshot, which records term hashes, not
a readable claim. That's acceptable. A unit test showing that `b1`'s value
reads back as `stepIs s n1 k pos s1` would say it directly. Optional.

## Smaller points

- The comment at `value.rs:2167-2173` says "Conversion unfolds it again
  ([`unfold_folded`])". That's true of the bare call `next` receives, but
  not of the `J`- or `App`-suffixed values `next` usually builds from it
  (finding 1). Reword it, or make it true with the conversion fix.
- The comment should mention the `FieldOf` interaction: the reused `spine`
  `Rc` makes `FieldOf` treat the call as stuck in its own tree.

## What I couldn't settle

- Whether the elaborator's unifier (`crates/elab/src/unify.rs`) handles a
  `J`-suffixed theorem call against the unfolded shape any better than
  `conv` does. I didn't read it.
- Which unglued elaborator readers, if any, take glued `Kept` unfoldings
  that hold the new shape and compare them with values they evaluated
  themselves.
- Whether the reproducer in finding 1 can be built in today's surface
  language (a proof hole in a data transport solved to a past-tree-stuck
  lemma). The code path exists. I haven't confirmed a program reaches it.
