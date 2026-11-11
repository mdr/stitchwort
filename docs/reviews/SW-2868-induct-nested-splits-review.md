# SW-2868 review: nested splitting in `f.induct`'s lifted-match split

Paper review (Opus, D2364), 11 Nov 2026, of `lane/SW-2868` at 0374c7a44.
Nothing was built or run. Line numbers are in
`crates/elab/src/equations/induct.rs` as of that commit.

**Verdict: merge as is. No must-fix.** Every term the generator builds is
checked by the kernel, and the hidden `%split`/`%apart` definitions go
through `define_group`, so the change can't make the system unsound. The
questions are whether a statement is wrong or unhelpful, and whether a
generated term can be *refused* by the kernel rather than skipped. I found
no refusal path for any shape a user can reasonably write. One contrived
path exists and is pre-existing (SHOULD-FIX 2). Two SHOULD-FIXes widen
coverage, and there is one missing regression test.

## (1) What each generated `f.induct` states: OK

- The case types come from the equations' binders (`Case::binders`, which
  `induct_case_type` reads). This lane doesn't change them. Cases still
  match the function's alternatives one for one and in order, and their
  hypotheses are exactly the equations'. The lane changes only the
  *proof*, plus which shapes get one. A case can't be stronger or weaker
  than its equation.
- Placing alternatives is right. At each node, `alt_descend` (1374) takes
  the first alternative in written order (`alts` sorted by `choice`, 1062)
  whose pattern agrees with the splits so far. It splits further only
  while that alternative still has an unsplit constructor (`unsplit`,
  1973), so every leaf is the place where the program takes that
  alternative. At a leaf, every earlier alternative disagrees at some split
  constructor (that is what `agrees` returning false means). So for a
  catch-all, `clash(root, p)` always finds the difference, because the
  root's `node_term` carries every split constructor. For an alternative
  that follows one it overlaps, the difference lies under one of its own
  variables. Within the shapes it accepts, the design proves every
  hypothesis it is given.
- For a user, the new cases read well and are directly usable:
  `x % 3 ≠ 0 → x % 3 ≠ 2 → motive …` (omega takes them), `(n: Nat) →
  rest.head = Some n → n ≠ 0 → …`, and `rest.head = Some (None, c)` with
  the inner field named. The example's `weighCounts` actually needs
  `notZero`, which shows the hypothesis is the useful one.
- NOTE: guarded alternatives in a lifted `match` are placed as if
  unguarded (`agrees` ignores guards). This is harmless today: the guarded
  alternative's own `c = True` hypothesis has no `→`, so `hyp_parts`
  (2084) returns `None` and the whole `f.induct` is skipped. It works
  because of that accident, though, not by design. A guarded alternative
  should get its own skip reason before it reaches `alt_leaf` (see
  SHOULD-FIX 2).

## (2) The claim that SW-1073's shapes give identical terms: OK (plausible, and the evidence is real)

- I traced the three SW-1073 shapes through the new code:
  - **One constructor per alternative, all leaf fields.** `alt_leaf` with
    `nodes = [root]` and no kids: `vs` are the field variables and
    `proof = Var(eq)`, so the `remap` is the identity on de Bruijn indices.
    The old code produced `lams(names, sub)` with the same body.
  - **Nested one-constructor patterns.** The old `nested_descend`
    processed a FIFO work list. The new `unsplit` scans nodes in creation
    order, then fields. Both visit fields breadth-first, so the `%split`
    calls and `node_proof`'s `J` chain come out in the same order.
  - **Catch-all.** The let types (old `ty.shift(k+1, j)`, new `remap`) are
    the same. `got`'s transport goes along `Var(eqn)` in both
    (`proof.shift(under)` with `proof = Var(0)` at the root). The data
    arguments are shifted by the same amount.
- The only visible difference is binder names: field names plus `e`,
  where the old code used the alternative's own names. `hash.rs` leaves
  binder names out, and `def_hash` includes proof bodies, so unchanged
  snapshots do show that the terms are the same.
- NOTE for the verifier: `hash_stability` runs `tier_sample`
  (`share`, `hash_stability.rs:270`), which takes every fourth example in
  the lane and merge tiers. Run it with `EXAMPLES` naming
  `function-induct`, `function-induct-catchall`, the other
  `function-induct*` files and `match-induct`, so that "unchanged" isn't
  just "not sampled".

## (3) The literal limit and other limits: OK

- 64 matches equations' `LITERAL_CAP` (`equations.rs:147`). The two
  bound different things (the size of a literal here, the number of
  hypotheses there), but with both at 64 the worst case stays polynomial.
  A literal `k` costs `k + 1` splits on its path. The worst catch-all has
  ≤ 64 hypotheses at ≤ 65 leaves, and each hypothesis's proof embeds a
  copy of the leaf's `node_proof`, a `J` chain up to 65 deep. That is
  O(10^5) `J` nodes in a pathological table, and a few thousand in
  realistic ones.
- NOTE (cost, no action needed now): `proof` is copied into every let at a
  leaf (`proof.shift(g, under, 0)`, in `alt_refute`), and `sub` is copied
  into every leaf an alternative takes (`alt_leaf`'s `remap`). The design
  says the proof is "made once and moved to every place it takes"; it is
  *made* once but *copied* at every leaf. Lifted matches nested inside an
  alternative multiply these copies. Binding `proof` once per leaf with a
  `let` would remove the first factor. Measure before acting (Matt's
  "profile before optimising").
- `> 64` and character literals skip with a reason (`big_literal`, 1840;
  the generic "isn't a constructor applied to …" message). `Term::Nat` on
  a non-`Nat` type is caught by the `pd != data` / `fd != pd` checks.
  OK.

## (4) The skip at a type parameter with variables: a symptom, not a necessity (SHOULD-FIX 3, not blocking)

- The rule is needed *for the discriminator as it is stated today*:
  `%apartN` is written over the root type's parameters,
  `{a} (y: Option a)`, and a `Case` on `Some`'s field, whose type is `a`,
  isn't a `Case` on a data type, so the kernel refuses it. Choosing the
  closed instance when there is one, and skipping otherwise, is correct.
  It also turns the old `Tree::refute` refusal into a skip or a success.
  `generic_path` (2903) checks exactly that each field on the path is
  declared at the next data type. That is the right test.
- It is not a fundamental limit. State the definition at the instance,
  abstracted over the instance's free variables: for `Option (Option a)`,
  `{a: Type} (y: Option (Option a)) → Prop`. There `Some`'s field has type
  `Option a`, a data type, and the same `build` works unchanged.
  Implementation: collect the free variables of `args` (closed under
  their types' dependencies), take their types from the context, pass
  them as implicit binders, and apply them at the use site. The
  proposal's suggested lift ("a projection per step and a discriminator
  on the field's own type") is heavier than needed. This is what the
  lane's finding "Some None then catch-all at Option (Option a)" calls
  for. File it as a follow-up, rated small to medium.

## (5) Paths where the kernel would refuse instead of skip: none reachable in practice; two defensive SHOULD-FIXes

Each kind of term was checked against its type:

- `node_proof` (2026): the motive `z e ⇒ target = C(…z…)` generalises a
  field. That is well-typed only if no later field's type mentions this
  one, and `alt_descend` checks exactly that before splitting (1394,
  `mentions(j - 1 - k)`, the right index). OK.
- `alt_refute` for a variable: `trivial : disc (node_term)`. `disc`
  follows `mine`'s constructors along `path` (`clash` descends only where
  the constructors agree), so it reduces to `Unit` by iota. `J` along the
  hypothesis's last equation then gives `disc p ≡ Void`. OK. For a
  catch-all: `J m1 (λw.w) proof : disc root → disc scrut`, applied to
  `trivial`. OK.
- Literals: the equation states `e = 2` while the leaf gives
  `e = Succ (Succ Zero)`. This needs the kernel to treat a literal and its
  constructor form as convertible, which the passing `score` and
  `literal` cases show it does.
- **SHOULD-FIX 2 (defensive, pre-existing in `induct_catch_all`):** for a
  catch-all, `alt_refute` (the `None if alt.pat.is_none()` arm) *assumes*
  that the hypothesis's left side is the scrutinee, without checking. If
  it isn't, `J (y e ⇒ disc y) got h` is ill-typed and the kernel refuses.
  The only way I found to reach this is a catch-all after a *guarded*
  alternative on a `Bool` scrutinee whose guard is itself a `Bool`
  (`match flag with | True if c => … | _ => …`). Its `NotGuard`
  hypothesis ends in `c = True`, which `hyp_parts` reads as "about the
  scrutinee". Today the guarded alternative's own leaf skips first, so
  the term never reaches the kernel. Two cheap fixes, either of which
  makes refusal impossible by construction: check that `lhs` is
  `x.scrut` at that depth, and skip otherwise; and skip a lifted `match`
  that has a guarded alternative, with its own reason.
- `rd != depth` is now checked for every lifted `match` (1068), where
  before it was checked only for nested patterns. This is not a
  regression: the old flat path `lams(names, sub)` was well-typed only
  when `rd == depth`, so that case never generated.
- Pre-existing, not from this lane: 2021 day 16's `readPackets` is
  refused on `main` (`E-NOT-A-FUNCTION`). `a_projects_inducts` is
  `#[ignore]`, so no tier catches this. It doesn't break a user's build
  (equations record a refusal as a skip, `equations.rs:2483`), but it is
  a generator bug. File it with the definition as the reproducer. Its
  recursive calls sit in a scrutinee and under a condition, much like the
  next finding.

## (6) The new example's theorems: OK

- `collectKeeps`: `length printed ≤ length (collect step printed fuel)`.
  This is true, and its cases take exactly the new nested-`Option` split
  (`None` uses `ih`; `Some value` adds one element).
- `scoreLe`: `score xs ≤ 2 * length xs`. The literal cases and the
  catch-all with `notZero notOne` are all there.
- `weighCounts`: `length xs ≤ weigh xs + 1`. This is true (every element
  after the first adds at least one). The `Some n` case needs the
  generated `n ≠ 0`, so the overlap hypothesis is shown to be useful,
  not just present.
- Each theorem's name says what it proves, and each uses its `f.induct`
  with the statement as written. The test file's new assertions
  (`literal`, `overlap`, `closed`, `generic` skip, `nestedDeeper`,
  `nestedMulti`) match the claimed cases.
- SHOULD-FIX (test): the commit says the `generic_path` check "guards
  `Tree::refute`, which the kernel refused there before", but no test
  covers that path. `generic` and `closed` exercise only `alt_refute`.
  Add a definition whose *own rows* overlap through `Some`'s field: a
  closed one (`Option (Option Nat)`, made) and a generic one (skipped
  with the parameter's reason).

## (7) Other findings

- **SHOULD-FIX 1 (coverage):** `alt_refute` uses only the *last* equation
  of a hypothesis that has several (`hyp_parts` treats the earlier
  equations as "variables"). `Tree::refute` already tries each equation
  until one clashes (the `for e in 0..eqs` loop). As a result, a single
  scrutinee of pair type with `| (0, 0) => … | (a, b) => …` is skipped: at
  the leaf where `a` is `Succ`, `b` isn't split and the code looks only
  at `b = 0`. Do the same as `Tree::refute`: find the equation whose
  variable's value clashes, and take that equation's `J`. This is sound,
  since any one false equation refutes the conjunction.
- **Lane finding: `transmissionBits` and `sumMagnitudes` silently get no
  `f.induct`.** This should be filed, and it is more than a missing skip
  reason. A recursive call in a lifted `match`'s *scrutinee* is a real
  recursive call, and an `f.induct` without its IH is weaker than the
  function's recursion, so users can't prove those functions'
  properties. Meanwhile the user is told the definition "doesn't call
  itself" (`E-UNKNOWN-NAME` with a note), which is false. At the very
  least, record a skip reason now; the real fix is IHs for calls in a
  scrutinee.
- **Lane finding: `Some None` then a catch-all at `Option (Option a)`.**
  See (4): lift it by abstracting the instance's free variables.
- NOTE (process, for the orchestrator): the proposal records
  `check --no-cache Aoc.Year2024.Day17` (2.0 s). A one-day check is small,
  but it is the kind of `aoc/` check the lane rules exclude.
- NOTE: the "skips checked again" paragraph in the proposal checked one
  definition at a time, not by sweep, and says so. That is honest. The
  daily tier's sweep will re-measure.

## Summary

| # | Verdict |
|---|---|
| 1 Statements | OK (cases are the equations'; placement follows the `match`'s semantics) |
| 2 Identical terms for SW-1073 shapes | OK, plausible; verifier should run `hash_stability` with `EXAMPLES` naming those files |
| 3 Literal limit 64 | OK; NOTE copies of `proof`/`sub` per leaf |
| 4 Type-parameter skip | Needed for the current `%apart`; SHOULD-FIX 3 (follow-up): abstract the instance's free variables |
| 5 Kernel refusals | None reachable; SHOULD-FIX 2 (defensive): check a catch-all's hypothesis is about the scrutinee, skip guarded alternatives |
| 6 Example | OK; SHOULD-FIX: a test for the `Tree::refute` instance path |
| 7 Other | SHOULD-FIX 1: try every equation of a hypothesis; file `readPackets` refusal and scrutinee-call IHs |
