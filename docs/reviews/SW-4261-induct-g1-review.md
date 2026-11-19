# SW-4261 review: `f.induct` for a guarded arm a later arm partly overlaps (G1)

Reviewer: Opus (SW-4294), 19 Nov 2026. Branch `lane/SW-4261`, commit
e9edd88f3. Probes were checked with that worktree's release binary; the
probe files are listed at the end.

## Verdict

**Merge.** The fixes below are optional and small (one error message, one
duplicate file). Nothing affects soundness or what the principle states.

## Soundness and trust

- Every new term goes through the kernel. `f.induct` uses the existing
  `define_group` path. The new `%fieldN` projections are declared with
  `declare_def` and `define_group`, with the same flags as `%apartN`.
  There is no axiom, admit or unchecked path: `stitchwort axioms` on
  `sameWithout` reports "no axioms are used", and the diff has no
  `admit`, `axiom` or `unsafe`.
- **The statement is unchanged by construction.** The case hypotheses come
  from the existing `Hyp::Overlap`, read off `f.eqK`. The lane adds only
  their proofs, where it used to skip. The probes confirm this by ascribing
  the expected type with `let t: … := notArmJ`:
  - Each was accepted: `o = Some a → ¬(a > 10)` (`sumBig`), `q = P a b →
    ¬(a > b)` and `… → ¬(a = b)` (two guarded arms on one pattern), the
    record pattern `p = { x, y } → ¬(x > y)`, `k = Comma → ¬(…)` (a nullary
    constructor in the guarded pattern), and `ys = [y, ..ys1] → ¬(x ≠ y)`.
  - **Variables are taken from the right scrutinee.** In `two` (p8), the
    guard reads the whole second scrutinee: `[x, ..xs], ys if
    List.length ys > x`, then `xs, [y, ..ys]`. The hypothesis accepted
    `¬(List.length [y, ..ys] > x)` and refused `¬(List.length ys > x)`.
- **No vacuous or over-strong principle.** A case's hypothesis is a premise
  the principle's own proof discharges at every leaf. A hypothesis that was
  too strong would fail in the kernel, not yield a weaker theorem. A
  stronger use was also refused: `sdWrong` (p3) drops the
  `ys = [y, ..ys1]` premise (`∀ y => ¬¬(x = y)`), and it is a type
  mismatch. `sdHead` applies the hypothesis properly and checks.
- **J motives and levels.** I traced the chain by hand. It is built
  innermost-first for `e = eqs-1 … 0`. Each motive maps:
  - the variables of earlier equations to `from_x` (projections of the
    leaf's values),
  - those of equation `e` to `from_y` (projections of the motive's `y`),
  - later ones to themselves.

  So the base of each `J` is the previous `J`'s result type. The innermost
  base is the condition at the leaf's values, refuted by `λh. void_here`.
  The outermost result is `stated → Void`. The levels are consistent:
  - `top = depth + vars + eqs + 1` and `under = top + 2` (the motive's
    `y` and `e`).
  - The fact is shifted by `top + 1 - at`, since it is used under `h`.
  - In `bool_clash`, `J (y e => y = notX) fact h : x = notX` uses the
    `c = notX` / `c = x` orientation the guard split gives.

  The kernel would catch any slip, and every probe form checks.
- **Projection defaults.** `project` defaults each step to the leaf value's
  own field (`ctor_of` on `x`). So at `y = x` each step reduces to the
  value's field, and at `y = p` to the pattern's variable, as the comment
  says. Parameters along a nested path are carried (`next`). For example,
  `List (Option Nat)` goes through Cons field 0 and then Some field 0
  (`sumBig`, p2), with an implicit type parameter (`dropWhileP`).
- **`facts.rev().find`.** On one path through the tree, a row's guard is
  split at most once. A leaf of row K where J's patterns match lies under
  J's `else` side, so the innermost fact for `j` is the failed one at these
  values. The constructor-apart route is tried first (`found`). So
  `refute_guard` only runs where J's patterns can match.
- **`¬Q`, `≠` and `Not` guards** (the lane's open question).
  `void_here = h fact`, with `h : ¬Q` and `fact : Q` (from `notNotOf`). The
  probes `skipDiff` (`if hne: x ≠ y`) and `sd` (`if hne: ¬(x = y)`), in p1
  and p3, build and are used. So the kernel does unfold `Not` here.
- The `Bool` forms `a == b` and `!(a == 0)` (`eqb`, p3) and `&&` chains
  (the examples) build.

## Completeness

The probes that built:

- a nullary constructor head with the guard on the tail (`g`);
- `Succ (Succ n)` against `Succ m` (`h`);
- `¬Q` and `≠` guards;
- a parametrised nested path;
- an implicit type parameter;
- a guarded bare variable (`k`);
- two guarded arms on the same pattern;
- a record pattern;
- guarded arms at different depths, the deeper first, with the later
  guarded arm itself taking `notArm1` (`deep`, p4);
- a later arm split deeper than the guarded one (`dd`, p7);
- two scrutinees with the guard on the bare one (`two`).

No panics or hangs.

The probes that were refused, all with a reason:

- **F1 (low): a misleading reason for a literal in the guarded pattern.**
  The doc comment and the proposal list this case as skipped "on a number
  or character literal". But the reason given is "an overlap hypothesis
  about a guarded earlier arm is needed where that arm's condition wasn't
  tested". Repro (p3):
  ```
  def lit: List Nat → Nat
    | [0, ..r] if List.length r > 2 => lit r
    | [_, ..r] => 1 + lit r
    | [] => 0
  ```
  The literal is tested by a decision, not a constructor split, so at the
  `Succ` leaf neither route applies. **Fix:** word the `facts`-miss skip in
  `refute_guard` as the doc does ("…where that arm's pattern has a number or
  character literal, which the split doesn't refine to a constructor"). A
  `Nat` literal could later be read as `Zero`/`Succ`; that is not needed
  now.
- Char literals and indexed families (`chars`, `vsum`, p9) are refused
  earlier, by the existing stage 2a reasons. The new indexed-family checks
  in `induct_field` and `refute_guard` are defensive and are not reached
  there.
- Mutual definitions get no `f.induct` at all ("doesn't call itself"). This
  is unchanged and outside G1.

**Not this lane, pre-existing on `main`** (checked with the main
checkout's binary); worth filing:

- **F2 (G2 gap):** a non-tail lifted `match` whose call recurses on a
  grandchild has no `f.induct`: E-TERMINATION, "`s` isn't seen as smaller
  than `xs`". Repro (p6):
  ```
  def g4 (xs: List Nat): Nat := match xs with
    | [a, ..r] => 1 + (match r with | [] => 0 | [c, ..s] => g4 s)
    | [] => 0
  ```
- **F3 (equations gap):** the overlapped arm has no `f.eq2` (E-REFL) when
  its body is a non-tail lifted `match`, so there is no `f.induct`
  either. Repro (`g5`, p6, and `g2` in p4):
  ```
  | [a, b, ..r] if a > b => g5 r
  | [a, ..r] => 1 + (match a with | 0 => 0 | Succ k => g5 r)
  | [] => 0
  ```

## Stability

- The only snapshot files are the two new ones for the new examples. No
  existing snapshot changes.
- `%fieldN` is numbered per definition by first use in the proof
  (`fields.len() + 1`), separately from `%apartN`, so no existing hidden
  name moves. Projections are made only for definitions that had no
  `f.induct` before.
- An edit elsewhere can't renumber them. An edit to the same definition
  can, which is the same as for `%apartN`.
- **Info (pre-existing pattern):** hidden definitions declared before a
  later skip stay in the kernel without `note_def`. This is the same as
  `%apartN`, and harmless.

## Code quality

- **F4 (nit):** in `void_here`, the last `else` (`fact h`) repeats the
  `read.prop.is_some()` branch. Either merge them, or say in a comment
  which guard form reaches the fallback (a proposition stated as itself
  that isn't `b = X`).
- **F5 (nit):** `quote(force(eval(…)))` now appears in both
  `refute_guard` and `project`, and also in the existing code. A small
  `normal_at(g, depth, t)` helper would shorten all of them.
- The `fields` map keys on `format!("{data:?}.{c}.{f}")`. That mirrors
  `discs`, but a tuple key `(DataId, usize, usize)` would be clearer.
- **F6 (nit):** `docs/proposals/functional-induction/g1-guarded-overlap.sw`
  is now a verbatim copy of `examples/accept/match-induct-guarded-overlap.sw`.
  Keep one; the proposal can point at the example.
- The comments follow CLAUDE.md: they give the why and the invariants (for
  example "at `p` they compute to the variables, at `x` to the values
  here"), with no narration.
- `refute_guard` is long (about 150 lines) but in clear stages: places,
  sides, projections, the clash, then the `J` chain. It reuses G2's
  `remap`, `ctor_of`, `branch_lib` and the `facts` machinery, rather than
  duplicating them.

## Probes

All are in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw4261rev/`:

- **p1, p2, p7:** all check.
- **p3:** `sdWrong` is refused as intended, and `lit` shows F1.
- **p4:** `g2` shows F3.
- **p6:** shows F2 and F3.
- **p8:** the scrutinee check: `t` is accepted and `u` refused.
- **p9:** `chars` and `vsum` are refused by earlier checks.
