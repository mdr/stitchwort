# SW-4262 review: `f.induct` for a recursive call in a non-tail `match` (G2)

Reviewer: Opus, paper lane, 19 Nov 2026. Branch `lane/SW-4262`, commit
`cc3221b5f`. Probes run with the branch's release binary against main's
(`~/repos/mdr/stitchwort/target/release/stitchwort`), on small files in
the reviewer's scratch.

**Verdict: merge after fixes** (three should-fix items: F1 and F2, and
F3, a one-line condition). Nothing here is a soundness problem: every
generated principle and its proof go through the kernel, and the probes
found no principle whose statement is wrong. Where the generator goes
wrong, the result is a refusal (`E-NO-INDUCT`), never an accepted
principle with a bad statement.

## What was checked and holds

Statements read off `stitchwort doc Main.f FILE`, all on the branch:

| Shape | `ih` generated | OK? |
|---|---|---|
| scrutinee is itself a recursive call, arm calls again (`match a rest with \| Succ k => k + a rest`) | `motive rest (a rest)`, then `(k: Nat) → a rest = Succ k → motive rest (a rest)`; no duplicate | yes |
| two nested `match`es (`Some n` then `Zero`/`Succ m`) | `(n) → o = Some n → n = 0 → …` and `(n) → o = Some n → (m) → n = Succ m → …` | yes |
| nested pattern `Some [v, ..w]` | `(value) → o = Some value → (v) (w) → value = [v, ..w] → …` | yes |
| catch-all after `None` (fields) | one `ih`: `(value) → o = Some value → …` | yes |
| `if` guard inside the alternative (structural) | `(m) → x = Succ m → motive k rest …` and `… motive (k + 1) rest …`; no guard premise | yes (fewer premises is a stronger, easier `ih`) |
| pattern variable shadowing a parameter (`Some x => s x rest`) | `(x: Nat) → o = Some x → motive x rest …`: the inner `x` (read from the code: the leaf refers to the alternative's binder) | yes |
| number arm `7` then `_` | `x = 7 → …`, and the default with no premise | yes |
| pair pattern `(u, v)` | `(u) (v) → p = (u, v) → …` | yes |
| local definition with captured variables (`cap.go y x rest x`) | premises are about the split parameter, captured `x` stays `x` (`x = 0 → motive (y + x) rest …`) | yes |
| local definition that calls itself | refused: "…`sc.go`, … which calls itself" | yes |

On the question "is each premise true at the call site and not vacuous":
every premise is `scrutinee = C fields` (or `= k`), with the scrutinee
exactly as the helper received it, so it is satisfiable by the
alternative that reached the call (the proof does `match hs: e with` and
passes `byComputing`, as the accept example shows). For structural
recursion the premises are not even needed by the generated proof, so
they cost the user nothing beyond `byComputing`. Nothing beyond what the
function establishes is assumed: the number default and guards add no
premise.

Existing principles: the only change on the old path is `move_under`
with `k = 0`, which is `move_to` (the `l >= b` branch is never taken),
the proof's `var` with `k = 0`, and no lambdas; so non-G2 principles are
the same terms by construction. Spot-check: `check --index` output of
`function-induct{,-nested,-catchall,-split}.sw` and `match-induct.sw` is
byte-identical between main's binary and the branch's (the index has no
hashes, so this checks names and goals only), and the printed
`f.induct` statement of every `def` in those files plus
`function-induct-call-in-scrutinee.sw` is identical too; the lane's diff touches no
existing hash snapshot. The verifier's `hash_stability` run is the real
check.

## Findings

### F1 (should-fix): a `decreasing` proof that relies on the `match`'s refinement makes the kernel refuse the principle, with an internal message

The generated `ih` reuses the call's decrease proof "read in the
alternative", but in the `ih` the scrutinee is a variable with a premise
`xs = [_, ..rest]`, not refined. A decrease proof that checked only
because the scrutinee was refined (the common case: a `match` on a
parameter, proof by `arithmetic`, `byComputing`, `Nat.leRefl`) no longer
has the right type, the kernel refuses the generated proof, and the user
sees a kernel type mismatch as the reason.

```
def lp (xs: List Nat): Nat
    decreasing xs.length
:=
  if xs.length == 100 then 0
  else
    Succ
      (match xs with
        | [] => 0
        | [_, ..rest] => lp rest [decreasing := arithmetic])

theorem tlp ∀ (xs: List Nat): lp xs ≥ 0 := match induct (lp xs) with
  | zzz => ?
```

```
[E-NO-INDUCT] … `lp` has none
  Note 1: why: the kernel refused the generated proof (E-TYPE-MISMATCH:
  type mismatch: expected `rest.length < xs.length`, but this has type
  `rest.length ≤ rest.length`)
```

Same with a number arm (`| 5 => dn 4 [decreasing := byComputing]`:
"`5 <= n` and `True` aren't equal"). Main refused both too (no
regression), but the docs now say a `decreasing` call "keeps its decrease
proof", which reads as covering these. Only the `match h:` style (the
accept example's `pops`) works.

Fix: transport the decrease proof along the premise. Under the `ih`'s
binders the premise `p: e = C fields` is Var-addressable; when `e` is a
case variable (or in general), the proof `π: P[C fields]` becomes
`J`/`Eq.subst` of `π` along `sym p` at motive `y => measure args <
measure (lhs with y)`. Alternatively, as a minimum, catch this kernel
refusal and say in words what can't be done ("its decrease proof uses
what the `match` learned; write `match h: e` and use `h`"), and say so in
`docs/syntax.md`. I'd do the transport: it is the shape users write.

### F2 (should-fix): a cycle of local definitions loops to the budget, ~5 s, with a misleading message

`helper_calls_under` refuses a helper that calls itself directly, but not
one in a cycle (`syntax.md`: "consecutive local definitions form a
group"). The walk goes `ev → od → ev → …` until the nesting budget stops
it, which takes about 5 s for one definition (main refused in 0.4 s for
the whole file) and reports the budget, not the cause:

```
def m (xs: List Nat): Nat := match xs with
  | [] => 0
  | [x, ..rest] =>
    def ev (k: Nat): Nat := match k with
      | Zero => m rest
      | Succ j => od j
    def od (k: Nat): Nat := match k with
      | Zero => 1
      | Succ j => ev j
    Succ (ev x)
```

Branch: `Main.m.induct  checking it takes more than the generator allows
for one equation (its proof computes too far)`, `check --no-cache` 5.2 s.
Main: "it calls itself inside `m.ev`, …", 0.4 s.

Fix: keep a stack of the helpers being walked (in `HelperWalk`) and
refuse with the existing "which calls itself" reason (or "…which is in a
cycle with `m.od`") when a helper is reached again. Add this file as a
reject example; it is the test that fails before the fix (today it fails
on the message and the time).

### F3 (should-fix, small): the `decreasing` path walks into any function the `%rec` lambda is passed to, not just `f`'s helpers

In `calls`, the non-`decreasing` arm requires a helper of `f`
(`helper_calls` checks the `f.` name prefix), but the `decreasing` arm
fires for any `Term::Def(x)` with a `%rec`-shaped argument, so a
top-level function given `(y p => hf y [decreasing := p])` has its body
read as if it were a lifted `match`:

```
def twice (k: Nat) (g: (y: Nat) → y < k → Nat): Nat := match k with
  | Zero => 0
  | Succ j => g j (Nat.leRefl k)

theorem twiceCong ∀ (k: Nat) (f1 f2: (y: Nat) → y < k → Nat) (e: (y: Nat) → (p: y < k) → f1 y p = f2 y p): twice k f1 = twice k f2 := match k with
  | Zero => byComputing
  | Succ j => e j (Nat.leRefl (Succ j))

def hf (n: Nat): Nat
    decreasing n
:=
  if n == 100 then 0
  else Succ (twice n (y p => hf y [decreasing := p]))
```

Branch: "the kernel refused the generated proof (… expected `j < n`, but
this has type `Succ j ≤ Succ j`)" (F1's problem, reached through
`twice`'s body). Main: "a recursive call's arguments depend on a
binder…", the documented reason. Were the proof not refinement-dependent,
the branch would state an `ih` through `twice`'s case tree: still true
(kernel-checked) but outside what the docs describe, and it walks
arbitrary bodies (std functions included). Fix: add the same `f.` prefix
condition to the `decreasing` arm (or check it at the top of
`helper_calls_under`).

### N1 (note): `if h:` inside the alternative of a `decreasing` definition is refused as binder-dependent

`| Some k => if h: n == 0 then 0 else dg (n - 1) (Some k) [decreasing :=
ltPred n h]` is refused with "a recursive call's arguments depend on a
binder it is under". Pre-existing limitation (the call is under `h`'s
binder); worth a line in the proposal's gap list next to G2, not this
lane.

### N2 (note, pre-existing, worth a ticket): wrong note for a `decreasing` definition with no top-level split

A `decreasing` definition whose body is `Succ (match … )` with no
top-level `if`/arms gets no equations at all, and `match induct` says
"`dg` doesn't call itself, so it has no `dg.induct`", which is false.
Same on main. Repro: `p5.sw`'s `dg` and `dn` without the leading `if n
== 100 then 0 else`.

### N3 (note): code quality

- `HelperWalk::tree`'s `Case` and `NumCase` arms each rebuild the
  "update `vals[hl]` and the `match h:` equations" step and the `rec`
  test; a small helper (`refine(vals, hl, value, at)`, `reaches_f(body,
  vals)`) would remove the duplication.
- "which splits an indexed family" is also the message when the
  scrutinee's quoted type is a different data type than the `Case`'s
  (`dd != data`); that's an internal "couldn't read" case and should say
  so.
- The two "isn't called with all its parameters" checks (`arity` and the
  `split_pis` length) can be one.
- The doc comment on `Ih.under` and on `helper_calls_under` are clear;
  the module doc's new parenthetical makes the old sentence hard to read
  ("…an inner call before the call it is an argument of; a call inside
  a lifted `match` that isn't in tail position under the alternative it
  is in, quantified …, G2), and the motive…"): a separate sentence would
  read better.

### Panics and loops

No panic found. Index arithmetic (`vals.len() - 1 - ix`) is checked;
the shifts assume `vat, tat ≤ cd`, which holds by construction. The only
loop is F2, which the nesting budget does stop.
