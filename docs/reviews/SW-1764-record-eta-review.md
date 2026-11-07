# SW-1764: review of record eta, stages 1 and 1b (`lane/SW-1642`)

*Independent review before merge (D2364), 6–7 November 2026, of `git diff
main...lane/SW-1642` at 98873e547 (9 commits, one of them a merge of main).
I read the design note (`docs/proposals/record-eta.md`, D2498–D2505), the
tickets SW-1642 and SW-1667, and `docs/reviews/SW-1744-trip-journal-float.md`
(D2551). I ran the branch's release binary (built 23:22) on small probe files
and on the new examples, `cargo test -p stitchwort-core --test record_eta`
(16 passed) and `a_namespace_checked_alone_has_the_same_hashes` (passed,
27 s). I didn't run whole AoC or the roguelike.*

## Verdict

**Merge after one fix**, then the whole-AoC and roguelike check (D2507).

I found nothing that makes something false check. The kernel rules are
sound under the conditions `check::has_eta` enforces, and the kernel, the
elaborator and the reference evaluator agree on everything I tried. The
native hold is sound and coherent. The fix:

1. **The check cache loses the `no_eta` mark** (must fix). A namespace
   replayed from the cache gets its interface dictionaries back *with* eta.
   So a warm check accepts what a cold check rejects, and the dictionaries'
   data hashes change between cold and warm. Shown in §2.4.

Small things worth doing in the same lane (each under 30 minutes):

2. A must-reject example that depends on the hold. Today's
   `float-sum-stays-a-sum` would be rejected without the hold too (§3).
3. A test that the machine and the reference evaluator agree on the hold.
4. A test that pins which definitions the hold covers, since its doc says
   "today only `Float.add`".

Smaller still, could be filed: the hold is missing from the two
stuck-tree walkers (latent, §2.3); a few code-quality items (§6); and
§6.4 of the design note no longer says what was built (§6).

## 1. Kernel soundness

**Which types get eta** (`check::has_eta`). It needs all of these: one
constructor, no indices, a sort other than `Prop`, a group of one, no
field type that mentions the type, at least one field whose sort isn't
`Prop`, not `no_eta`, and declared as a record (D2509). Each is read from
the final declaration, and on both admission paths: `install_data_group`
sets `eta` for `admit_data_group` and for the cache's
`admit_trusted_data_decls`. The trusted path also refuses records with
indices. Sorts are concrete (`Sort::Prop | Type(u32)`, no level variables),
so "a field whose sort isn't `Prop`" can't hide a proof, and
`proof_field` reads the same `field_sorts`. The D1981 argument in the
comment is right. I checked the case it doesn't spell out: a record whose
only data field has a type without eta (`{ u: UnitType, ok: P }`). Two
unknowns are then compared at `x.u` against `y.u`, two different neutrals,
so they are "different", and transitivity holds.

**Projections** (`infer_proj`). The value's type is *inferred* and must
force to `Data(d, ps)` with the same `d` (the Lean projection bug). `d` must
have eta, which rules out `Prop` and so any data taken out of a proof. The
field's type is instantiated with `ps`, then with `t.j` for each earlier
field. `eval::project` never takes apart another type's constructor; such
a case panics as an internal error, and only an ill-typed term can reach
it. `Term::Proj` is handled in every pass over terms (hash, codec, dump,
pretty, inert, termination, axioms, JS, rt, unifier traversals). JS writes
an erased field as `undefined` and Float's `bits` as `toCanonicalBits`.

**Rule 1** (`conv_step`). It comes after glued calls are forced and after
the folded-value arm, so `n` is a plain neutral or a stuck field call.
Fields go left to right. Proof fields are skipped in normal mode and
compared in shortcut mode, exactly as for two constructors. It relies on
conv's same-type contract, which nothing here weakens. Within the
elaborator, the one place where that contract doesn't hold is
`first_order`, and the unifier's rule 1 is off there (`NO_ETA`). Core
`conv` called from inside `first_order` would still apply rule 1 to
ill-typed pairs. It could only answer "equal" for junk projections that
match exactly, and the kernel rechecks anyway, so this is harmless.

**Rule 2** (`branch`, `walk_tree`, `reference::eval_tree`, `same_trees`).
It takes the only branch on a neutral of an eta type, with the fields
projected from the scrutinee *before* it was forced (`eta_fields`): a field
of a glued call stays a field call. It's off while a program runs. It
fires on metavariables in the elaborator, as D2511 decided. The kernel
never sees one, and once `?r` is solved, `ReplayElim` projects the
solution, so what the elaborator decided is what the kernel computes.

**Fields of glued calls** (`project_call`, `Frame::CallField`,
`Unfolding.base`). The field call is defined as
`project(force(call))`, and every path computes exactly that:

- `force_call` forces the base call, sharing the base call's unfolding;
- `unfold_folded` runs the tree, then projects;
- `unfold_once` does the same one step at a time.

Its stuck form, `Neutral(Def f, [args…, .i])`, names the same value as a
projection of the stuck call `f args`. `is_folded` counts it as folded, so
a comparison that fails structurally unfolds it before saying "different".
Same-head spines are compared by congruence, which is sound whatever they
unfold to. I found no path where a field call and its projection could be
told apart in a way that adds an equality.

**Probes run on the branch** (`check --no-cache`):

| Accepted (all fail on main) | Rejected (E-REFL) |
|---|---|
| `p = { row = p.row, column = p.column }` | `(x y: Checked) → x = y`, `Checked = { value: Nat, small: value < 10 }` |
| `(down p).column = p.column` | `(x y: Small) → x = y`, `Small = { ok: 1 < 10 }` (proofs only) |
| `Box (List Nat)`: `b.get = b.value`, and `b = { value = b.value }` | `x = { ok = h }` for `Small` |
| `c = { value = c.value, small = h }` (any proof) | `x = {}` for a record with no fields |
| `x + y = { bits = x.bits, valid = x.valid } + y` | `p = asPerson q` for `Person`/`Pet` of one layout |
| | `r = { label = r.label, kids = r.kids }` for a recursive `Rose` |
| | `p = { a = p.b, b = p.a }` |
| | `Float.add x y = Float.ofBits (Float.Model.addBits x.bits y.bits)` (the hold) |

The brief's specific worries:

- **A record with no fields** gets no eta, and its probe is rejected.
- **A record with proof fields** is tested beside a data field and with
  proofs only, both rejected.
- **A definition with an implicit index**: records can't have indices
  (both admission paths), and `has_eta` checks it anyway. Implicit
  *parameters* are ordinary parameters: projections don't store them.
- **Mutual or recursive records**: a group of more than one has no eta, and
  a field mentioning the type has no eta. Recursion is tested; mutual
  records aren't (§3).
- **Universe levels**: nothing to do. A projection's type is a field type
  that was checked when the type was declared, instantiated, and there is
  no cumulativity.

## 2. The native hold (D2551)

**2.1 Keying on `has_native`.** `Builtins::has_native` is true when the
definition is in `natives` or has a float native, whatever
`disable_natives` / `disable_float_natives` say. That's the right choice:
conversion is then the same with natives on and off, so the gate that
compares natives with their definitions checks the same terms as the
normal run. The set is a function of the environment. `bind_builtin_def`
binds a std definition when it becomes final, before anything after it is
checked, and the cache's replay binds through the same function. The
kernel, the elaborator and the reference evaluator read one
`g.env.builtins()`, so they agree.

**2.2 "Fewer equalities, never more."** True. The hold turns one rule-2
step inside a native's own case tree into `stuck_tree`, the definition
applied to its arguments. Everything conversion then says "equal" (same
head with convertible arguments, unfolding elsewhere) is true in the model,
with or without the hold. The hold can't make a term that is well typed in
one checker ill typed in another, since all three apply it to the same
definitions. What it costs is **incompleteness, not disagreement**:
`Float.add x y` isn't convertible with its own unfolding on unknowns (my
last probe). It is narrower than SW-1744 feared: `Float.add x y` against
`Float.add {..x..} {..y..}` *is* accepted (compared argument by argument,
then rule 1).

**2.3 Two walkers without the hold.** `value::walk_tree` and
`reference::same_trees` apply rule 2 with no `eta_held` check. Today
that's harmless. `opens_by_tree` never opens a definition that is
`float_bound`, or one whose Nat native is on, and Nat natives' trees don't
match on records. But `opens_by_tree` follows the native *switch*
(`native(id).is_none()`), while the hold ignores it. With natives off, a
Nat native opens by tree, and the walker would apply rule 2 where `branch`
wouldn't. Suggest checking `eta_held` in both walkers, for symmetry.

**2.4 The cache drops `no_eta` (must fix).** `mark_no_eta` is called only
by the elaborator, when it declares an interface (`lib.rs:1956`). The check
cache's entry writes `auto_params` but not `no_eta`, and its replay
(`cache/mod.rs` ≈2830) re-marks only `auto_params`. Repro, in a two-file
project (A declares `interface Sized (k: Type) = { size: k → Nat }`, B
imports it):

```
theorem dictEta (s: Sized Nat): s = { size = s.size } := rfl
```

With B edited and A replayed from the cache, `check` says `checked 2
namespaces`. `check --no-cache` says E-REFL ("`s` and `{ size = Sized.size
}` aren't equal"). So the answer depends on the cache, and A's dictionary
hashes without its `no-eta` tag when warm, so entries written warm and cold
don't match. It isn't unsound: eta is true for dictionaries, and D2502
withheld it as a design choice. But it breaks "a target never changes
meaning". Fix: write `no_eta` in the data record of the entry, and call
`mark_no_eta` on replay while the type is still pending. Add a test that
replays an interface namespace from the cache and compares hashes and the
`dictEta` verdict with a cold check. `a_namespace_checked_alone_…` doesn't
use the cache, so it can't catch this.

## 3. The must-reject tests

`record_eta.rs` covers the types that must get no eta: proofs only, no
fields, recursive (`Rose`, `Loop`), two constructors, `Prop`, a dictionary
(with its hash). It also covers ill-typed projections (another type with
the same layout, a field past the last, a projection of a `Nat`, the wrong
parameter's field type) and machine/reference agreement on both rules.
That's the right core. Missing:

- **A reject that depends on the hold.** `float-sum-stays-a-sum` rejects
  `span.end = span.length + span.start`, which is false by computation
  even without the hold: bit-level addition doesn't commute definitionally.
  Only its message snapshot pins the hold. Add the `Float.add x y =
  Float.ofBits (Float.Model.addBits x.bits y.bits) := rfl` reject. The
  hold rejects it, and without the hold it should check (I didn't
  confirm that with the hold removed).
- **The reference evaluator under the hold**: add that pair to
  `the_reference_evaluator_agrees`, using a native-bound definition with a
  record case (a test `Builtins` registration, or std's `Float.add`).
- **Which definitions are held**: a test listing the definitions with
  `has_native` whose tree has a `case` on an eta type, asserting
  `{Float.add}`. A new one then becomes a decision, not a surprise.
- **A mutual group of records** (`group.len() == 1` is untested).
- **A projection of a pending type** (in a later field of its own
  constructor), refused because `eta` is false while the type is pending.
- **A dictionary after cache replay** (§2.4).
- `Box Nat` against `Box Bool` (records.md §14) can't be reached:
  conversion of different types is ruled out by the contract, and the
  projection typing test covers the parameter. No test needed.

## 4. The hash moves

The commits give the reasons: interface dictionaries' `no-eta` tag, terms
that now contain `Proj`, and Float's pins (which in the end take main's
values). I spot-checked 15 snapshots:

| Snapshot | What moved | Explained by |
|---|---|---|
| `records` | `Person`/`Team` `%instDecEq`, `%show`, `%compare`, `%equal`, `%flip`, `%trans`, `%instOrd`; *not* the accessors, `ext`, `leadName`, `firstLead` | dictionaries |
| `abort` | `Turn.%…` derived, `test` | dictionaries |
| `ctor-braces-later-record-pattern` | derived instances only | dictionaries |
| `derive-ord-own-deceq` | derived, `instDecEq`, `test` | dictionaries |
| `extract-pairs` | derived only | dictionaries |
| `match-eq-auto` | `pick`, `pickLess`, `pickRewrite` (all `[auto ord: Ord k]`) | dictionaries |
| `partial-filter-lambda` | `totalSteps` (`List.sumBy`, `[auto add: Add b]`), `test` | dictionaries |
| `rewrite-premises` | `cancelled`, `small` (`List.sumBy`); not `swapped`, `fixed`, `bounded` | dictionaries |
| `random-seed` | `main` (string interpolation, `Show`), `test` | dictionaries |
| `decreasing-callback-argument` | `splits*` (`sumBy`, `==`), `asked*`; not `asking` | dictionaries |
| `logic-notation` | `fresh`, `inSet`, `position`… (`Map`, `Set`: `Ord`) | dictionaries |
| `quot-protomap` | the `ProtoMap` and `Inventory` *data* (auto `Ord` parameter), then everything | dictionaries |
| `cases-bool` | only `ieeeLtLe` and its `%match`es; not `orComm`, `xorAssoc`, `clampBelow` | `Proj` in a generated proof (`cases` over `x.bits`) |
| `omega-day05` | `absorbLo`, `absorbStacked`, `coveredTop`, `mergedContains` (omega and `match` proofs over `r.from`); not `absorb` | `Proj` in generated proofs |
| `prelude` | 2041 of 5567; for example `Mod.addAssoc`, `Float.ieeeLe*`, `Float.Theory.unitsPositive` | both |

Every move I looked at is explained, and what didn't move is consistent
with that: accessors, `ext` lemmas, and programs with no instance.
**The `no-eta` tag is right**, and hashing it is necessary, not just
tidy: what's accepted depends on it (§2.4's `dictEta`), so two
environments that differ in it mustn't share cache entries. The cost is
that every hash that reaches an instance moves once, which is migration
cost (doesn't count).

One thing the hashes show that the design note doesn't say: **the
elaborator never emits `Proj` for `p.field`.** Field access is still a
call of the accessor definition. Rule 2 opens it on an unknown, and `Proj`
reaches stored terms only through read-back (tactics, motives, `cases`,
`omega`). That's why `leadName` keeps its hash. It works, but it isn't
record-eta.md §6.4 ("the elaborator emits `Proj` directly for `p.row`"),
and part of rule 2's cost is every field access on an unknown. Either
update §6.4, or file "emit `Proj` for field access" for a later stage.

## 5. Cost: `resolveOutOfWalls` (SW-1762)

I didn't run the roguelike. From the code, the growth (proof term 4.6k →
106k nodes) looks like a cost, not a deeper problem.

- **Rule 2 builds no constructors**; it binds projections. Rule 1 only
  compares. Neither rule expands anything inside a motive.
- **What does build constructors** is the record updates: `{ state |
  message = … }` is a generated definition that matches its record and
  rebuilds it (`…update…%match1` in the snapshots). On an unknown `state`,
  rule 2 opens it to a constructor of every field as `state.fᵢ`, and
  `monstersTurn`, `playerMoves` and `drink` then compute further on those
  literals.
- **`match phase: state.phase`** builds its motive by abstracting
  `state.phase` in the goal. If the goal is read back unfolded, each branch
  of `resolve` is written out as full `State` literals, as a tree.

That's the SW-1744 shape again (computation on unknowns, read back without
sharing), and it belongs to D2514's direction: motives and searches built
from goals as written. It's not a soundness sign, and it's not eta inside
motives. To confirm cheaply: count the `Ctor(State)` and `Proj` nodes in
the old and new terms, or check `Walls.sw` with rule 2 off for the update
definitions only.

## 6. Code quality and comments

The comments are good: each rule says why it's sound, why it ends, and
where its twin lives. The soundness block above `has_eta` is a model of
its kind. Smaller points:

- Two functions called `has_eta` with different meanings:
  `check::has_eta(&Data)` *decides*, `value::has_eta(g, d)` *reads the
  flag*. Rename one (`decide_eta`?).
- `folded_call`'s doc ("[`is_folded`] but for fields of calls: a folded
  call the machine unfolds") reads as the opposite of what it does: it is
  `is_folded` *without* field calls.
- `Frame::CallField(Box<(DataId, usize, DefId, Spine, bool)>)`: a named
  struct would say what the `bool` is (unfolded already).
- `omega.rs` `Ranges::parts`: the `Neutral(Head::Def(mem), spine)` arm
  `filter_map`s eliminations and silently drops a `Proj`. It's harmless
  for `Mem` (a `Prop`, so it never has a field call), but the pattern
  would misread a field call of a definition that returns a record.
  Guard it with `is_call_field`, as the `Call` arm now does.
- `eta_held`'s doc says "today only `Float.add`": pin it with the test in
  §3.
- `infer_proj` evaluates `t.j` for every earlier field each time it's
  inferred. That's fine at record sizes; it would only matter with a very
  wide record.

## Findings worth filing

- §2.4: the cache drops `no_eta` (fix on this branch before merge).
- §2.3: the hold in `walk_tree` and `reference::same_trees` (small).
- §3: the hold tests and the mutual and pending-projection rejects
  (small; could go with the fix).
- §4: emit `Proj` for field access, or update record-eta.md §6.4 (design
  follow-up, stage 2 or 3).
- §5: SW-1762 is the bounded-readback family. Link it to D2514's stages
  rather than treating it as an eta bug.
