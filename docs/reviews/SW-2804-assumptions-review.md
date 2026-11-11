# SW-2804 review: kernel assumptions for open goals (stage 1)

**Reviewed:** commit `604c398b9` on `lane/SW-2804` ("Kernel: assumptions for
open goals (SW-2804, stage 1)"), against
`docs/proposals/using-unfinished-proofs.md` (option A, D3504) and the
branch's `docs/core.md` section "Assumptions (open goals)".
**Reviewer:** Fable, 11 November 2026 (D3473). **Method:** paper review
only. Nothing was built or run; the lane's tests
(`crates/core/tests/it/assumptions.rs`) were read, not executed. File and
line numbers are the branch's.

## Verdict

**The kernel form is sound. It can be merged as stage 1.** I found no path
that gives an assumption a body, unfolds it, solves it, or uses it to make
a branch impossible, and no counterexample to the "premise, not a rule"
argument.

Three things are not settled by this commit and should be before the
later stages ship:

1. **Erasing a proof-typed assumption is only safe when the goal is true.**
   Under a false goal the erased run takes a branch it "can't", or treats a
   value as the wrong type. `docs/core.md` says such a `?` "is never
   reached", which overclaims. This matters now that D3507 lets programs
   with open goals run (F1).
2. **`State::Final` no longer means "finished", and nothing consults
   `relied_on` yet.** `audit` reports `State::Final` as `Checked`
   (`crates/driver/src/audit.rs:204`). Stage 2 must not land on `main`
   ahead of the stage 3 reporting, or `audit` passes declarations that rely
   on a goal (F2).
3. **The kernel doesn't refuse two assumptions with one label and type.**
   They would be two different constants with one hash (F3).

| # | Question | Verdict |
|---|---|---|
| 1 | A body, unfolding, or convertibility with anything else | SOUND |
| 2 | Index unification and empty matches | SOUND |
| 3 | Reliance read off checked terms | SOUND for the walk; UNSURE for "never counted as finished", which is not implemented yet (F2) |
| 4 | Hashing | SOUND, given unique labels, which the kernel doesn't enforce (F3) |
| 5 | Erasure when running | Data-typed stuck: SOUND as an interim. Proof-typed erased: UNSOUND at run time under a false goal (the logic is unaffected) (F1) |
| 6 | `docs/core.md` | Accurate on the form; four gaps (below) |

## 1. Can an assumption get a body, unfold, or equal something else? SOUND

An assumption is `State::Final`, `body: None`, `arity: 0`, `group: None`,
not opaque, not a theorem (`check.rs:2400-2435`, through `push_def`). This
is the shape float primitives and the `Delay` primitives already have
(`float.rs:658-660`, `partial.rs:432-434`), and in checking it behaves as a
hidden opaque definition does, so every path below was already exercised by
body-less final definitions.

**No later body.**

- `define_group` and `admit_trusted_group`: `install_group` refuses a
  member that isn't pending, "has already been defined" (`check.rs:2168-2169`).
- `retype_def`: pending only (`check.rs:2449-2453`).
- `set_run_body` and `admit_trusted_run_body`: both go through
  `run_body_shape`, which refuses an assumption (`check.rs:2515-2519`).
- `mark_opaque`, `mark_folded`, `mark_instance`, `set_unfolding`,
  `mark_tailrec`, `mark_param_default`: pending only (`check.rs:2472-2596`).
- `float::define_primitive` and `partial::define_primitive`: pending only
  (`float.rs:625`, `partial.rs:408`).
- `register_native`: refused explicitly (`native.rs:450-453`), and by the
  pin before that (`native.rs:429`).
- `registry::bind_def`: refused (`registry.rs:754`).
- An `unfolding` list naming one: `E-NOT-OPAQUE` (`check.rs:2657-2664`).
- The only other writers of `defs_mut()` are `abandon_pending` (pending
  only) and `add_validator` (see F5).

**One path has no explicit check: `float::register_def`**
(`float.rs:671-694`). It binds a float native to any final definition whose
content hash matches the pin (`float.rs:680`) and whose arity is the
native's. An assumption can't pass: its hash starts with the tag `assume`,
and its arity is 0 where every float native takes arguments. So it is
closed, but by the pin and the arity rather than by intent (F6).

**No unfolding.** Every unfolding path reads `body_seen`
(`value.rs:2593-2596`) or `def.body` directly, and both are `None`:

- `unfold_now` (`value.rs:2511-2556`): not opaque, no float definition, no
  native (those tables can't hold it, above), no body, so it returns
  `Neutral(Head::Def(id), spine)` at line 2556.
- `eval_step` and `quick` on `Term::Def` (`value.rs:1501-1504`,
  `1519-1542`): the glued-constant and arity-0 arms all need `Some(body)`.
- `is_folded`, `folded_call`, `opens_by_tree`, `matches_at_once`,
  `stuck_on_variable`, `underapplied`: all require a body
  (`value.rs:2690`, `2703`, `4024`, `946`, `4047`, `3984`).
- The termination checker and `inert.rs` only read the bodies of the group
  being checked (`termination.rs:129`, `inert.rs:134`).

**Conversion.** Heads are equal only for the same `DefId`
(`value.rs:389`). Two neutrals with the same assumption head take the
`sealed` arm and compare spines in shortcut mode (`value.rs:3754-3761`).
An assumption against any other head falls to "different". The
tree-comparison arms need `opens_by_tree`, so they never fire. Record eta
(rule 1, and rule 2 at `value.rs:2291-2295`) and the skipping of proof
fields (`value.rs:3740`) apply to it as to any neutral, and both hold for
every value of the type, so for every filling.

**The check cache and export.** `assume` passes `export = false`. The
cache's capture refuses a namespace holding any final definition without a
body (`crates/elab/src/cache/mod.rs:1468-1470`), so an assumption can't be
written to a cache entry, whatever the elaborator's bookkeeping says.

**Positivity.** A data type can't hide a non-positive occurrence behind an
assumption of type `Type -> Type`: a member inside any application that
isn't a data type is `Occurrence::Inside` (`check.rs:3863`).

## 2. Index unification and empty matches. SOUND

There is one implementation, `unify_index::unify`, and three callers: the
kernel's `case` branch (`check.rs:1182-1200`), `determined.rs:317` (replay
for the runtimes, outside the kernel) and the elaborator
(`crates/elab/src/families.rs:723`). Only `Outcome::Conflict` makes a
branch impossible (`check.rs:1196`).

- **Never solved.** `Scope::flexible` matches only `Head::Var`
  (`unify_index.rs:70-81`). A variable may be solved *as* a term that
  mentions an assumption, which is the ordinary rule.
- **Never a conflict.** A conflict needs `constructor()` to return a
  constructor for both sides (`unify_index.rs:273-280`), and it returns
  `None` for any neutral (`unify_index.rs:339-352`). So an assumption
  against a constructor is `Stuck(NotConstructor)`, which the kernel
  reports as `E-INDEX-STUCK`.
- **Deletion** is `conv`, so `a ≡ a` is deleted. That is right for every
  filling.
- **Numbers.** `2 + a` against `1` peels to `1 + a` against `0`, a conflict
  (`peel_succs`, then `constructor` on `NatAdd`). That is true for every
  `a`, exactly as for a variable.
- The occurs check ignores `Head::Def` heads and walks their arguments
  (`unify_index.rs:446`), which is right for a closed constant.

I looked for another place where "different" accepts something rather than
refuses it, and found none in `crates/core`: validators need a decision to
evaluate to `True`; `TypesDiffer` is stuck; eta's conditions are on the
declaration, not on a comparison.

## 3. Reliance. The walk is SOUND; "never counted as finished" is not built yet

`assumption::relied_on` (`assumption.rs:30-75`) walks a definition's type,
body, run body, validators and `unfolding` list, and a data type's
parameters, indices, constructor fields, result indices and validators. It
follows `Def`, `Data`, `Ctor`, `Case` and `Proj`.

**Semantic dependence is inside the walk.** A checked term can depend on an
assumption only by mentioning it, or by mentioning a declaration whose type
or body is evaluated. Each step of evaluation goes from a term to a
declaration it names, and the walk follows the same edges. Instances,
generated equation lemmas and cached declarations are ordinary definitions
whose terms are stored, so they are walked like any other.

**Three references are implicit in terms and the walk doesn't follow
them**, though the hasher does (`hash.rs:728-760`, `800`): `Term::Nat` and
`Term::NumCase` (to `Nat`), and `Term::Chars` (to `List` and `Char`, and
through `Char`'s fields to its validity proof). Today none can reach an
assumption:

- `Nat` is bound only if it is exactly `Zero | Succ Nat` with no
  parameters (`native.rs:389-405`), so its terms mention nothing else.
- `List` and `Char` are bound only at their pinned content hashes
  (`chars.rs:142`, `165`), and a hash that covers an assumption can't be
  the pinned one.
- Natives are bound at pinned hashes too (`native.rs:429`, `float.rs:680`).

So the gap is closed by the pins, not by the walk (F4).

**Kernel bookkeeping.** The kernel records a user of an assumption as
`State::Final`, by design. So `Final` no longer means "finished", and every
reader of `Final` as "proved" must change:

- `crates/driver/src/audit.rs:204`: `State::Final => Status::Checked`.
- `crates/driver/src/axioms.rs:226-290`: the walk doesn't look at
  `Def::assumption`, so a relier is reported with no axioms.
- `rt/src/lower.rs:123-131` and `js/src/lib.rs:994-1002`: these refuse a
  body-less definition whose result isn't erased, with the message "it
  hasn't been checked successfully". A proof-typed assumption passes them.

Nothing outside the tests calls `relied_on` yet. That is fine at stage 1,
where no assumption can exist. It is the main risk of stage 2 (F2).

One API gap: `relied_on` takes `DefId` roots only, so there is no way to
ask what a data type relies on.

## 4. Hashing. SOUND, given unique labels

- An assumption's hash is tag `assume`, the owner as a length-prefixed
  string, the hole number, and the type (`hash.rs:168-184`). A user's hash
  covers it through `def_ref` (`hash.rs:628-634`), since `def_hash_in`
  returns `Some` for it. So a change of type, owner or hole number changes
  every user's hash, and filling the `?` changes the owner's body and so
  every user's hash.
- The tag keeps it apart from primitives (`primitive`), float primitives
  and ordinary declarations.
- The proofless hash is the same function, so a data-typed assumption keeps
  its label there. A proof-typed one at a proof position is the marker, as
  any proof is. That is what the proofless hash is for, and nothing is
  cached by it (`hash.rs:128-131`).

**The gap (F3).** `assume` doesn't refuse a label and type already in use.
Two calls with the same `(owner, hole, type)` make two constants that
conversion tells apart and the hasher doesn't. Then `t : a₁ = a₁ := rfl`,
which checks, and `t' : a₁ = a₂ := rfl`, which doesn't, have one content
hash, and "same hash, same meaning" fails. Uniqueness is left to the
elaborator's numbering. The cases I'd expect to produce a duplicate are a
declaration re-elaborated in one kernel (the REPL, a redefinition), and
holes inside lifted helpers numbered per helper instead of per owner. The
damage is bounded, since nothing that relies on an assumption is finished,
but D3507's test results are cached by hash.

Run bodies aren't hashed, and `relied_on` walks them. So an assumption
reached only through a run body is reported but isn't in the hash. Stage 2
should make a run body use the same assumptions as the body, not new ones.

## 5. Erasure when running

The kernel never checks with erasure (`in_kernel_modes` stops it,
`machine.rs:73-89`), so nothing here affects what is provable.

**Data-typed, stays stuck: SOUND as an interim.** The reference evaluates
to `Neutral(Head::Def(id))`, which `erase::is_erased` doesn't match (the
placeholder is `Head::Var(ERASED)`, `erase.rs:64-71`). A `case` on it is
stuck: eta is off while a program runs (`value.rs:2388`), and no other arm
takes a neutral. Natives on it are stuck, or answer what is true for every
value (`0 ≤ a`). The fast runtime and JS refuse it before running
(`rt/src/lower.rs:123-131`, `js/src/lib.rs:994-1002`), with a message that
is wrong for this case but safe. No path produces a value that depends on a
guess at the filling.

**Proof-typed, erased: not safe under a false goal (F1).** `erases_result`
(`value.rs:2820-2824`) makes it the placeholder, as for a theorem. The
argument in `erase.rs:39-51` for why that's safe rests on "proofs are
already checked (and total) when the program runs". An assumption's proof
isn't. When its goal is false:

- **Cast.** `J` on the placeholder takes its base (`erase.rs:17-23`). With
  `h : Nat = Bool := ?`, `h ▸ 0` runs as the number `0` at type `Bool`. What
  a later `if` does with it depends on the runtime: the core machine's
  `case` is stuck on it, JS tests `0` for truthiness and silently takes a
  branch. With `h : 2 = 3 := ?`, a `Vec Nat 2` becomes a `Vec Nat 3`, and
  an in-bounds read of index 2 walks off the end.
- **Impossible branch.** `def pick (b: Bool) (h: b = True): Nat` with the
  `False` branch impossible, called as `pick False ?`: the run reaches the
  branch with no body and hits
  `panic!("internal error: unreachable: an impossible branch was reached")`
  (`value.rs:2307-2313`). That is loud, but it is a panic worded as a
  compiler bug, and I haven't read what `rt` and `native` do there.
- **Termination.** A `decreasing` goal left as `?` is erased, so a
  function that doesn't terminate runs until the budget stops it.
- **A test can pass under a false goal**, and D3507 runs tests under
  `warn`.

So `docs/core.md`'s "a proof's `?` costs nothing and is never reached" is
true only for a true goal. The proposal's own D-d said this ("a false one
... can make the erased program take a branch it 'can't' or treat a value
as the wrong type"); D3507 reversed D-d, and the running-stage ticket asks
for exactly this check. Until that stage decides, the kernel's rule should
be stated as conditional, and the memory safety of `rt` and `native` on a
mistyped value should be checked before a program with a proof `?` is
allowed to run through them.

## 6. `docs/core.md`

The section is accurate on the form, the refusals, conversion, index
unification and hashing; each claim I checked matches the code (sections 1
to 4 above). Gaps:

1. **Running** overclaims, as in section 5. It should say erasure of a
   proof assumption is correct only if the goal holds, and what a run may
   do otherwise. It also says a data one "stays a neutral: a run that needs
   its value is stuck", which is true of the core machine only; `rt` and JS
   refuse the program up front.
2. **"Why it's sound"** should state the second difference from a
   variable: a term that mentions an assumption is *closed* but needn't
   compute to a constructor. In checking that already happens (a hidden
   opaque call, `Delay`); in a running program it is new, and
   `value.rs:2289-2290` ("its values are closed") and the panic at
   `value.rs:2312` assume otherwise.
3. **Missing from "It never gets a body"**: `retype_def`, the two
   `define_primitive`s, `float::register_def` (closed by its pin and
   arity), and that `add_validator` currently accepts one.
4. **Unstated invariants**: labels must be unique and the kernel doesn't
   check it (F3); the walk relies on `Nat`'s shape check and the `List`,
   `Char` and native pins for the implicit references (F4); and `Final`
   no longer implies "relies on no open goal". The check-cache sentence is
   half structural ("has": the capture refuses a body-less definition) and
   half elaborator bookkeeping ("relies on": `unfinished_count`,
   `cache/mod.rs:704`), and should say which.

Also stale: `value.rs:2582-2585` (`sealed`'s doc lists "a member of the
group being checked, or an axiom") and `erase.rs:39-51` (the safety
argument) don't mention assumptions.

## Findings

| # | Finding | Severity | Suggested fix |
|---|---|---|---|
| F1 | Erasing a proof-typed assumption is unsafe at run time when the goal is false: mistyped values through `J`, a panic at an impossible branch (`value.rs:2312`), non-termination, a passing test. `docs/core.md` says it "is never reached". | High for the running stage (D3507); none for the logic | Before programs with proof `?`s run: decide what a run does (refuse, or run and say results mean nothing if a goal is false), check `rt`, `native` and JS on a mistyped value and an impossible branch, turn the panic into a diagnostic naming the goal. Fix the doc and `erase.rs`'s argument now. |
| F2 | `State::Final` is read as "checked" by `audit.rs:204`, `axioms.rs` and the runtimes' lowering, and nothing calls `relied_on`. | High for stage 2's merge order | Stage 2 and the stage 3 gates (`audit`, `axioms`, `run`, `build`, `test`, the cache's "relies on" rule) land together, or stage 2 keeps marking reliers unfinished until stage 3. |
| F3 | `assume` accepts a second assumption with the same label and type: two constants, one hash. | Low to medium | Refuse a label already held by an assumption (`E-MALFORMED`); add a test. |
| F4 | `relied_on` doesn't follow `Term::Nat`, `Term::NumCase` or `Term::Chars` to `Nat`, `List` and `Char`, which the hasher does. Unreachable today because of the shape check and pins. | Low | Follow them in the walk, as `hash.rs:728-760` does; add tests for reliance through a data type's field, a validator, a run body and an `unfolding` list. |
| F5 | `add_validator` accepts an assumption (`check.rs:4296-4320` checks only `Final`). Harmless to the logic. | Low | Refuse it. |
| F6 | `float::register_def` has no explicit assumption check; the pin and the arity close it. | Low | Add the one-line refusal, as `register_native` has. |
| F7 | `rt/src/lower.rs:130`, `js/src/lib.rs:1001` and `js/src/run.rs:152` tell the user a data-typed assumption "hasn't been checked successfully". | Low (running stage) | Name the open goal instead. |
| F8 | `relied_on` takes only definitions as roots. | Low (stage 3) | Accept data types too. |

## What I didn't check

- Nothing was run: the lane's tests, and its claim that no existing hash
  changes (`pinned_hashes`), are taken from the commit message.
- `crates/rt`, `crates/native` and `crates/js` beyond the lines cited: what
  they do with a mistyped value or an impossible branch is F1's open
  question.
- The elaborator's unifier (`crates/elab/src/unify.rs`), which treats
  `Head::Def` heads in its own ways. The kernel rechecks what it produces,
  so it can't affect soundness, only which programs elaborate.
- Whether rewinding declarations (`Registry::forget_from`,
  `Builtins::rewind`) clears the per-`DefId` caches an assumption's id
  might be reused under. That mechanism predates this change.
