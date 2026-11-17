# Review: keeping a declaration's type glued (SW-3911)

Fable, 17 Nov 2026. Reviews [docs/proposals/glued-kept-types.md](../proposals/glued-kept-types.md)
(SW-3888): evaluate `Def::ty_value` with gluing on in `push_def` and
`retype_def`.

Done by reading the code at `acfab959a`. Nothing was built or run: there was
no binary with the prototype patch, and a paper lane doesn't build one. So
every statement below about behaviour *with* the change is from reading, and
the ones that most deserve a run are marked "unverified".

## Verdict

**Sound as proposed, as far as what the kernel accepts. Land it with the
changes in §2**, which are about determinism and about readers outside the
kernel, not about accepting something false.

I found no way for a glued call in a kept type to make the kernel accept a
term it would refuse today. I found one way for it to change what the
*elaborator* sees depending on whether a body was checked or replayed from
the cache (R1), and five readers that would misread a type written through
a nickname (R2). Both are cheap to fix.

## 1. Soundness

### 1.1 The argument

1. **No new rule.** The change adds no value form, no evaluation rule and
   no conversion rule. A closed type's value becomes what the codomain of a
   type with parameters already is while a body is checked: evaluated
   glued, with calls forced by whatever takes them apart. `check`,
   `infer`, `conv`, `sort_of`, `is_type_former` and `telescope` meet glued
   calls in every body check today (D483), and the first domain of an
   outer `Pi` and the top of a closed type are the only places that were
   always unglued.
2. **Same term, same relation.** `ty_value` is still the evaluation of the
   checked term `Def::ty`. docs/core.md's equality rule ("Consequence")
   says gluing changes when something is computed, never what is equal,
   and `proof_equivalence.rs` holds every mode to that. The kernel already
   relies on it for bodies.
3. **The kernel never uses an unfolding it didn't compute.** This is the
   new exposure: a kept type's calls carry cells (`Unfolding::kept`) that
   outlive the check and that the elaborator also forces. `Kept::fits`
   serves a reader only an unfolding from epoch 0 or the reader's epoch.
   The kernel's `Ev` has `NoMetas`, epoch 0; the elaborator's stores start
   at 1 (`ev.rs`, `Metas::epoch`). So an unfolding the elaborator computed
   never fits a kernel reader, which recomputes and overwrites it. The
   cell's field is private to `value.rs`, so untrusted code can't write
   one. Even if that failed, the unfolding of a closed call with closed
   arguments is computed by the same trusted machine and can't read a
   metavariable, so the worst case is still a correct unfolding.
4. **Forcing later is forcing in a larger environment, and the environment
   only grows.** A call is made only for a definition that already has a
   body (`case_tree`: `def.body` is `Some`), bodies are set once
   (`check.rs:2528`), `opaque`, `fold` and `no_eta` can be set only while a
   declaration is pending, and removing declarations (`forget_from`)
   removes a definition together with everything after it, so a kept type
   never outlives what its calls mention. Between making a call and
   forcing it, the only changes are pending declarations becoming final,
   which adds equalities (delta, record eta) and takes none away.

### 1.2 The cases the brief lists

- **Conversion between glued and unglued forms.** Expected type a call,
  found type a call of the same definition: arguments first, in shortcut
  mode, then unfoldings (D483, D2352); a call against anything else is
  forced. All of this runs today for types with parameters. With gluing
  off (`telescope` from `erase.rs`, `add_validator`, the native shape
  checks' `conv`), `needs_forcing` is true for a call whatever the mode,
  so those readers force as well.
- **Opaque definitions.** A direct call of a hidden opaque definition is
  still a neutral for good: `unfold_now` returns the neutral before any
  call is made. What changes is a call of a *transparent* definition whose
  body reaches an opaque one: forced under a set that holds it, it
  computes through. Three facts make that harmless:
  - unfolding an opaque definition is never unsound, only a breach of
    abstraction, and here the set allows it;
  - `Kept` records the transparency set, so an unfolding made under one
    set is never served under another;
  - the checker itself never reads `ty_value` under a non-empty set:
    `infer` on a `Def` and `admit_group` both go through `def_type`, which
    evaluates `Def::ty` afresh. The readers that do are `determined.rs`
    `Replay::of_def` (under the definition's own set) and `erase.rs` while
    a program runs (every opaque body visible). Both already see through
    opaque definitions in the codomains of types with parameters; closed
    types now behave the same. See finding F1.
- **Universes.** A type's sort comes from `check_type` on the term, before
  and independently of `ty_value`. Calls in a kept type are closed, at
  level 0. Nothing changes.
- **Proof irrelevance.** The kernel has it (core.md, "Proof irrelevance").
  Two calls are compared by arguments in shortcut mode, which compares
  constructors' proof fields, so the shortcut says "equal" only where the
  unfoldings would. `conv`'s precondition (two values of one type) holds:
  the two sides are both types. No new comparison site.
- **Recursion and mutual groups.** A member of the group being checked has
  no body, so it's never a call, and a neutral made for it stays one. A
  kept type can't observe a half-admitted group: bodies are installed
  together after the group's checks. A recursive definition's call is
  forced step by step as it is in a body check; termination was checked
  when it became final.
- **Quotients.** With gluing off a call with a `Quot.lift` leaf is folded
  by name; glued it's a `Call`. Kept types move from the first to the
  second. Both are lazy forms under the equality rule, and
  `proof_equivalence.rs` covers the lift leaf in both modes.
- **Rejecting what should be accepted.** I found no case. One difference
  in the other direction: a closed statement too expensive to compute
  failed at its declaration with `E-RESOURCE`; now it's admitted if the
  proof never forces it. That's the point of the change.

### 1.3 What does change, without being unsound

- **The first lazy state shared across declarations.** Today every glued
  value dies with the check that made it. A kept type's calls live as long
  as the definition, so whether a later declaration pays to force one
  depends on whether an earlier reader already did, and that differs
  between a cold check and a cached replay (`admit_trusted_def` skips the
  body). Step counts per declaration become history-dependent, and a
  declaration right at its budget could hit `E-RESOURCE` in one and not
  the other. Rare, and results never differ; core.md should say so.
- **Cached replays get faster.** `admit_trusted_def` calls `push_def`, so
  today every replay of the reproducer computes the whole statement
  unglued (the proposal's 21%). Glued, a replay computes nothing. The
  proposal doesn't claim this gain; it should.
- **Memory.** The proposal says the unfolding a call keeps "is what the
  unglued value held anyway". That's true of the top value only. Once a
  `byComputing` proof forces the statement, the kept type holds the call,
  its arguments' calls and each one's kept unfolding (for the reproducer,
  the 3,601-element list and the chain of `List.all` calls), for the life
  of the session, where today it holds `True = True`. Measure peak memory
  on a whole-project check (R5).

## 2. Changes

Required:

- **R1. Record the kernel flag in `Modes`** (`value.rs`), and require it
  to match in `Kept::fits`. `eta_fields` builds different values under
  `Machine::kernel`: the elaborator keeps a stuck field of a folded call
  as `(f x).i`, the kernel projects the unfolded neutral, which shows a
  `decreasing` definition's fuelled helper. Today no kernel-made unfolding
  reaches the elaborator. With the change, one computed while the kernel
  checks a body (epoch 0, gluing on) fits every elaborator reader, so what
  a later goal shows, and what `match` and `rewrite` find in it, would
  depend on whether that body was checked or replayed from the cache. It
  takes a closed type with a stuck folded call in it (an axiom, an opaque
  definition or an open goal's assumption under a record projection), so
  it's rare, but it breaks SW-1782's rule that an unfolding never depends
  on who forced it first. Unverified by a run.
- **R2. Force before looking at the top of a kept type** in the five
  readers that don't (§3, marked "no"). `auto.rs` `result_head` matters
  most: it remembers its answer.
- **R3. A test that fails without the change**, stated in steps rather
  than seconds: a kernel test (`crates/core/tests/it`) that declares a
  closed statement whose computation exceeds a small
  `budget.operation(limits)` and admits a general proof of it within that
  budget. The proposal says the examples suite can't pin a step count; a
  kernel unit test can.
- **R4. The comments and documents that say otherwise**: `Machine::glue`'s
  doc, the comment in `admit_group` ("made unglued by `declare_def`"),
  `def_type`'s doc, `push_def`'s doc, `Kept::fits`'s doc, folded-calls.md
  stage 4, and core.md (§5).
- **R5. Two measurements before it lands**, by the verifier or Overmind,
  not a lane: kernel time on a population of closed statements proved by
  computing (the proposal measured two `Proofs` namespaces; tests whose
  definition's own type is the computed equation are the population the
  1.4× falls on), and peak memory on a whole-AoC check.

Recommended:

- **R6. Turn gluing on before `def_type` in `admit_group`**, so its
  re-evaluation under a non-empty transparency set is glued too. As
  proposed, a theorem with an `unfolding` list keeps today's cost: its
  type is evaluated unglued by `def_type`, since gluing is switched on one
  line later.

## 3. Readers of `Def::ty_value`

"Forces" means it calls `force`, `telescope`, `conv` or `quote` before
looking at the shape, so a call at the top is harmless.

Kernel (`crates/core`):

| Site | Use | Forces |
|---|---|---|
| `check.rs:2414` `def_type` | the type for `infer` on a `Def`, `admit_group`, `set_run_body`, `inert.rs:93` | callers do |
| `check.rs:4677` `add_validator` | `telescope` | yes |
| `determined.rs:189` `Replay::of_def` | `telescope`, under the definition's transparency set | yes (F1) |
| `erase.rs:195`, `:238` | `telescope`, `proof_telescope`; remembered per definition | yes (F1) |
| `partial.rs:423` | `conv` against the expected shape | yes |
| `native.rs:507`, `float.rs:617`, `nat_add.rs:422` | `conv` against the expected shape | yes |
| `globals.rs:225`, `:351` | the accessor; a test-only setter | n/a |

Hashing (`hash.rs`), the check cache and the reference evaluator don't
read it: hashes are of `Def::ty`, the term.

Elaborator (`crates/elab`):

| Site | Use | Forces |
|---|---|---|
| `auto.rs:1419` `result_head` | the data type a result is, remembered | **no**: `while let Pi = &ty` with no first `force`; a type written through a nickname gets `None`, cached |
| `dot.rs:2013` | "isn't a function with an implicit first parameter" | **no**: `matches!` on the value |
| `dot.rs:2042` `annotation_type` | "a definition without parameters is a nickname" | **no**: a definition whose type is a nickname for a function type would count as one |
| `interfaces.rs:1293` | hint naming a dictionary of the right type | **no**: `if let Value::Data`; only loses a hint |
| `library.rs:964` `library_decision_procedures` | test helper (`#[doc(hidden)]`) | **no** |
| `reading.rs:391`, `:982`, `:1116`, `:1677` | parameters of a reading | yes |
| `numbers.rs:1962`, `omega.rs:982`, `:4299`, `ring.rs:1253` | applying a lemma to arguments | yes |
| `interfaces.rs:399`, `:636`, `:1062` | an instance's parameters | yes |
| `partial.rs:117`, `:147`, `:650` | counting parameters | yes |
| `auto.rs:503`, `:808`, `:872`, `:1451` | lemma parameters | yes |
| `search.rs:171`, `:1229`, `:1241` (`type_holes`) | types of holes | yes |
| `rewrite/repeatedly.rs:1607` | lemma parameters | yes |
| `unify.rs:2593` | the type of a call's head | yes |
| `check.rs:6016` (`insert`, `unify`), `:9017` (`takes_lambda_argument`) | hints | yes |
| `dot.rs:1111`, `:1730`, `:1786` (`named::signature`) | named arguments | yes |
| `dot.rs:1876` | shown in a message | prints |
| `assume.rs:408` | `conv` with a new assumption's type | yes |
| `counterexample/mod.rs:348` (`quote`), `:457`, `:484`, `inputs.rs:347` | the statement to search | yes |
| `decreasing.rs:1422`, `lib.rs:4184`, `lib.rs:4236` (`def_ty`) | the body's expected type; `telescope` | yes |
| `kernel.rs:278` `def_ty` and its 25 callers | `def_type` for the elaborator | callers force, as for any codomain |

Elsewhere:

| Site | Use | Forces |
|---|---|---|
| `driver/src/run.rs:214` | `main`'s type shown in a message | prints |
| `driver/src/audit.rs:545` `concludes_empty` | result type | yes |
| `js/src/lib.rs:212` (`quote`), `:240` | export checks | yes |
| `rt/src/specialise.rs:181`, `:245`, `rt/src/erasure.rs:47` | `telescope` | yes |
| tests: `core/tests/it/groups.rs:507`, `termination.rs:660`, `driver/tests/soundness_fuzz.rs:1982`, `proofs/differential.rs:198`-`222`, `elaboration/nesting.rs:415`, `:438`, `division.rs:140` | `check`, `conv`, `force`, `try_normal`; `division.rs:140` prints a type with a parameter | yes |

The proposal says only the top of a closed type can now be a call. The
first parameter's type is one too: a `Pi`'s domain is a value, evaluated
with the type. Every later domain is already glued for a glued reader, so
code that takes a domain apart either forces or is already wrong for
second parameters; I didn't audit domains site by site.

## 4. Messages

A printed kept type shows a call as written rather than its unfolding
(`Readback::Shown` writes a `Call` as the call). Unverified by a run.

- **Better:** `dot.rs:1876` and `interfaces.rs:1293` (a function's type in
  a note), `run.rs:214` (`main`'s type), and the kernel's `E-TYPE-MISMATCH`
  in a body check ("the expected type is …"): `Parser Nat`, not what
  `Parser Nat` unfolds to. This is what types with parameters already
  print.
- **Worse:** the kernel's `E-REFL` (`check.rs:814`) for a closed statement
  would say "`List.all … slow` and `True` aren't equal" where it now says
  "`False` and `True` aren't equal": the computed form was the informative
  one. It reaches a user only when the elaborator accepted the proof and
  the kernel refused it, so it's a message about a bug, and the
  elaborator's own message, already glued, doesn't change.
- **Unchanged:** `E-NOT-A-PROP` evaluates the type itself; the
  counterexample note reads the statement back with `quote`, which writes
  unfoldings.

## 5. The 1.4× on `byComputing`

Where it comes from: today a closed statement proved by `Refl` is computed
once, unglued, in `push_def`, and `Refl`'s `conv` then compares two normal
forms. Glued, `conv` forces the call, and glued forcing allocates a call
and a kept unfolding for each nested call it then forces at once.

- **Compare glued first, then fall back.** That is what the proposal does:
  arguments first, then unfoldings. The cost isn't a second comparison;
  it's that the fallback's forcing is glued. A fallback that computed
  unglued instead would need either a comparison that never forces (new
  trusted code) or a second, unglued value of the type kept beside the
  glued one. Not worth it.
- **Unglued when the body is `Refl`** is workable and small. In
  `admit_group`, if the body under its locations and annotations is
  `Term::Refl`, evaluate `Def::ty` unglued for that check, as `def_type`
  already does under a transparency set, instead of using `ty_value`. A
  `Refl` body forces both sides of the equation whatever happens, so
  nothing is lost against today, the glued `ty_value` was never forced so
  nothing is computed twice, and it's a choice between two evaluations of
  one checked term, so it can't affect what's accepted. It leaves
  `f 5 = f 5 := Refl` at today's cost rather than the glued one. It only
  helps when `Refl` is the whole body; a `Refl` under `Decidable.sound`
  is checked against a codomain, glued today and unaffected either way.
- **Recommendation:** land without it, measure (R5), and add the `Refl`
  case only if a real population shows the cost. Two Proofs namespaces and
  Whereabouts showed none.

## 6. What docs/core.md must say

In "Glued calls", replace "never for a type it keeps (`Def::ty_value`)"
with:

- The kernel evaluates a definition's kept type with gluing on, so a call
  in a closed type, or in a first parameter's type, is computed only when
  something takes it apart. A kept type is still evaluated with every
  opaque definition hidden; `def_type` evaluates it again under a
  non-empty transparency set.
- A kept type's calls outlive the check. An unfolding is kept with the
  modes it was computed in, now including whether the kernel computed it
  (R1), and with its epoch: the kernel uses only unfoldings from epoch 0,
  its own, and recomputes any other.
- A call is forced in the environment of the time. That is sound because
  the environment only grows: a call is made only of a definition with a
  body, bodies and the `opaque`, fold and `no_eta` marks are fixed before a
  declaration is final, and a definition is removed only together with
  everything declared after it.
- A consequence: the steps a declaration's check takes can depend on which
  earlier check already forced a call in a kept type, so on whether those
  were checked or replayed from the cache. Results don't.
- Under "Arguments are computed only when a type needs them": a closed
  statement is computed while checking only if its proof takes it apart; a
  proof by computing still computes it, a general one doesn't.

folded-calls.md stage 4 ("so nothing glued outlives the check", and "A
type without parameters gains nothing") gets a note pointing here.

## 7. Findings for tickets

- **F1. Three readers use `ty_value` where `def_type` is meant.**
  `determined.rs:189` runs under the definition's transparency set, and
  `erase.rs:195` and `:238` can run while a program runs, with every
  opaque body visible, and cache the answer per definition. For a type
  with parameters the codomain is evaluated in those modes and sees
  through an opaque nickname; for `def f: Hidden` the kept neutral never
  does. So what the telescope says about parameters hidden behind an
  opaque nickname depends on how the type is written and, for erasure, on
  the mode at first use. It exists today; the change moves closed types
  written through a transparent nickname from one side to the other.
  Worth a probe: a definition with `unfolding Hidden`, type `Hidden`, and
  a lambda body, through `Replay::of_def` ("fewer parameters than
  lambdas").
- **F2. `set_run_body` checks with gluing off** (`check.rs:2859`), unlike
  `admit_group`. Probably deliberate; if not, it's the same four lines.
