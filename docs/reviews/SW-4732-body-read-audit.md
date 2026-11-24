# SW-4732: the elaborator's reads of a definition's body and arity

Fable paper lane, 24 Nov 2026. Code read at `2b273366d`; probes run with main's
release binary built at 11:48 that day (SW-4728's eta fix, in review, is not in
it). Marks: **[verified]** read at the file and line given, or probed;
**[not verified]** argued but not followed to the end.

## Result

**No hole found.** No read of a body, an arity or a group in `crates/elab`, or
in `crates/driver` outside tests, lets another sealed theorem's proof (or a
shape derived from it) reach a cache entry, a warning, a term or a verdict of a
namespace that the interface-digest cache would replay.

Two things do depend on other theorems' proofs, both as SW-4706 found them:
the text of one error's note (`equation_notes.rs:212`), and the driver's
report-time walks (`axioms`, `audit`, test reliance, the editor's trial). An
error keeps a namespace out of the cache, and the walks read the live
session, never an entry.

The argument is by reading for most sites, and nine of them rest on an
indirect reason (the type of what is read, or "this is the current
declaration's own helper") rather than a test in the code. That is the
weakness: nothing stops the next read from being wrong. Section 5 proposes
one accessor to make it structural.

## 1. What a sealed theorem hides

The digest (`cache/mod.rs:2725-2800`) leaves out, for a definition with
`hash::has_interface` (a theorem, final, with a body, not an assumption):

- its body (`mod.rs:2752-2757`);
- its group list (`mod.rs:2772-2789`);
- so also everything admission derives from the body: `arity` (the body's
  leading lambdas, `core/check.rs:2782`), `lift_leaf`, `recursive`
  (`check.rs:2796-2798`) and the transparency set;
- since stage C, whole declarations: the lifted `match` helpers that only
  sealed proofs reach.

So the question for each read is whether it can reach any of these for a
theorem other than the one being elaborated.

The kernel side is one predicate. `value::body_seen` (`core/value.rs:3453`)
returns no body for a definition whose type is a proposition (`frozen`,
rule F) while checking, and every theorem's type is one (docs/core.md, opaque
definitions rule 6). Every unfolding and every arity read in the evaluator
that I looked at is behind it or behind `unfold_now`'s `frozen` test
(`value.rs:1853-1895`, `3255-3263`, `3355-3376`, `3545-3566`, `3688-3728`)
**[verified for those lines; `crates/core` was not audited as a whole, which
was SW-4700's and SW-4728's job]**. A glued call `Value::Call` is therefore
never headed by a theorem while checking, which two unifier sites below rely
on.

## 2. The reads

The grep (`.body()`, `.arity()`, `body_seen`, `run_body()`, `own_run_body()`,
`.group()`, `admitted_metadata`, `def_hash(`) gives 252 lines in the two
crates outside tests; most are fields of other records (`alt.body`,
`branch.body`, `closure.body`, `QuotForm::arity`, a walk family's `arity`).
The reads of a `Def` are below, all of them.

Verdicts: **safe** (can't reach another theorem's proof, or reads nothing the
digest leaves out), **harmless** (can, but only into an error's text or a
report that isn't cached).

### 2.1 Behind `body_seen`: safe

| Site | Read |
|---|---|
| `quot.rs:552` | whether a body reaches a quotient |
| `cases.rs:3636-3649` | case tree and arity of a stuck call |
| `unify.rs:958` | whether a head is rigid: a theorem gives `Rigid::Opaque`, whatever its proof |
| `probe.rs:412` | the body to instrument |
| `dot.rs:127-130` | body and arity of a definition of a type |
| `matching/untouched.rs:125` | arity, after `is_folded`, which tests `body_seen` |

### 2.2 A test in the code excludes theorems or proofs: safe

| Site | Read | The test |
|---|---|---|
| `rewrite/repeatedly.rs:1745` | body present | `def.theorem()` first |
| `rewrite/repeatedly.rs:1580-1582`, `1620`, `1769` | case tree, node count, arity of a rule that names a definition | reached only through `definition_named` (`1745`), which returns nothing for a theorem; `unfold` is set only at `1586` |
| `opaque.rs:249`, `256` | body and arity for `f.unfold` | `def.theorem()` at `243` |
| `opaque.rs:467`, `529` | body of an opaque definition declined in a goal | `def.opaque()`; a theorem is never marked opaque (rule 6) |
| `unify.rs:3477-3480` | whether an accessor's body is a projection | `g.def(*d).proof()` at `3474` |
| `equations.rs:2319`, `2370`, `2383` | arity and body of the definition whose equations are made | theorems return at `2287-2312` before either |
| `equation_notes.rs:35` (into `equations/induct.rs:235`, `207`) | whether `f` calls itself | `def.theorem()` at `29` |

### 2.3 Safe by an indirect argument

No test in the code; the read is safe because of what the definition must be.
These are the sites the accessor in section 5 is for.

| Site | Read | Why it can't be another theorem's proof |
|---|---|---|
| `unify.rs:3189` (`projection_of`) | whether a body is one `case` giving a field | called only on the heads of `Value::Call`s (`3127-3146`), never a theorem's (section 1) |
| `reading.rs:496-498` | arity of the test function in a `@[reading]` statement | the function's result is `Bool` |
| `matching.rs:2672` | whether a constant's body is a number literal, for a note | a proof is never `Term::Nat` |
| `walk/mod.rs:708-711` (`ignores_arguments`) | body and arity of a walk family's relation | its result is `Prop`, so it isn't a proof |
| `walk/mod.rs:975` (`case_tree`) | body of a lifted `match` in the code being walked | the code is a program in the goal; a goal can't mention a helper that only a sealed proof reaches **[not verified beyond `mod.rs:946-958`]** |
| `equations.rs:4379-4380`, `4424`, `4440-4443` | arity and body of a `.%match` helper in the body whose equations are made | the helper is the current definition's own (2.2 excludes theorems upstream) |
| `equations/induct.rs:456-466` | body and arity of a helper on the way to `f.induct` | same; `helper_calls` (`207`) also requires `f`'s name as prefix |
| `decreasing.rs:1106`, `1235-1236`, `1966-1968`, `2320-2322`; `decreasing/plain.rs:799`, `855-864` | the step, the measure and the helpers of a `decreasing` definition | generated for the declaration being elaborated; `decreasing_measure` has one caller, `induct.rs:1285`, on the same definition |
| `tailrec.rs:204`, `208`, `237`, `390-393` | run body, group and arity for `@[tailrec]` | the declaration being checked, its group and its helpers |
| `carry.rs:264`; `core/pretty.rs:3634` | body of `Decidable.elim` | a builtin, not a theorem |
| `nav.rs:1525`; `core/pretty.rs:1004` | body of a parameter default's helper | a helper is a definition in the digest, also when its owner is a theorem |
| `core/pretty.rs:2888` | arity of a `.%match` helper being printed | printed terms are goals and types, which can't mention a proof-private helper **[not verified]** |
| `lib.rs:4251` | whether `List.length` has its run body | a builtin |

### 2.4 Only whether there is a body: safe today

| Site | Used for |
|---|---|
| `module.rs:3219` (`auto_eligible`) | "not finished checking": a verdict |
| `reading.rs:1886` | which instances a reading search considers |
| `interfaces.rs:1029` | which of two error texts |
| `interfaces.rs:1300`, `auto.rs:1547` | hints in an error |

A definition without a body hashes differently, and no proof edit changes
whether a final theorem has one. All five matter for stage 2 (section 4).

### 2.5 Reaches other theorems' proofs: harmless

| Site | Read | Why harmless |
|---|---|---|
| `equation_notes.rs:212` | the proof of every theorem named like a generated equation, session-wide | only an error's note; `encode_pass` refuses a namespace with an error. The comment at `203-207` says so |
| `assume.rs:157` | the body of the declaration that owns a `?`, which may be a theorem below | one caller, `driver/test_run.rs:254`, wording a test's "unfinished" report at run time |
| `timings.rs:364` | sizes, for `--timings` | not in an entry |
| `driver/axioms.rs:233`, `278`; `core/assumption.rs:151-152` | every body, for `axioms` and reliance | report-time walk over the live session (proposal 2.3) |
| `driver/audit.rs:467` (`witness_of`) | every theorem's proof, looking for one that applies a given theorem | `audit`'s own report |
| `driver/declhash.rs:140`, `153` | full hash and mentions of each declaration | a listing |
| `driver/live/trial.rs:570`, `582`, `588`, `839`, `974` | full hashes, terms and mentions of the edited namespaces and their users | compared within one live session after the trial's check; nothing is stored. (SW-4706 had not read this file.) |
| `driver/test_run.rs:348`, `447`, `529` | a test's hash, and the hashes of the goals it relies on | a test's hash covers theorems by statement; reliance is found by walking live bodies and is in the result key (`326-352`) |

### 2.6 The cache itself

`cache/mod.rs:2570`, `2757`, `2760`, `2790-2791`, `2797`, `4042`, `4328` and
`cache/dump.rs:246-275` read the unit's own definitions to write, replay or
print its entry. The body and group of a sealed theorem are written to the
entry and left out of the digest, as designed. A theorem's own run body
(`2790`) is in the digest: at worst a missed cut-off.

## 3. Probes

Each probe is a two-namespace project. `A` is checked, then only proofs in `A`
are edited; `B`'s result from a warm cache (confirmed "replayed from its
entry" with `STITCHWORT_CACHE_DEBUG=1`) is compared with `check --no-cache`.
Then `B` is elaborated from cold against each version of `A`, and its two
entry files compared byte for byte.

| Probe | Proof edits in `A` | `B` uses the theorems by | Result |
|---|---|---|---|
| p0 | `byComputing` to a call of a later `def` | direct use | same |
| p1 | recursive `match` to a call of another theorem; lambda to a bare name (arity 1 to 0, statement `∀ (n: Nat) => …` after the colon); `byComputing` to a call; tuple pattern to `Both` pattern; record pattern to a field; recursion to a library lemma | application, application to fewer arguments (`def partial := bumpId`), `rewrite`, `rewrite repeatedly`, `.flipped`, `byFacts`, a transport in a `def` (`rewrite … then v`), a declaration with an unused-binder warning | same output and exit; `B`'s two entries (6,478 bytes) differ in 48 bytes |
| p2 | a `@[reading]` theorem's proof from a call to a `match`; two more given a `match` or reordered arms | pattern on a test fact, `.read`, a record built as a test fact, `byFacts`, `rewrite repeatedly [clamp, h]`, a `test` | same; entries (6,364 bytes) differ in 48 bytes; `stitchwort test` warm gives "cached", `--no-cache` passes |

The 48 bytes are the entry's 16-byte salt and its 32-byte checksum
(`cache/mod.rs:3119-3139`): offsets 45-60 and the last 32. The key, the
dependency hashes and the whole body, every term and warning of `B`, are
identical whichever proofs `A` has **[verified by `cmp -l`]**.

One thing seen on the way, not a hole: changing a proof from a `match` on
`h: p ∧ q` to `h.left` moved `A`'s digest, so `B` was elaborated. With another
theorem in `A` already using `.left` it didn't move, so it is the namespace's
needs (the dot name, or the library file behind it), which the digest keeps
on purpose (proposal 1.3). A missed cut-off, the cheap direction.

The probe sources are in the lane's scratch folder and are not committed;
p1's shape is enough to rebuild them:

```
namespace A
import Std (Eq, Nat)
def bump (n: Nat): Nat := match n with
  | Zero => Zero
  | Succ k => Succ (bump k)
theorem bumpId ∀ (n: Nat): bump n = n := match n with     -- edit: := bumpAux n
  | Zero => byComputing
  | Succ n => Eq.cong Succ (bumpId n)
theorem bumpAux ∀ (n: Nat): bump n = n := bumpId n        -- edit: the match
theorem bumpFn: ∀ (n: Nat) => bump n = n := n => bumpId n -- edit: := bumpAux
```

What the probes don't cover: `byWalking`, instances that are theorems,
`decreasing` definitions, mixed groups of a theorem and a definition, `check
--jobs`, and the editor.

## 4. For parallel stage 2: the stated theorem

A stated theorem (parallel-checking.md 10.2) is final, has no body, no group
and arity 0. Places that would behave differently for one:

**Changes a verdict or what is found: must change with stage 2.**

| Site | What happens |
|---|---|
| `module.rs:3219` (`auto_eligible`) | no body is read as "not finished checking", so `auto` stops using every stated theorem. Should test the state, or `stated` |
| `reading.rs:1886` | an instance without a body is left out of the reading search; wrong if an instance can be a theorem and so stated |
| `core/hash.rs:237` (`has_interface`), `205` (`def_hash`) | both need a body: a stated theorem would not hash as a proved theorem's reference does, and has no full hash at all. 10.2 says it must hash as one; this is where |
| `cache/mod.rs:2570` | `encode` refuses a unit holding a final definition without a body. Right for a unit's own declarations; stage 3's `leave_stated` makes own ones |

**Changes only an error's text.**

| Site | What happens |
|---|---|
| `interfaces.rs:1029` | an invalid instance with no body is reported as "isn't finished here" where it would say "has errors" |
| `interfaces.rs:1300`, `auto.rs:1547` | stated declarations drop out of the hints |
| `equation_notes.rs:212` | the note lists no equation whose theorem is stated: a worker's note and the last pass's would differ |

**Needs the proofs, so needs a session loaded in full.**

`driver/axioms.rs:233`, `278` and `core/assumption.rs:151` (reliance, `axioms`,
the check summary's "rely on" line), `driver/audit.rs:467`,
`driver/test_run.rs:236-254`, `326-352` (goals a test relies on; a walk that
stops at a stated theorem would miss a goal inside its proof and give the
wrong result key), `driver/declhash.rs:140-153`, `driver/live/trial.rs:570-588`,
`839`, `974`, `assume.rs:157`, `timings.rs:364`. With stated theorems each
would under-report in silence, not fail. 10.4's rule that such a session loads
again in full has to cover every one, and a walk that meets a stated theorem
should be an internal error, not an empty result.

**Arity 0.** No reader in the elaborator is affected: every arity read is of a
computing definition or behind `body_seen` (section 2). In the kernel,
`value.rs:3545-3566` and `3722` compare a spine's length with the arity before
they test `body_seen`, which is harmless at 0 since `body_seen` then fails.

**Unaffected.** `unify.rs:958` and the evaluator's `Term::Def` case
(`value.rs:1853-1895`) already treat a theorem as a head that never unfolds;
`rewrite/repeatedly.rs:1745` and `opaque.rs:243` test `theorem()` first.

## 5. Recommended fixes and tickets

1. **One accessor for the elaborator (hardening, small).** Add
   `Def::computing_body()`, or an elaborator helper, that returns no body when
   `has_interface` holds, and use it at the sites of 2.3 and 2.4; keep the bare
   `body()` for the cache, the reports of 2.5 and the kernel. Then "no
   declaration sees a theorem's proof" is a property of one function, and a
   grep for `.body()` in `crates/elab` outside `cache/` should list only
   `equation_notes.rs:212`, `assume.rs:157` and `timings.rs:364`. No result,
   message or hash changes. Sonnet, with a test that pins the list.
2. **Stage 2's build plan (SW-4727) takes the list in section 4**: the four
   verdict sites first, `auto_eligible` above all, and the rule that a
   reliance walk never passes through a stated theorem quietly.
3. **Widen the differential test** (proposal section 6, "for each theorem,
   replace its proof"): compare the dependant's entry bytes outside the salt
   and checksum, not only the check's result, as section 3 did by hand. It
   catches a proof-dependent term that happens not to change a message.
4. **No ticket**: the `h.left` missed cut-off (section 3) is the digest's
   needs rule working as designed.

## 6. What I could not verify

- `crates/core` beyond the lines cited: the reference evaluator
  (`reference.rs`), erasure and termination read `body` and `arity` and were
  only skimmed.
- The "own helper" rows of 2.3 rest on the callers I read and the functions'
  doc comments, not on every path to them.
- A running program unfolds everything (`frozen` is off while
  `program_running`); that erasure has removed every theorem call first is
  taken from the spec, not checked.
- Whether an instance can be a theorem (`digest_plan` at `cache/mod.rs:2268`
  allows for it); the stage 2 row for `reading.rs:1886` depends on it.
