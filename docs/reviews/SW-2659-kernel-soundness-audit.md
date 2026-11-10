# SW-2659: a fresh-eyes soundness audit of the kernel

10 November 2026, on `main` at `4a617cdb8`. A paper lane: the code was read,
and suspected holes were tried as small `.sw` probes against the release
CLI already built (`stitchwort check --no-cache`). No test suite was run.

The question: is there any way a false theorem gets accepted?

## Verdict

**I found no way to make the kernel accept a false theorem.** Every probe
that states something false was refused, and the rules I read (typing,
case trees, index unification, conversion, the number natives, termination,
admission) say what `docs/core.md` says, with the gaps listed below.

**The one real exposure is outside the kernel's logic: the check cache.**
A cache directory that arrives with a project (copied, downloaded,
committed) is read and trusted, and trusted entries skip the kernel. The
salt meant to stop that is stored in the same directory. This is F1.

**This audit did not read the whole crate.** `crates/core` is 26,900
lines; I read about 10,000 closely. The parts most worth a second lane
are how the evaluator unfolds and forces calls (`value.rs` 1215–1512 and
2489–2812) and read-back. "What I did not read" below is the list.

Counts: 0 at severity 1, 1 at severity 2, 2 at severity 3, 4 at
severity 4.

## Findings

| # | Sev | Where | Finding | Ticket |
|---|---|---|---|---|
| F1 | 2 | `crates/driver/src/check_cache.rs:149-173`, `crates/cli/src/main.rs:1440-1451`, `2690`, `2727` | A cache directory copied with a project is trusted: its salt travels with it, and `check`, `test` and `audit` read it by default | SW-2661 |
| F2 | 3 | `crates/core/src/check.rs:2832`, `3087` | A data type becomes final with an index type that mentions a failed declaration | SW-2662 |
| F3 | 3 | `crates/core/src/check.rs:2815-2821`, `3378-3403` | A data type's parameter types aren't checked for `case` outside a case tree | SW-2663 |
| F4 | 4 | `docs/core.md` (Terms, Typing, Evaluation and conversion) | The spec has no `Proj` term, no projection typing rule and no record-eta rules; it still says "Record eta, if it's added" | none |
| F5 | 4 | `docs/core.md:307` | The spec says natives are bound by type only and a changed `Nat` library is outside the guarantees; the code pins them by content hash | none |
| F6 | 4 | `crates/core/src/native.rs:1054-1080`, `docs/core.md:292` | `*`'s shortcut builds a "stuck" call without running it: `Succ (two 0) * 3 = 9` is refused. G9 names only `Nat.add` | none |
| F7 | 4 | `docs/core.md:3` | The status line says 16 October 2026 | none |

Severity: (1) a false theorem accepted; (2) a likely hole, unconfirmed;
(3) a missing guard; (4) a gap between spec and code.

### F1. A cache directory copied with a project is trusted (severity 2)

**What the design says.** `docs/proposals/check-cache.md` §3.1 lists the
threat "a cache copied from elsewhere (another machine, a committed
`.stitchwort`, a download)", which under trusted replay means "trusting a
stranger's proof". Its mitigation is "never read caches you didn't write:
a per-machine random salt in the cache directory's header".

**What the code does.** The salt is read from `check/header` inside the
cache directory itself (`check_cache.rs:149`), and an entry fits when its
salt is that one. So the salt stops one entry file being moved into
another directory. It doesn't stop the whole directory travelling: the
header comes too. The entry's checksum is plain BLAKE3 with no secret
(`crates/elab/src/cache/mod.rs`, `seal`), so anyone can write a
well-formed entry. The default cache directory is `.stitchwort/cache` in
the project folder (`main.rs:1440`). `audit`, the command that says whether
theorems can be trusted, reads it too (`main.rs:2690`, `2727`).

**Confirmed:** entries in a copied directory are loaded, not rebuilt.

```sh
cp -R examples/projects/accept/alias-dot-across-import ca
(cd ca && stitchwort check)          # writes ca/.stitchwort/cache/check/*
cp -Rp ca cb
(cd cb && stitchwort check)
stat -c '%y %n' ca/.stitchwort/cache/check/* cb/.stitchwort/cache/check/*
```

In `cb` the five `std.*` entries keep the modification times they had in
`ca`, so they were read from the copy and admitted through
`admit_trusted_*`. A hit writes nothing; a miss rewrites the entry. The
two `ns.*` entries were rewritten only because the project's name defaults
to the folder's, which changed.

**Not confirmed:** I did not build a forged entry that proves `False`. It
needs the entry encoder (`cache/codec.rs`), about a day's work, not a
probe. My confidence that it works is high: replay installs bodies without
type checking or termination checking (`check.rs:3322-3344`), and the only
checks left are structural.

**Who is exposed.** Anyone who runs `check`, `test` or `audit` without
`--no-cache` on a project folder they didn't build themselves, with the
same compiler build as the forger. The `.gitignore` written into
`.stitchwort/` stops accidental commits, not deliberate ones. §3.1's other
row, "someone malicious who can write to your project folder: out of
scope", doesn't cover this: here the folder was written before it reached
you.

**Suggested fix.** One of:

- seal each entry with a keyed hash whose key is kept per user, outside
  any project (the user's cache or config folder), so only entries this
  user's own runs wrote fit;
- or keep it as it is and make `audit` always check in full, as
  `--no-cache` does, and say in `check-cache.md` that a cache directory is
  as trusted as the compiler.

The first closes the row in §3.1; the second only narrows it. This is a
trust decision, so it's Matt's.

### F2. A data type can be final with an index type that mentions a failed declaration (severity 3)

`declare_indexed_data_group` lets a failed reference through, in the
parameters and in each member's index types, with the comment "a failed
reference is let through: `define_data_group` finds it again"
(`check.rs:2815`, `2832`; the `admissible` result is dropped).
`admit_data_group` then looks again at the parameters, the fields and the
constructors' result indices (`check.rs:3087`, `3113`, `3223`), but never
at the index telescopes. So a group whose index type mentions a failed
definition, and whose fields and result indices don't, becomes final.

That breaks the invariant `admissible`'s own doc states (`check.rs:3483`):
"every final declaration was admitted under this rule, so everything it
reaches is final too". The spec says the same ("nothing built on it is
ever accepted").

**Why it isn't severity 1.** A failed definition has no body, so it's a
neutral constant, and any definition that mentions it directly is still
refused. To build a value of the type you need an index, whose type
mentions the failed definition. I see no path to `False`, and the file has
an error already, so `check` fails. No reproducer through the CLI: the
surface language has no way to write an indexed type with no constructors,
and a constructor's result index would mention the failed type.
Confidence in the reading: high.

**Fix.** In `admit_data_group`, pass every member's index types to the
first `admissible` call along with the parameters. A core test with a
failed definition in an index type and no constructors.

### F3. A data type's parameter types aren't checked for `case` outside a case tree (severity 3)

Every other type the kernel admits goes through `case_only_in_tree(ty,
false)`: a signature (`check.rs:2303`), a field (`3105`), an index
(`2836`), a result index (`3228`). A data group's parameter types don't,
on the checked path (`2815-2821`) or the trusted one (`3378-3403`). `infer`
refuses a bare `Case`, but `check` accepts one anywhere it's checked
against a type, for example as a lambda's body in an argument
(`check.rs:438`, `541`). "Evaluation relies on this", as the function's
doc says: a `case` outside a definition's tree that gets stuck panics
(`value.rs:2482`).

Only a wrong elaborator or a wrong cache entry reaches it, and the result
is a panic, not a false theorem. **Fix:** the same check on each parameter
type in both functions.

### F4. The spec doesn't describe record eta or projections (severity 4)

`docs/core.md` has no `Proj(D, i, t)` in its Terms table, no typing rule
for it (`infer_proj`, `check.rs:690`), and neither of the two eta rules
(`value.rs:2290`, `3848`) in "Evaluation and conversion". Its one mention
is in the proof-irrelevance paragraph: "Record eta (D1981), if it's
added, must be limited to records with at least one field that isn't a
proof". It was added on 6 November, with that limit
(`qualifies_for_eta`, `check.rs:2691`). The comment above that function is
the best statement of the rules today, and D3210 says the spec should
carry them.

### F5. The spec's trust paragraph for the number natives is out of date (severity 4)

`docs/core.md:307` says registration "doesn't check a definition's body"
and that a library whose `Nat` definitions differ "is outside the
guarantees (SW-898)". Since SW-1885 the kernel's natives are bound only if
the definition's content hash is the pinned one (`pins.rs`,
`native.rs:497-502`), and the unpinned registration is behind
`test-bypass` (`native.rs:506`). The code is stricter than the spec.

### F6. `*`'s shortcut leaves a call "stuck" that isn't (severity 4)

SW-2572's shortcut for `(k + m) * n` returns `k·n + mul m n` with `mul m
n` built directly as a stuck call (`native.rs:1073-1079`). When `m` is a
call folded by name that computes, the case tree would have unfolded it;
the built value never does.

```
def two (n: Nat): Nat decreasing n :=
  match n with
    | 0 => 2
    | Succ m => two m

theorem base: two 0 * 3 = 6 := rfl            -- accepted
theorem viaSucc: Succ (two 0) * 3 = 9 := rfl  -- refused: true, and should be accepted
```

It refuses something true, never the reverse: the value is a correct lower
bound (`k·n` `Succ`s around the rest), so a conflict in index unification
or a number case's default taken from it is right. It's G9's shape, which
`docs/core.md` lists for `Nat.add` only. **Fix:** hand the rest back to the
evaluator (`Outcome::Again`) instead of building the call, or add `*` to
G9 and its ignored test.

### F7. The spec's status line (severity 4)

"Describes what's implemented in `crates/core` as of 16 October 2026." The
text has been kept up since; the date hasn't.

## What I read and found sound

Each line says what was checked, so the next audit can skip it or
disagree.

**Typing (`check.rs:233-895`).**
- `infer` and `check` for every term form match the spec's rules. An
  application needs the same implicitness; a constructor is checked
  against its own type's parameters and its result indices compared with
  the expected ones; `Refl` needs `conv`.
- `J`: the motive is checked as a type under `y: A` and `p: x = y`; the
  base against `P x rfl`.
- `infer_proj` needs the type itself, with eta (so final, one
  constructor, in `Type`), and gives later fields the earlier projections.
- `infer_quot`: C1 to C6 as its doc says. A quotient of a proposition is
  refused. `Quot.lift`'s result type can't depend on its argument.
- Universes: `Sort::succ` never saturates, `Sort::pi` is impredicative only
  for `Prop`, `fits_in` is checked for every field and every index.

**Case trees (`check.rs:905-1365`).**
- `E-PROP-ELIM`: one constructor, alone in its group, no nested or
  self-holding field, every field a proof (`field_sorts`), or every branch
  impossible. Probes: a witness out of an `Exists`-like proposition, a
  `Prop` out of a proof, a field out of a `Prop` record through `.w`: all
  refused.
- Refinement, and a second `case` on a variable already refined: the
  checker then knows less than the run, never more.
- `NumCase`: an arm is checked with the number, the default with the
  variable marked apart.

**`Apart` and SW-1819 (`value.rs:365-454`, `machine.rs:91-127`,
`check.rs:1369-1393`).** The change's argument holds:
- sets are only added, and a name is looked up by contents, so a name
  never changes meaning;
- `excludes` is right: every arm below `k`, or `k` more than a number in
  the set;
- a mark only appears in the default arm's context and is dropped with it
  (`check_num_case` restores `env` and `types`);
- `substitute_in` re-evaluates any value whose variable's mark differs
  from the context's (`clean_var`), so a glued call's shared unfolding
  made without the mark isn't reused with it, or the reverse;
- `Head`'s equality ignores the mark, which the tree memo and `identical`
  rely on: within one comparison a level has one mark.
- Probes: four attempts to carry a fact to another variable, another
  offset or a nested match; all refused.

**Index unification (`unify_index.rs:150-491`).** A conflict needs two
different constructors at a data type in `Type`; types, proofs and stuck
calls are stuck, never a conflict. A folded call is a neutral there.
`peel_succs` only takes off `Succ`s both sides have. The occurs check
follows types.

**Conversion (`value.rs:3381-4540`).**
- Every shortcut answers "equal" from equal arguments or nothing.
- Proof fields are skipped only in the normal mode; the shortcut mode
  compares them.
- Eta rule 1 compares each field with the projection, under the six
  conditions of `qualifies_for_eta`.
- The tree comparison walks both trees with the same fresh fields, and
  records a pair only after comparing it (no assumption that a pair in
  progress is equal).
- `TreeMemo`: the key has relation, mode, level and epoch; the memo is
  emptied when the outermost comparison ends, on an error too (`Drop`).
- `CallMemo` only answers "different" or skips a shortcut.
- Probes: 14 false equations over `*`, `-`, `+`, big numbers, division by
  zero, record eta, proof-only records and pairs of case trees: all
  refused.

**The evaluator's rules (`value.rs:1513-2180`, `2216-2312`).**
- `J` takes its base only on `rfl`; `Quot.lift` computes only on a
  `Quot.mk`; a projection only takes a field of its own type's
  constructor; a `case` takes a branch only on a constructor, a number or
  a compact list, or by eta rule 2.
- The erased placeholder: `J`, `branch` and `project` test `is_erased`
  without asking whether erasure is on. That's safe because every one of
  the nine places that make the placeholder is behind
  `erasure.active()`, which `in_kernel_modes` turns off, and a kept
  unfolding records whether it was made erasing (`Kept::fits`).
- The unused placeholder (`unused()`, for an argument no later type
  mentions) is only made where `Term::mentions` says the type doesn't use
  it, and `mentions` counts binders for every form, `case` and `NumCase`
  scrutinees included.

**The number natives (`native.rs:690-1242`, `pins.rs`).** Each of
`run_numbers`' arms against the definitions in `std/core/Data.sw` and
`Division.sw`: `sub` stops at zero, `divFuel` is `min(fuel, n / d)` and 0
for `d = 0`, `decEq` builds `Yes rfl` or `No (natNeq m n rfl)`. The partial
shortcuts are equations of the definitions. Registration checks the pin
first.

**Termination (`termination.rs:1-710`).**
- Every occurrence of a member is a call and must be saturated.
- A field is smaller only by matching; a `NumCase`, `J`, a projection and
  a quotient form give nothing.
- A rebuilt constructor: a field may differ from the matched one only if a
  later rebuilt field's type pins it. I tried to forge a proof field
  through a proof parameter (`PBox a`, which conversion skips): the
  forged value can't hold a member of the recursive group, because "no
  field depends on one holding `D`" refuses the type that would need.
  Sound as far as I can argue; this is the most delicate rule in the file.
- Probes: six non-terminating definitions, `decreasing` and structural:
  all refused.

**Admission (`check.rs:2105-2620`, `2980-3200`, `3293-3680`).**
- `in_kernel_modes` sets gluing off, the transparency set empty and
  erasure off on entry to every admission function, so a mode left on by
  a caller, or by an earlier panic, can't change what the next admission
  accepts. SW-1821's concern is real for the elaborator's values, not for
  the kernel's verdicts.
- A group's members have no body until all are accepted. A pending
  reference is refused; a failed one fails the group (except F2).
- Only four places make a declaration final: a checked or trusted group,
  a data group, and the `Delay` and float primitives, each of which checks
  the exact type and admits each primitive once.
- `transparency`: the list's members must be final and opaque, and the
  definition itself opaque.

**Positivity (probes only; `check.rs:3681-4212` not read).** Six attempts
through nested parameters, a lambda argument, a definition, a
continuation and an index: all refused.

**Freeing values (`value.rs:60-230`, `644-784`).** The iterative free
replaces parts with `Refl` only through `Rc::get_mut` or after a strong
count of 1, so a value still in use is never changed.

**Hashes (`hash.rs:100-200`, `530-700`).** The term walk covers every
form, with lengths, implicitness and impossible branches. `type_hash`
(SW-1937) is read only by the counterexample search's memo, which writes
notes on errors; nothing accepts or rejects by it.

**Rewind (`globals.rs:760-862`, `caches.rs`).** `forget_since` cuts
declarations, built-ins and the derived caches by id. `apart_sets` and the
budget are the operation's, and kept.

## What I did not read

- How the evaluator applies, unfolds and forces: `run`, `apply_step`,
  `force_call`, `unfold_now`, `unfold_folded`, `matches_at_once`
  (`value.rs:1215-1512`, `2489-2812`). Glued and folded calls were covered
  through conversion and probes, not line by line.
- Read-back (`value.rs:2842-3380`), `identical` and `shape_hash`
  (`4541-5240`), `Unchanged` (`check.rs:1860-2073`).
- `inert.rs`, `sct.rs`, `nat_add.rs`, `chars.rs`, `reference.rs`,
  `budget.rs`, `erase.rs`, `step.rs`, `registry.rs`.
- `float.rs`'s arithmetic. The primitives have no bodies, so any total,
  deterministic function is consistent; the risk there is a result that
  differs between the native and WebAssembly builds, not a false theorem.
- The positivity and nestable-parameter code, and `add_validator`.
- The check cache's encoder and key (`crates/elab/src/cache`), beyond what
  F1 needed.
- The elaborator. Probes went through it, so a kernel hole it never
  reaches would not show.

## For Matt

- **F1 is a decision about trust:** whether a cache directory may be
  trusted when it comes with a project. Recommendation: key the entries
  per user, outside the project.
