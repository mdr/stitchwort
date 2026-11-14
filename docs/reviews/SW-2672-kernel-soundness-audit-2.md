# SW-2672: kernel soundness audit, part 2

10 November 2026, on `main` at `b8b1c33b4`. A paper lane, the second half of
[SW-2659](SW-2659-kernel-soundness-audit.md): the code that audit listed as
not read. The code was read, and suspected holes were tried as small `.sw`
probes against the release CLI already built (`stitchwort check
--no-cache`). No test suite was run.

The question is the same: is there any way a false theorem gets accepted?

## Verdict

**I found no way to make the kernel accept a false theorem, and no likely
hole.** In particular I found no non-terminating definition that the
size-change check accepts: the algorithm in `sct.rs` is the published one,
the graphs `termination.rs` gives it claim "smaller" only for real parts of
a matched value, and over 30 non-terminating definitions written to slip
past it were all refused.

What I did find is small:

- two guards that hold today only because every caller behaves (severity 3);
- one more note for SW-2673 (check cache trust);
- two termination rules the kernel spec doesn't state (severity 4).

Counts: 0 at severity 1, 0 at severity 2, 3 at severity 3, 1 at severity 4.

**Limits.** Every probe went through the elaborator, which refuses most
false statements before the kernel sees them. So the probes show that the
two together hold; the claim that the kernel alone holds rests on the
reading. Between the two parts about 15,000 of `crates/core`'s 27,300
lines have now been read; "Not read by either part" lists the rest.

## Findings

| # | Sev | Where | Finding |
|---|---|---|---|
| G1 | 3 | `crates/core/src/value.rs:3278` | Read-back checks that a variable is in scope only in debug builds; in a release build an out-of-scope variable, or either placeholder, becomes a plausible index |
| G2 | 3 | `crates/elab/src/cache/codec.rs:237`, `272`; `crates/elab/src/cache/mod.rs:1118` | The cache's term writer shares nodes by address and nothing keeps the terms alive or stops a caller passing a temporary |
| G3 | 3 | `crates/elab/src/cache/mod.rs:2671-2688` | After a replay, the hashes the entry states are installed without being computed, so later entries' dependency checks trust them (add to SW-2673) |
| G4 | 4 | `docs/core.md:153-160`; `crates/core/src/termination.rs:250`, `641` | The spec's termination rule leaves out two things the checker does: a rebuilt constructor may differ in a field a later field's type pins, and a lifted `match` used once is inlined |

Severity: (1) a false theorem accepted; (2) a likely hole, unconfirmed;
(3) a missing guard; (4) a gap between spec and code.

### G1. Read-back's scope check is debug-only (severity 3)

`visit` turns a variable at level `l` into the index `level - 1 - l`, after
`debug_assert!(l < level)` (`value.rs:3278`). The workspace sets no
`overflow-checks` for release builds, so there the assertion is gone and
the subtraction wraps.

- For an ordinary variable with `l >= level` the index is huge, and
  evaluating the term anywhere panics on the environment lookup. That is
  loud, so it's safe.
- For the two placeholders it isn't loud. `unused()` is the variable at
  `usize::MAX` (`value.rs:806`) and `erased()` the one at `usize::MAX - 1`
  (`erase.rs:64`). Read back with `level` variables in scope they become
  `Var(level)` and `Var(level + 1)`: ordinary-looking indices one and two
  past the context. Evaluated at the same depth they panic. Evaluated
  under one or two more binders they name a real variable.

**Why it isn't a hole today.** `unused()` is only put in an environment
slot the body doesn't mention (part 1 checked `Term::mentions`), and
`erased()` is only made while a program runs, which `in_kernel_modes` turns
off. So neither should ever reach read-back in the kernel, and a term
read back at one depth is evaluated at that depth. I found no path to it.
Confidence that it's unreachable: fairly high, not certain; the kernel's
read-backs whose terms are evaluated or checked again (`check.rs:632`,
`975`, `1318`, and `Rebuild::read_back` at `1803`) all rely on it.

**Fix.** Make it a real check: `level.checked_sub(l + 1)` and an internal
error (or panic) otherwise. One comparison per variable read back. The
same file has the two other debug-only checks worth the same treatment:
`float_value`'s `debug_assert!(is_valid(bits))` (`float.rs:709`), where an
invalid result would be a record holding `rfl` as a proof of something
false (unreachable: every caller passes `canonical_bits` of an `f64` or a
sign flip of valid bits), and `unify`'s length check
(`unify_index.rs:151`), where a short side panics on indexing anyway.

### G2. The cache's term writer shares nodes by address, unguarded (severity 3)

`TermWriter` writes each term node once and finds it again by its address:
`ids: HashMap<*const Term, u32>` (`codec.rs:237-246`), filled in `term`
(`codec.rs:272-293`). The addresses stay in the map for the whole entry,
but the writer holds no reference to the terms and `term` takes a plain
`&Term` with no lifetime tied to the writer. If any caller passed a
temporary (a term built in a loop, a clone), the next temporary at the
same address would be taken for the first and written as a reference to
it. The entry would then decode to a different term than was encoded, and
a trusted replay installs what it decodes without checking it.

**Why it isn't a hole today.** I checked every call of `Encoding::term`:
the kernel's declarations (`mod.rs:1592-1659`) are borrowed from the
environment, `unfolding_refs` is a vector that lives for the whole
encoding (`mod.rs:1498`), and the elaborator's tables encode rows borrowed
from the tables (`state/table.rs:135`, `cache/rows.rs:341-345`,
`mod.rs:1126-1142`). All outlive the writer. The kernel's declarations are
also written first, so a temporary in a later table could only collide
with another temporary. Confidence: high.

The evaluator's `ShapeCache` has the same design and does guard it: it
keeps an owner for every address it remembers (`value.rs:4559-4573`).

**Fix.** Give `TermWriter` (and `Encoding`) the lifetime of the terms it
has seen, so `term` takes `&'t Term` and the borrow checker refuses a
temporary. No run-time cost.

### G3. A replayed entry's stated hashes are installed, not computed (severity 3; add to SW-2673)

When a replay succeeds, `admit_replayed` puts the content hash the entry
states for each declaration into the kernel's hash cache
(`mod.rs:2671-2688`), "rather than hashing the terms again". Every later
entry's dependency check (`decode`, `mod.rs:2361-2376`) then compares
against those.

This is the trust SW-2673 is about, with one more consequence worth
writing on that ticket: the dependency check does not tie a later entry to
what was actually installed, only to what the earlier entry said was
installed. So a wrong decode (G2, or any future codec bug) in one entry is
invisible to every entry built on it, and a forged entry need only state
the honest hash to keep its dependents loading.

The pins are not affected: built-ins are bound during `submit`, before the
stated hashes are installed, so `pins::check_def` hashes the terms.

**Fix.** Whatever SW-2673 decides, a cheap guard is a mode (always on in
tests, and in `audit`) that computes each replayed declaration's hash and
refuses the entry if it differs from the stated one. That turns every
round-trip bug in the codec into a counted refusal (`Stats::refused`).

### G4. Two termination rules the spec doesn't state (severity 4)

`docs/core.md`, "Definitions", step 4, says an argument is related to a
parameter when it is "a constructor applied to exactly the fields of a
match". The checker does two more things, each stated in
`termination.rs`'s own comments and not in the spec:

- **Pinned fields** (`Walker::rebuilt`, `termination.rs:641-683`,
  `pins_var` at `371`). A rebuilt constructor may have any term in a field
  that a later rebuilt field's type pins (`n` in `VCons [n] x xs`, written
  `Succ m` by the elaborator). Part 1 called this the most delicate rule
  in the file. I went through it again (below) and agree it is sound, but
  the argument needs two facts from elsewhere in the kernel, so it belongs
  in the spec with them.
- **Inlining** (`inlined`, `termination.rs:250-287`). A member whose name's
  last part starts with `%match`, occurring once, in another member, is
  walked where it occurs and makes no graph of its own. Soundness doesn't
  depend on the name (inlining any once-used member is as sound), but the
  kernel is reading an elaborator naming convention, which the spec
  should say.

D3210 says the kernel spec carries the kernel's rules. SW-2670 is open for
`docs/core.md`'s gaps and could take this.

## What I read and found sound

Each line says what was checked.

### Size-change termination (`sct.rs`, all; `termination.rs`, all)

**The algorithm (`sct.rs`).**
- A graph holds, for each parameter of the callee, at most one arc from a
  parameter of the caller. `compose` follows the second graph's arc into
  the first's and is strict if either arc is (`Label::then` is `max`,
  `Lt > Le`). An unknown stays unknown.
- The closure starts from every call and extends each graph on the right
  by every call that starts where it ends. That reaches every nonempty
  path. No identity graph is added.
- Every new graph is tested: idempotent, from a member to itself, and no
  `<` from a parameter to itself fails the group. Graphs with the same
  ends are kept apart (the set is keyed by the whole graph).
- Running out of budget or of the 100,000-graph limit is an error, never
  an acceptance. `failed.or(add(...)?)` still runs `add` for every call.

This is Lee, Jones and Ben-Amram's criterion for graphs with fan-in one,
which composition preserves.

**The graphs (`termination.rs`).** The claim `<` or `≤` is made in exactly
these places, and each is true of values, not types:
- a variable bound by a `Case` on a variable that is a parameter or
  already smaller (`walk`, `Term::Case`): a field of a matched value;
- a recursive function field applied to arguments (`relate`,
  `is_recursive_fn`): only the field variable itself, only when its
  declared type ends in a member of the matched type's group, and only
  when the variable is already smaller;
- a constructor rebuilt from a match's own fields (`rebuilt`): the same
  constructor, the same number of fields, each the match's own variable
  (or pinned, below), so it is the matched value;
- a `let` whose value is one of the above; an inlined member's parameter
  whose argument is one of the above.

Everything else is unknown: lambda variables, results of other calls,
`J`, projections, quotient forms, numbers. A `NumCase` binds nothing.

Every occurrence of a member is a call or an error: `walk` covers every
term form, and `occurrence` refuses fewer arguments than the arity.
Arity is the body's count of leading lambdas, checked equal for every
member, so "saturated" means every parameter has an entry.

**Pinned fields.** A field `j` may differ from the matched one if a later
field `k` is the match's own variable and its declared type is a data type
with field `j` as an argument. The body type-checked, so the two types of
field `k` are convertible, so the two values of field `j` are convertible.
Convertible is not identical in one case: a data type's proof parameter is
skipped by conversion, so a proof field can be replaced by any other proof
of the same proposition. I tried to turn that into a loop. It needs the
replaced proof to hold a value the recursion can continue on, at a type
the function accepts:
- a proposition declared with the data type, holding it: refused, "no
  field depends on one holding a member" (`check.rs:3143-3149`);
- the data type nested in an earlier proposition (`Wrap D`): the same rule
  (`holds` counts nested occurrences);
- the data type's own parameter, instantiated later with a proposition
  that holds it: that parameter isn't nestable, because a later field
  mentions the field that holds it (`param_nestable`, condition 5);
- a proposition that holds a value of any type (`MkAny (a: Type) (v: a)`,
  which is accepted in `Prop`): the type can't be recovered, since the
  match can only produce a proof and nothing refines `a`.

In every case the forged call is also only `≤`, never `<` (probe: "the
1st argument stays the same"). I agree with part 1: sound as far as I can
argue.

**Inlining.** The cycle-breaking loop leaves at least one member of every
cycle of inlined members walked, so no body goes unwalked. An inlined body
is walked with its parameters standing for the arguments at the one place
it's used, and its calls are recorded as the caller's. A once-used
function that isn't recursive itself terminates on every input when the
members it calls do.

**What the argument assumes**, as the file's header says: every data
type's values are well founded. For nested types that rests on the
relabelling to the mutual encoding, "believed but not proved"
(nested-data-types.md §6.3, C1). For a proposition with an impredicative
field (`MkD (f: (p: Prop) → p → D)`, accepted, with `loop: D → Void`
accepted) it is the usual argument: recursion over such a type only
produces proofs (`E-PROP-ELIM` refuses a self-holding type), and the type
is the least fixed point of a monotone operator on truth values.

**Probes:** 33 non-terminating definitions: swapped arguments, a rebuilt
constructor with one field changed, lengthened, or taken from another
match, vector indices, function fields rebuilt by eta or passed to another
parameter, `let` aliases, an inner match on a call's result, lambdas, and
mutual wrappers. All refused. The 13 most delicate were written with one
suspicious call each, so that another call's error couldn't hide an
accepted one.

### Positivity and nestable parameters (`check.rs:3681-4212`, `3079-3200`)

- `not_positive` runs on each field's checked type. A member may appear
  as itself with the group's own parameter variables and member-free
  indices; after function inputs that don't mention any member; or inside
  an earlier, final data type at nestable parameters only, each argument
  checked by the same rule under its leading lambdas. Anything else
  (a definition applied to it, a variable applied to it, an equation, a
  quotient, a `let`, an annotation) is refused: the rule is syntactic and
  falls through to "inside something that isn't a data type".
- `occurs` counts `Data` and `Case` nodes over every sub-term.
- `param_nestable`'s five conditions are the ones its comment gives, and
  `stored_only` mirrors `not_positive` for a parameter. A parameter
  applied to arguments that mention it, or passed to a definition, isn't
  nestable.
- A field can't use anything declared after its type (`declared_later`),
  and a constructor's result indices can't mention the group.
- A data group has one universe; fields and indices must fit in it.
  `Type → Type` as an index of a type in `Type` is refused, as is a
  `Type` field.
- Probes: a type in its own index type, negative occurrences through a
  nestable parameter, a function field reached through `Box`. Refused or,
  where accepted, correctly so.

### The evaluator's calls (`value.rs:1215-1512`, `1905-2095`, `2165-2180`, `2313-2812`, `835-960`)

- `unfold_now`: a hidden opaque definition never unfolds, before the
  natives are tried. A float primitive runs only on known, valid bits. A
  body runs only with all its arguments, none of them a `J` or a
  projection.
- `force_call`: a field of a call forces the call without the field,
  through that call's own unfolding cell, then projects.
- `Frame::CallField`, `eta_fields`, `unfold_folded`, `FieldOf`: a stuck
  field of a call, `(f x).i`, is a name for the projection of what `f x`
  computes to. It is only made when that is a neutral, so the projection
  is stuck too; `unfold_folded` and `FieldOf` compute it by running the
  call's tree and projecting.
- Kept unfoldings (`Kept::fits`): reused only in the same modes and
  transparency set, at epoch 0 or the current one.
- **The principle that makes the rest safe:** nothing in the kernel
  treats "this value is stuck" as a fact. A stuck call against a
  constructor is `Stuck` in index unification, a `NumCase` on a neutral
  doesn't step, and conversion answering "different" proves nothing. So a
  value that is neutral only because a body wasn't visible when it was
  made (a group member, a stale kept unfolding) costs completeness, never
  soundness.

### Read-back (`value.rs:2842-3380`) and `Rebuild`/`Unchanged` (`check.rs:1366-2073`)

- `quote_as`: indices are `level - 1 - l` (see G1); closures are entered
  with a fresh variable at `level`; a spine is rebuilt in order with its
  implicitness, `J`s and projections; a glued call is written as the call
  with its arguments (folded) or as its forced unfolding (unfolded). Both
  mean the same.
- `Rebuild` computes `eval(ρ, quote(v))` directly for variables,
  constructors, data types, equations and applied variables, and reads
  everything else back. Its memos are by the address of fields and spines
  borrowed for the whole substitution.
- `Unchanged` keeps a value only if no variable in it is the substituted
  one and every variable's `Apart` mark is the context's. It refuses
  closures, definitions, metavariables and quotient heads. A kept glued
  call is judged by its arguments, which is right: its unfolding is a
  closed definition applied to them.

### `identical`, the memos and `shape_hash` (`value.rs:4318-5240`)

- `identical` answers "alike" only for the same structure: closures by
  body term and by the environment values of the body's free variables
  (`free_variables` uses `Term::subterms`, whose binder counts I checked
  form by form, `term.rs:730-785`). Two calls with one unfolding cell are
  the same call, since a cell is only made with its call
  (`project_call` makes a new one for a field).
- `shape_hash` is only a filing key. `TreeMemo::known` and
  `ShapeMemo::contains` answer from a pair only after `identical` on both
  sides, so a collision costs time, not an answer.
- `same_trees_of` compares the branches of two stuck trees with the same
  fresh fields and the scrutinee left as it is, not replaced by the
  constructor. That compares more general terms than needed, so "equal"
  still holds after the replacement. It never enters a `NumCase`
  (`TreeEnd::Other`), so conversion never adds an `Apart` mark, which is
  what lets the memo ignore marks. Two `case`s with no possible branch
  are equal without comparing scrutinees: both scrutinees have empty
  types.
- The memo reuses an answer for an identical pair at the same level under
  different fresh variables. That's right because conversion is a
  function of the values alone: it never looks up a variable's type.

### `inert.rs` (all)

A candidate must have a type in `Prop` (`candidates`, by `sort_of`). So
whatever the analysis decides, skipping the argument is proof
irrelevance on two proofs of one proposition, because the earlier
arguments were compared or are themselves skipped proofs. A wrong mark
would cost transitivity, not consistency. The analysis itself matches its
comment: every occurrence other than the three allowed clears the mark,
over a greatest fixed point. An error gives the group no marks.

### `nat_add.rs` (all)

`stuck` reads the second argument only when the first is stuck: a number
`k` gives `k` `Succ`s around `m`; `k + n'` gives `k` `Succ`s around `add m
n'`; anything else stays stuck. Both are R4 `k` times then R3 or nothing,
equations the prelude proves. `register` binds the rules only to the
pinned `Nat.add` and checks the two theorems' types. `reread` only unfolds
what the evaluator could.

### `chars.rs` (all)

A range can only be made within its buffer. `split` gives `Nil` or `Cons
(MkChar c rfl) rest`; the `rfl` is true because a Rust `char` is exactly
what `Char.isScalar` accepts (checked against `std/core/Char.sw:11`) and
the declarations are pinned by hash. The shared table is indexed by code
point over 0..256, all valid. Probes: index unification between two
literals, a literal and a list, and a literal and a list with a variable:
a conflict only where the lists differ.

### `float.rs` (all of the kernel's part, 1-335 and 560-880)

- Only the primitives reduce while checking; the natives need a running
  program. A primitive reduces only on records of the bound `Float` whose
  bits are known and valid, and returns `canonical_bits` of an `f64`,
  which `is_valid` accepts: every non-NaN pattern, and the one NaN.
  `is_valid`'s four constants are `Float.isValid`'s (checked digit by
  digit against `std/Float/Float.sw:34-36`).
- `nat_to_f64` rounds to nearest, ties to even, with the sticky bit from
  `trailing_zeros`; over 1024 bits is infinity. `js_round` follows the
  specification's cases.
- The primitives have no bodies, and the library has no axioms about
  them (it has no way to state one: a declaration without a body is
  `E-MISSING-DEFINITION`, and a program can't add to `Float`'s
  namespace). So any total, deterministic function is consistent, and
  `*`, `/`, `%`, `floor`, `ceil` and `trunc` are IEEE operations with one
  result on every platform.
- Probes: 13 equations over `*`, `/`, `%`, `round`, `ofNat` at 2^53 + 1,
  the zeros, the NaN and overflow. True ones accepted, false ones
  refused.

### The check cache's encoder and decoder (`cache/codec.rs`, all; `cache/mod.rs:960-1150`, `1490-1700`, `1860-2000`, `2350-2500`, `2580-2690`)

Read for one question: can an entry decode to something other than what
was encoded?

- Every term form but `Meta` is written with all its parts, in the order
  the reader takes them (`App`, `Pi`, `Let`, `J`, `NumCase` checked
  argument by argument). Children are back-references to earlier nodes,
  and the reader's arithmetic is the writer's. Numbers, text, universes
  (capped at `MAX_LEVEL`), implicitness, the erasure flags, optional
  parts (`Eq`'s type, an impossible branch) all round-trip.
- References: a declaration of the entry is an offset from the entry's
  first; anything else is an index into the header's dependencies, each a
  kind, a full path that must name one declaration, and a content hash
  that must match now. Both sides index one combined list.
- Sharing is by address (G2), safe for today's callers.
- Each declaration's flags are written and read; `eta`, the nestable
  parameters, the inert marks and `lift_leaf` are recomputed.

So: no, apart from G2's unguarded invariant. The key's completeness I did
not read (below).

### Probes through the surface language

About 110 statements in 23 files, counting the ones named above. The rest:
- quotients: `Quot.mk` is not injective in index unification (stuck), `J`
  doesn't compute on `Quot.sound`, `Quot.lift` needs its proof;
- proof irrelevance: a proof's constructor is not injective in index
  unification (stuck), and a constructor's proof field is skipped there
  without a conflict;
- type constructors are neither injective nor disjoint (stuck);
- record eta and fields of calls, including a `decreasing` definition
  that returns a record, and `Map`: three true equations accepted, ten
  false ones refused;
- number cases and their default arms, with `+` on either side and `*`,
  with text and lists: 18 false equations refused, and seven theorems
  with a wrong `rfl` in a `match` branch refused at that branch;
- declarations without bodies, and attempts to redeclare `Float.mul` and
  `Effect.now`: refused;
- an open goal: `check` and `audit` both fail, and so does everything
  that uses it.

Nothing false was accepted.

## Not read by either part

In `crates/core`:
- `reference.rs` (the second evaluator, used by tests and `run
  --reference`), `step.rs` (running `Delay`), `erase.rs` beyond the
  placeholder, `budget.rs`, `backend.rs`, `machine.rs` beyond
  `in_kernel_modes`;
- `registry.rs` and `globals.rs:1-760` (how built-ins are bound and
  declarations stored), `native.rs:1-690` beyond what part 1 says of
  registration, `hash.rs:330-530`;
- `pretty.rs`, `determined.rs`, `js_repr.rs`, `ev.rs`, `env.rs`,
  `collections.rs`: display, extraction and plumbing;
- `shape_hash`'s body past its first 80 lines (it can't change an answer).

Outside it:
- the check cache's key (`Elaborator::library_interface`, the namespace
  keys, `crates/driver/src/check_cache.rs` beyond what F1 needed) and its
  tables' replay. A key that misses an input would report a source as
  checked from an entry made for another;
- the elaborator, and so whether it can build a term the kernel accepts
  wrongly that no surface program of mine reached;
- the runtimes and JS extraction, which decide whether a run computes
  what was checked, not whether a theorem is true.

The most useful next step is not more reading: it is a way to give the
kernel core terms directly (a fuzzer or a small text format for
`crates/core`), so that its checks are tried without the elaborator in
front of them.

## For Matt

Nothing here needs a decision. G3 is one more fact for the SW-2673
decision (whether a cache directory is trusted).
