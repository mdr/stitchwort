# SW-4796: rule S reads a parameter's type through a definition (review)

Fable paper review, 25 Nov 2026, of `lane/SW-4796` at `cb3396336`
(`value::parameter_type`, `reference::type_at`, docs/core.md, example
39b). Read from the code; nothing was built. Five small scratch files were
checked with the lane's binary and main's; where a claim rests on one, it
says "checked". Everything else is by reading.

**Verdict: merge.** The change is sound, the two evaluators agree, and I
found no checked tree that still declines. Three small follow-ups, none
blocking: more cases in example 39b (finding 1), a hedge in one docs
sentence (finding 2), and the reference validator's own as-written walk
(finding 3).

## Soundness

Rule S fires when the scrutinee's type, as read, is `D ps is` with the
constructor's result indices equal to `is`. The argument needs the type
read to be the scrutinee's real type, up to conversion. The new reading is
the definition's type evaluated, each function type forced and its
codomain applied to the actual arguments before the scrutinee: that is the
application rule's type for that argument. Forcing only unfolds real
definitions, which preserves meaning under any transparency set (opacity
hides, it never changes what a definition is). So the type read is equal
to the one the old code read wherever the old code read one, and correct
wherever the old code gave up. Nothing new is accepted that isn't true;
the change only removes a decline.

## The lane's questions

**1. Transparency: can the reading differ by evaluator or path? No.**
Both evaluators decide "hidden" with the same `value::hidden` under the
same `Machine::transparent` (`reference.rs:530`, `:594`), so they read the
same type. The only setters of the set in `crates/core` install a
definition's closed set or the empty one (`check.rs:2839`, `:3282`,
`:5280`, `erase.rs:215`, `determined.rs:165`; the rest set empty); the
elaborator's two (`elab/src/opaque.rs:180`, `lib.rs:4315`) call the
kernel's `transparency_set`. A tree runs only where its definition
unfolds. If the definition is transparent it has no `unfolding` list
(`E-UNFOLDING-TRANSPARENT`; checked), so its arms were typed with nothing
unfolded and any set reads at least that much. If it is opaque, the caller
holds it in its set, and the closure (`check.rs:3483-3486`) puts the
definition's own set there too; the trusted path computes sets with the
same code (`install_group`), so a cache hit is no different. A larger set
can only unfold more of the type, to an equal value. A kept unfolding
records its set, kernel flag and program flag (`Kept::fits`), so a replay
under another set recomputes. While a program runs everything unfolds,
which a fresh `eval` sees.
Checked: `opaque def useH … unfolding h` (without `Hidden`) and
`theorem … unfolding useH` compute `useH pf` and `useH s` to 5 on the
lane's binary, in the elaborator and the kernel; main fails both.

**2. Glued unfoldings: no conflict.** `eval(def.ty())` makes a fresh
value each time, so its calls' unfolding cells are new and filled under
the current modes; nothing is shared with `Def::ty_value`, which is where
kernel and elaborator readers meet. The forcing happens before
`meet_in_evaluation` reserves its block of levels, and any test met while
forcing the type reserves and releases its own. The arguments given to the
codomains are the same environment values the old code evaluated the
domain in, so the reserved-level argument (audit finding A) is unchanged.

**3. Is the decline unreachable in checked trees? I found no reachable
case.** Tried and computing on the lane's binary (all stuck on main):
a codomain behind a definition after an argument (`def Rest (x: Nat): Type
:= Q2 x → Nat`, `def f2: (x: Nat) → Rest x`), and a recursive type
function (`def Fam: Nat → Type | 0 => Nat | Succ n => (q: Q2 0) → Fam n`,
`def f4: Fam 2 | MkQ2 w, MkQ2 v => 5`, with `f4 pf pf`). One theoretical
case stays, outside what the elaborator builds: a tree whose later
parameter is a function type only under an earlier branch's refinement
(`f: (b: Bool) → IsTrue b → T b` with three lambdas). The elaborator
refuses that arity (`E-ARITY`; checked), and when such a branch is reached
by iota, rule S or eta the earlier arguments make the type compute the
same way, so I believe it computes there too; I didn't prove it. If it
ever declined it would be the old incompleteness, not unsoundness.

**4. Cost: small; keep `eval`, not `ty_value`.** Evaluating a function
type builds its first domain; each codomain application builds the next.
So a test on parameter `L` now evaluates the domains of parameters
`0..L`, where the old code evaluated only `L`'s. Glued (ordinary
checking) those are lazy calls; unglued (`byComputing`) they are computed,
so a signature with real computation in an earlier parameter's type, in a
recursion that fires rule S on an indexed proposition at every step, pays
that per step. I know of no such definition in the repo; the budget
counts the steps, so the failure mode is `E-RESOURCE`, never a wrong
answer. `ty_value` would not help: it saves one `eval` of a `Pi` node,
and it was evaluated with every opaque definition hidden for good, so it
is wrong under a non-empty set and while a program runs
(`check::def_type` covers the first, not the second).

## Findings

### 1. Example 39b covers only a nickname at the top of the type (low)

Every case in `examples/accept/proof-irrelevance-39b-alias-signature.sw`
has the nickname as the whole type, so only the first `force` in
`parameter_type` / `type_at` is exercised. The force after a codomain is
applied has no test. Add the two shapes from question 3 (`f2: (x: Nat) →
Rest x` with `f2 0 pf`, and `f4: Fam 2` with `f4 pf pf`) and their values
for the differential test. Both pass on the lane's binary and fail on
main (checked, kernel only; I could not run the reference evaluator).

### 2. docs/core.md line 310 says "never meets" a little too firmly (low)

"…which a tree checked under the transparency rule never meets" is
argued only for opaque nicknames. The refinement-dependent case in
question 3 is not covered by that argument. Suggested wording: "which no
tree the elaborator builds meets, since it counts a definition's
parameters from its type with nothing refined; for an opaque nickname,
arms over it need it in the definition's set…". Line 374's sentence is
exact.

### 3. `reference::validate_marks` still reads the type as written (low; validator coverage, not the kernel)

`reference.rs:1763`, `validate_pi_marks` (`:1792`) collects binder marks
by walking `Term::Pi` over `def.ty`, and `:1767` compares the body's
lambda marks only against those. For `def f: Reader` it collects none, so
the "each parameter's lambda against its type's binder" check
(docs/core.md, "Proof marks") is skipped for every definition with a
nickname signature. The kernel derives those marks from the computed
function type, so nothing is wrong today; the independent check just
doesn't look. Worth a ticket.

## Other walks of a definition's type as written, in `crates/core`

| Where | What it reads | Matters? |
|---|---|---|
| `reference.rs:1763`, `:1792` (`validate_pi_marks`) | binder marks for the mark validator | finding 3: coverage only |
| `pretty.rs:1966` | whether a call's result is `Prop`, for display | display only |
| `pretty.rs:2767` (`call_with_defaults`) | parameter names for default arguments | display only |
| `pretty.rs:2999`, `:3042` | whether a definition is a record projection | display only |
| `pretty.rs:3155` | explicit parameter count for dot display | display only |
| `registry.rs:855` (`shape_of`) | a builtin's binder shape; documented as not unfolding | registration of builtins, whose types are written out |
| `hash.rs:170` and others | hashes the type term | intended: the hash is of the term |

Not a definition's type, noted for completeness: `check.rs:4946`
(`is_arity`), `check.rs:4970` (`stored_only`) and `termination.rs:484`
(`is_recursive_fn`) walk a data type's parameter or field types as
written. They are classifications where missing a function type behind a
nickname is the cautious side as far as I read them; I did not review
them. `native.rs:445`, `float.rs:589`, `nat_add.rs:392` build an expected
type and compare by `conv`, so they see through nicknames. `erase.rs:292`
and `check::proof_telescope` read the evaluated type. I did not look
outside `crates/core`.
