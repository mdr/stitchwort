# Proposal: don't store constructor fields the type's indices determine

**Status:** Draft 1, 8 November 2026 (SW-2406, from D3426). Design only:
nothing was built or run for it. The questions for Matt are in
[§9](#9-open-questions). It reverses half of D141 for the fast runtimes
only; the kernel, the reference evaluator and every proof stay as they are.

Claims about Stitchwort were checked at commit `d15ae50e2`, plus SW-2398's
WIP commit `bf4936b9e`. Labels:

- **[checked: S]**: read in S (a file in this repository, or a URL);
- **[inferred]**: my reasoning from checked facts;
- **[estimated]**: a number reasoned out, not measured;
- **[from memory]**: believed, not confirmed against a source here.

## 0. Summary

- **The problem.** At run time, an indexed family's constructors store the
  index they're at. `FSucc (FSucc FZero): Fin 4` lowers to
  `FSucc(4, FSucc(3, FZero(2)))`, and `Fin.toNat` reads the stored `n` to
  pass its own implicit argument down [checked: SW-2398's snapshot
  `it__lower__nat_shaped_types_are_numbers.snap`]. D141 chose this on
  purpose, and left erasing such fields to "a separate change with its own
  argument that the representations agree" (indexed-families.md, D141). So
  `FSucc` has two run-time fields, `Fin` isn't shaped like `Nat`, and
  nat-shaped-types.md (D3423, D3424) picks up nothing in std or `aoc/`. Every
  `VCons` cell also carries a length it doesn't need, and every
  construction computes it.
- **The change.** A constructor field whose value can be read back from the
  constructor's result type (FSucc's `n`, in `Fin (Succ n)`) isn't stored by
  the fast runtimes (interpreter, native code, JS). Where a match binds such
  a field and the branch uses it, the backend rebuilds it from the
  scrutinee's type, which the program already has at run time: the matched
  `i: Fin n` has its `n` in a variable, so FSucc's field is `n - 1`. One
  function in `stitchwort_core` says which fields are determined (by the
  declaration alone, like `nat_shape`), and one says how to rebuild each at
  each match (by replaying the kernel's own index unification for that
  match, outside the kernel). Every backend calls both, so they agree.
- **What it should do.** `Fin` becomes Nat-shaped, so SW-2398 and
  nat-shaped-types.md's natives apply to it: a `Fin` is a machine number
  and `Fin.toNat` the identity (nat-shaped-types.md §8.1: a `Fin`-indexed
  array read becomes one bounds check instead of a walk). A `VCons` cell
  goes from three fields to two, and its length is no longer computed when
  it's built **[estimated: a word and a field store per cell, plus whatever
  the elaborated length term cost]**. The kernel is untouched, and no proof
  depends on the runtime.
- **Work.** About 4-5.5 lane-hours in two stages, then SW-2398 finishes
  ([§8](#8-stages-and-estimate)).

## 1. What Stitchwort does today

### 1.1 D141, and why

indexed-families.md (SW-178) decided, as D141: "Keep computational fields,
forced implicit ones (like `n` in `VCons`) included, and keep implicit
index parameters at run time, as DESIGN.md §6 says; proof fields are erased
by the existing rule. … Erasing forced fields (Brady–McBride–McKinna) or
Idris-style quantities come later, as a separate change with its own
argument that the representations agree" [checked: indexed-families.md
§12, D141; §6.8]. DESIGN.md §6 says the same: "Data indices like a
vector's length are **not** erased … which is acceptable since performance
isn't a goal" [checked: DESIGN.md:465].

What it protected, reading the note and its review:

1. **Simplicity of the first family lane.** Erasure stayed one rule
   (`Ctor::field_erased`: proofs and type formers), shared by every runner;
   families needed no new run-time machinery.
2. **One representation everywhere.** The reference evaluator, the fast
   runtime and JS all store the same fields, so "with and without erasure"
   driver tests compare like with like.
3. **No reconstruction to get wrong.** A stored field is read, never
   recomputed, so there's no argument to make that a rebuilt value is the
   right one.
4. **Termination (D143).** "A stored constructor field, implicit ones
   included, is a structural subterm of the value": the implicit `n` in
   `VCons [n] x xs` is smaller than the vector [checked: §6.7].

What it cost, also in the note: a stored implicit field costs whatever its
elaborated term costs (`fromList` as written was quadratic, 2.8 s for 4,000
elements against 0.11 s without the field) [checked: §8.1, measured there].

This proposal reverses only the first half of D141, and only on the fast
runtimes: **implicit index parameters of functions stay at run time**, and
this design depends on that (§3). Of what D141 protected: (1) is the cost
this note pays; (2) changes, because the reference evaluator keeps storing
the fields, which makes it an independent check of the rebuilt ones (§6);
(3) is §3's argument, plus a debug check; (4) is about kernel terms, where
the field is still a field, so it doesn't move (§6.3).

### 1.2 Where the fields are stored and read

- **The kernel** stores every field in `Value::Data` and compares indices
  in conversion [checked: indexed-families.md §6.8]. Unchanged.
- **The reference evaluator** (`stitchwort run --reference`, `stitchwort
  test`) is the kernel's machine with `Erasure::running`; it skips fields
  marked `field_erased` and stores the rest [checked: `erase.rs` rule 2;
  docs/core.md:242]. Unchanged by this proposal.
- **The fast runtime** (`crates/rt`, interpreter and native code from one
  `Image`) lowers a match by walking `field_erased`: an erased field is
  `Bind::Erased`, every other one gets a slot loaded from the cell if the
  branch uses it [checked: `crates/rt/src/lower.rs:1141-1270`]. Its layout
  is read at 7 sites in `lower.rs`, `clauses.rs` and `effect.rs`.
- **JS** does the same at 16 sites in `crates/js/src/lib.rs`, `effect.rs`
  and `run.rs`, plus `crates/core/src/js_repr.rs` [checked: grep of
  `field_erased`]. Families can't cross the JS boundary (`E-EXPORT`, D147),
  so no codec or `.d.ts` is involved [checked: indexed-families.md §6.8].

`field_erased` is also read by the kernel (`check.rs`, `value.rs`) and the
elaborator (deriving, `Show`, the counterexample search, the cache). Those
uses are about proofs and types, not layout, and stay on `field_erased`.

### 1.3 Who reads a determined field at run time

The families with run-time values in std are `Fin` and `Vec` (and `Grid`,
built on `Vec`); `Effect.AlwaysTreeOf` is a proposition, erased whole
[checked: grep of `type … → Type` in `crates/elab/src/std`, `aoc/src`,
`games/`]. `aoc/` declares no families of its own, but uses `Fin` (2021
days 9, 15; 2025 days 3, 7) and `Vec` (2025 days 4, 7) [checked: grep].

A branch uses a determined field in one of three ways:

| Use | Example | Today | Under this proposal |
|---|---|---|---|
| Passed on as an implicit index argument | `Fin.toNat`'s `FSucc i => Succ (Fin.toNat i)` elaborates to `Fin.toNat [m] i`; `Vec.map`, `Vec.get`, `Vec.zipWith`, `Vec.toList` the same | field load | rebuilt: `n - 1` from the function's own `n`, a prim (free in steps) |
| Stored again in a constructor | `Vec.map`'s `VCons (f x) (Vec.map xs f)` is `VCons [n := m] …` | field load, then store | nothing: the new cell doesn't store it either |
| Computed with | `examples/accept/indexed-families.sw:53`, `length: Vec a n → Nat \| VCons [n := k] _ _ => Succ k`; std's `Vec.getReplicate`, `Vec.getTabulate` (proofs, erased) | field load | rebuilt, as in the first row |

No case was found where a determined field is used and can't be rebuilt:
§3 shows that can't happen for an accepted match [inferred]. The cost moves
from building (every cell computes and stores the field) to the matches
that use it (one rebuild each, usually a subtraction).

## 2. Which fields are determined

### 2.1 The rule

Field `f` of constructor `c` of family `D`, with result indices
`j₁ … jₘ` (`Ctor::result`, terms over the parameters and fields
[checked: `globals.rs:596-599`]), is **determined** when:

1. it isn't already erased (`field_erased`: a proof or a type former);
2. some `jₗ`, after stripping `Loc` and `Ann`, contains `Var(f)` at a
   **constructor path**: `jₗ` is `f` itself, or a constructor application
   (`Term::Ctor`, `Succ` included) one of whose arguments contains `f` at a
   constructor path. Nothing else counts: not under a definition's
   application (`n + 1`, which D145 already tells people not to write in an
   index), not as the head of an application (`f x`), not under a lambda
   or a `Pi`;
3. each step of that path goes through a field the backends store: a
   `Nat`'s `Succ`, or a field of another type that isn't itself erased or
   determined (so the step can be read at run time). In practice the paths
   are `n`, `Succ n` and `Succ (Succ n)`;
4. its type isn't a quotient, or a type containing one (§6.3, the one place
   rebuilding leans harder on the erasure contract);
5. the family is data (`Sort::Prop` types are erased whole).

**Non-linear indices** (`f` in two indices, or twice in one: `Same x x`)
are fine: the rebuild uses whichever occurrence the unifier solved first
(§3), and typing makes the others equal. **Computed indices** (`Fin (n +
1)`, `Vec a (List.length xs)` in a constructor's result) make the field not
determined; it stays stored, as today. **Parameters** aren't fields and
aren't stored anyway.

It is a function of the declaration only, like `Data::nat_shape` and
`Data::unboxed_field`: `Ctor::field_determined: Vec<bool>`, computed once
in core (outside the kernel's admission; not hashed: it's a function of
what is). The backends' layout then uses one predicate, `Ctor::stored(i) =
!field_erased[i] && !field_determined[i]`, and SW-2398's `nat_shape`
counts stored fields instead of non-erased ones.

### 2.2 What it gives

| Constructor | Fields today (run time) | Stored after |
|---|---|---|
| `FZero: Fin (Succ n)` | `n` | none |
| `FSucc (i: Fin n): Fin (Succ n)` | `n`, `i` | `i`: **Nat-shaped** |
| `VNil: Vec a 0` | none | none |
| `VCons (x: a) (xs: Vec a n): Vec a (Succ n)` | `n`, `x`, `xs` | `x`, `xs` |
| `MkCertified (n: Nat) (ok: IsPrime n): Certified n` (§6.8's example) | `n` | none (`n` is the whole index) |
| `Ty`'s `TList (t: Ty b): Ty (List b)` | `t` (`b` is a type, erased) | `t` |
| a constructor whose index is `n + 1` | `n`, … | `n`, … (not determined) |

This is the classic notion: Brady, McBride and McKinna's forced arguments,
Agda's "a constructor argument is forced if it appears as pattern variable
in an index of the target" [checked: Agda `Agda.TypeChecking.Forcing`
module docs] (§5).

## 3. Rebuilding a field at a match

### 3.1 Why the lowerer can't do it alone

`Term::Case(x, D, branches)` carries the scrutinee's variable and its data
type, but not its type's indices [checked: `term.rs:194-197`]; the
lowerer keeps slots, not types [checked: `lower.rs:278-289`, `Bind`]. The
scrutinee's index is somewhere in the definition's type, but finding it
isn't syntactic: after an earlier match the scrutinee's type may only be a
family because of that match (`T b` with `T True = Fin 3`), which is what
the kernel's case refinement works out (indexed-families.md §6.3).

### 3.2 Why a rebuild always exists

Take a possible branch of an accepted case on `x: D ps is`, constructor `c`
with result indices `js`, and a determined field `f` at a constructor path
in `jₗ`. The kernel unified `isₗ` with `jₗ` and finished without getting
stuck (stuck is `E-INDEX-STUCK`, refused; a conflict makes the branch
impossible, with no body to lower) [checked: indexed-families.md §6.3.2].
Walk the path down from `jₗ`. At each constructor on it, the left side
(evaluated in the refined context) was one of:

- **the same constructor**: Injectivity, and the walk goes down a level;
- **a flexible variable `y`**: Solution, `y := ` the right side's subterm.
  Then `f` is that subterm's field at the rest of the path, and `y`'s run-
  time value *is* that subterm. **Rebuild: read `y`, project down the rest
  of the path** (for `Succ`, subtract; for `Fin (Succ n)` and `n: Nat`,
  `n - 1`);
- **a number literal** (the Numbers rule): it was split into `Succ`s; the
  walk goes on, and ends in Solution with a literal (`f := 4`).

At `f` itself the left side `t` was solved into it (`f := t`, Solution,
rule 1 or 2 of §6.3.3), or `f` was already solved by an earlier
occurrence (Deletion). **Rebuild: evaluate `t`.** In every accepted case
the rebuild is "a term `t` of the refined context, then a projection path",
and it's always there [inferred from the rules as written; stage 1 checks
it, §6.2].

The term `t` or variable `y` refers to the refined context's variables.
At run time each of them is a slot: a parameter (kept at run time by
D141's second half), an earlier field (stored, or itself rebuilt the same
way), or the scrutinee. None is erased: `t` has a data type, so it uses
proofs and types only in erased positions [inferred]. This is why index
*parameters* must stay at run time: Agda learned the same, fixing its
erasure mode so that "only arguments with a `@0` annotation count as
forced", because "forced arguments need to be reconstructible from the
type" (agda/agda#6867, PR #6870) [checked: PR #6870]. An erased index
parameter (ghost fields, erase-proof-data.md, or a later usage analysis)
would make a field rebuilt from it ghost at that match (§7).

### 3.3 The options

| Option | How | Where it lands | Cost |
|---|---|---|---|
| **A. Replay the case's unification, outside the kernel** (recommended) | A core function, `erase::rebuilds(g, def)`, walks the definition's case tree from its type (as `erase::of_def` and `rt/src/erasure.rs` already evaluate a definition's telescope), calling the same `unify_index::unify` the kernel and the elaborator call (D149), and returns, per branch and determined field, `Rebuild { source: Term, path: [(DataId, ctor, field)] }`. Cached per definition in `EvalCaches` | core, consumed by rt and JS; kernel admission untouched | one unification per branch per definition, once; about what the kernel spent checking it |
| B. The kernel records each branch's solution in the `Branch` it returns, unhashed (as it does `Let`'s and `Quot`'s erasure flags) | `check.rs` writes it, the term carries it | kernel code (`check.rs`), the term format, the cache's serialised terms, and `Branch` constructions in 22 source files | no replay; but a kernel change for a runtime concern |
| C. The elaborator rewrites the uses (`m` becomes `Nat.pred n` in the body) | elaborated terms change | elaborator; changes hashes, goals, messages | terms grow, and proofs see the rewrite |
| D. Usage analysis (Idris 1): don't store what no reachable code reads | whole program, from `main` | every backend | the layout depends on the program: one `Vec.length` on a tail anywhere stores `n` for everyone; std's layout differs per program |
| E. Quantities (Idris 2, Agda `@0`): implicit constructor fields erased by default, reading one at run time an error | the language | elaborator, the guide, every program that reads one | user-visible; `length` above stops compiling; against D3424's "automatic" |

A is the recommendation: no kernel or language change, one place deciding
for every backend (as `nat_shape` and `unboxed_field` do), and the kernel's
own unifier gives the solution, so the replay can't disagree with what the
kernel accepted. B is the fallback if the replay proves awkward (it would
make the information exact by construction, at the price of touching
`check.rs`).

**Keying.** A rebuild has to be found again by the backend at the right
branch. The runtime's specialisation copies a definition's body with
cases on row parameters replaced by their `Empty` branch
[checked: `crates/rt/src/specialise.rs:1-25`], so a pointer into the
original term doesn't survive. Stage 1 keys rebuilds by the branch's
position in the case tree (the sequence of branch numbers from the root)
and has `specialise.rs` map positions as it removes row cases; if that is
fiddly, an unhashed `Branch` field filled in by `erase::rebuilds` (not by
the kernel) is the alternative. An implementation detail for the lane.

### 3.4 What the backends do with a rebuild

- **rt** (interpreter and native code): a new `Bind::Rebuilt(source,
  path)`, lowered only if the branch uses the slot (the existing
  `slot_used` check), as `source` lowered as an ordinary term, then each
  path step: `Nat`'s `Succ`, or a Nat-shaped type's successor, is a
  subtraction (the `Nat.sub` native, `prims.rs:483`, by k, the number of
  `Succ`s; exact, since the value is at least k); a field of an unboxed record is the value itself;
  another data field is a one-arm match. Native code compiles the same
  `Image`, so it needs nothing of its own.
- **JS**: the same, with `- kn` on a `bigint` and a property read for a
  field.
- **The reference evaluator**: nothing. It keeps storing the fields.

For `Fin.toNat`, rt's IR goes from

```
fn Std.Fin.toNat(v0, v1) =
  match v1: Fin { FZero => 0
                  FSucc(n: v2, i: v3) => %Nat.add(Std.Fin.toNat(v2, v3), 1) }
```

to (with SW-2398's Nat-shaped lowering on top)

```
fn Std.Fin.toNat(v0, v1) =
  match v1: Nat { Zero => 0
                  Succ(pred: v3) => %Nat.add(Std.Fin.toNat(%Nat.sub(v0, 1), v3), 1) }
```

**[inferred]**, and nat-shaped-types.md's stage 2 then replaces the whole
function with the identity native.

## 4. What changes for each use

| Where | Change |
|---|---|
| `Fin` (std, examples) | `FZero` stores nothing, `FSucc` its predecessor: Nat-shaped (§2.2) |
| `Vec`, `Grid` | `VCons` two fields; construction doesn't compute `n`; `Vec.map`, `get`, `zipWith`, `toList`, `foldLeft` and the rest pass `n - 1` down instead of loading it |
| `Vec.length (v: Vec a n) := n` | unchanged: reads its parameter, not a field |
| `examples/accept/indexed-families.sw`'s `length` (`VCons [n := k] _ _ => Succ k`) | `k` rebuilt as `n - 1` from the scrutinee's `n`; same answers |
| `examples/soundness/index-descent.sw` | kernel-side test; unchanged |
| `Fin.ofNatLt`, `Vec.fromListN`, `Vec.replicate`, `Vec.tabulate` (construction) | stop computing and storing the index field; `fromListN`'s `[n := k]` is no longer evaluated |
| proofs over `Fin`/`Vec` | unchanged (kernel) |
| JS | the same layout change behind the same predicate; nothing crosses the boundary |

**Must any stay stored?** A field that rule 2 doesn't catch stays (a
computed index). A field the rule does catch can always be rebuilt (§3.2),
so none must stay for correctness. The only cost risk is a rebuild whose
`t` is an expensive term: `MkCertified`'s `n` matched on a
`c: Certified (List.length xs)` rebuilds `n` as `List.length xs`, O(length),
where today it's a field load. Nothing in std or `aoc/` has that shape
[checked: §1.3's grep], and it costs only where the branch uses `n`.
Stage 1 adds a census of rebuilds whose source isn't a variable or a
literal, so such sites are visible.

**A cost this doesn't remove.** Callers still compute implicit index
*arguments*: `Fin.toNat [n := List.length xs] i` evaluates the length to
pass an `n` that `Fin.toNat` never needs. That's D141's second half, kept
here because rebuilds need it. A later analysis that erases index
parameters nothing reads (directly or through rebuilds) would remove it
(§7, finding 1).

## 5. Other implementations

| System | Indices in constructors at run time | How a field is recovered | Notes | Source |
|---|---|---|---|---|
| Brady, McBride, McKinna (TYPES 2003) | Forced arguments dropped, and constructor tags where indices determine the constructor; some families collapse entirely | From the indices of the scrutinee's type, via the case-tree's dot patterns | The origin of this note's idea; 80% less storage for a typed λ-calculus | "Inductive Families Need Not Store Their Indices", LNCS 3085, 115-129 [checked: Heriot-Watt portal abstract] |
| Agda | Forced constructor arguments "may be erased as they can be recovered from dot patterns" | The forcing translation moves the binding site in the unifier: `proj .(suc n) (zero n) = n` becomes `proj (suc n) zero = n` | Bugs: forcing ignored relevance (#2819), was sensitive to normalisation (#3898), several internal errors (#2888, #2919, #2947, #3063); with `--erasure`, only `@0` arguments may be forced (#6867, PR #6870). Its soundness issue #6654 was forced arguments used for *termination* with large indices, now `--forced-argument-recursion` | Hackage `Agda.TypeChecking.Forcing` (2.6.1.3); release notes 2.5.4, 2.6.1; PR #6870; indexed-families.md A2 [checked] |
| Idris 1 | Erased by whole-program usage analysis from `Main.main`: "everything that is found to be unused is erased", data constructor fields included | Not needed: an unused field is dropped | Layout depends on the program; warnings unhelpful by its own docs | Idris 0.9.19 manual, "Erasure By Usage Analysis" [checked]; Tejiščák's thesis [checked: abstract] |
| Idris 2 | `Fin`'s `k` in `FS : Fin k -> Fin (S k)` is an unbound implicit, so quantity 0: erased; reading it at run time is an error | The programmer binds `{k : _}` (quantity ω) to use it, and then it's stored | Quantities in the type system; tags are removed where constructors are disjoint (`getDetags`); `calcNaty` makes such Peano types numbers, but `Fin`'s `%builtin` is commented out | Idris 2 `libs/base/Data/Fin.idr`, `src/TTImp/ProcessData.idr`; Idris 2 manual "Updates required" (TDD) [checked] |
| Lean 4 | `Fin` is a structure, `{ val : Nat, isLt : val < n }`: no indexed family, and the proof is erased | n/a | Types and proofs have no run-time representation; other fields (an indexed family's implicit `Nat`) are relevant, so stored **[inferred from the relevance rule; not stated for indices]** | Lean reference, "Run-Time Representation", "Relevance" [checked] |
| Rocq extraction | Logical parts and types erased; everything else kept | Manual: `Extraction Implicit qualid [args]` declares arguments of a function *or constructor* "useless in extracted code"; an error if it can't be honoured | User-directed, per declaration | Rocq manual, "Program extraction" [checked] |
| Stitchwort today | Stored (D141) | n/a | Proofs and types erased (`field_erased`) | indexed-families.md §6.8 |
| **This proposal** | Determined fields not stored by the fast runtimes; the reference evaluator keeps them | Rebuilt at each match from the kernel's own unification solution (replayed) | Automatic, by the declaration; kernel unchanged | §2, §3 |

The closest is Agda's: the same definition of "forced", recovery from the
match's index, and the same lesson that the index must be available at run
time. The difference is where it lives: Agda's forcing is part of the
type checker and its unifier, and its bugs were there; here the kernel and
its unifier are reused, not changed, and the result feeds only the
untrusted runtime.

## 6. Steps, frames, agreement and soundness

### 6.1 Steps and frames

Steps on the fast runtime are frames entered; constructing, matching and
small number prims cost none [checked: nat-shaped-types.md §4].

- **Construction**: an elaborated index field (`[n := t]`) is no longer
  evaluated. Where `t` was a variable, nothing changes; where it called a
  definition, steps and frames fall by that call's.
- **Matches**: a rebuild is a variable or a literal plus a subtraction in
  almost every case: free. Where `t` is a call (§4's `Certified` shape),
  steps rise by that call's, and only where the field is used.
- **Frames**: unchanged by the layout; a rebuild doesn't add a frame unless
  `t` is a call.
- **The checker's budget** and **ticks** are unaffected (the kernel, and
  `Tick` operations).

Interpreter and native code run one `Image`, so they agree on steps by
construction. JS outputs are compared, as today.

### 6.2 Agreement

- The reference evaluator stores the fields; the fast runtimes rebuild
  them. Running the family examples (`examples/accept/indexed-families.sw`,
  `nat-shaped.sw`, std's `Fin` and `Vec` tests, 2025 day 4) on both and
  comparing outputs is a real check of the rebuilds, not a tautology.
- **A debug check** (stage 1): under the runtime's test builds, lowering
  stores determined fields as well and, at each rebuild, asserts it equals
  the stored value. Cheap, and it turns any wrong rebuild into a loud
  failure on the existing tests.
- `validate.rs` keeps checking arm field counts against the stored layout.

### 6.3 Soundness

**The kernel is untouched**: it keeps the fields in its values, compares
them in conversion, and counts them as structural subterms for termination
(D143). `field_determined` and `rebuilds` are computed outside admission,
aren't hashed and don't feed anything the kernel reads. The reference
evaluator (`--reference`, `test`) is unchanged. The fast runtimes are
already untrusted: "its output can be wrong, but a proof never depends on
it" [checked: docs/core.md:242]. So nothing here can make a false theorem
check, and `docs/core.md` needs no change. Agda's soundness issue with
forcing (#6654) came from using forced arguments in termination checking;
Stitchwort's termination checker reads kernel terms, where the field is
still a field, and never derives a decrease from an index (D143).

What can go wrong is a wrong answer at run time, if a rebuild doesn't equal
the field. The argument that it does: the value has its type, so the
scrutinee's index equals the constructor's index with the field in it; the
kernel's unification solved the field from that equation (§3.2); and the
run-time values of the index's variables are the kernel's values with
proofs and types erased. That last step is the erasure contract (D863):
`J` on an erased proof returns its base, which is right because any proof
of `x = y` means `x` and `y` are the same value. A value transported from
`Fin n` to `Fin n'` keeps its cell, and its rebuild reads `n'`; the contract
says `n'` is `n`. For a quotient, "the same value" means the same class, not
the same representative, so a field rebuilt from a quotient index could be
a different representative from the one stored. Rule 4 keeps quotient-typed
fields stored, rather than argue that every observation goes through a
lift.

## 7. Interactions

- **Ghost fields** (erase-proof-data.md, proposed): if index parameters or
  fields can be ghost, a rebuild whose source mentions one is itself ghost
  at that match, and a run-time use is refused as any ghost use is.
- **Prop elimination's deferred clause** (DESIGN.md §6, D140: a proof's
  field that "appears among the indices" may be read into data): the same
  shape of test, over a proposition. If it's adopted later, it can share
  §2.1's function; not proposed here.
- **Tags** (Brady et al., Idris 2's detagging): when indices determine the
  constructor too (`Vec`'s `VNil` at `0`), the tag could go. Not needed for
  any layout here; not proposed.
- **The TRMC gap** (SW-2405, running now): a Nat-shaped value built around
  a recursive call (`More (f x)`, `FSucc (Fin.ofNatLt n i h)`) lowers to
  `%Nat.add(f x, 1)` and loses its tail-recursion-modulo-constructor loop,
  so frames grow with the number (SW-2398's example, steps 530 to 526).
  Separate from this note, but it applies to `Fin.ofNatLt` as soon as `Fin`
  is Nat-shaped, until nat-shaped stage 2's native replaces it.

## 8. Stages and estimate

| Stage | Work | Model | Estimate |
|---|---|---|---|
| 1 | Core: `Ctor::field_determined` (§2.1) and `Ctor::stored`; `erase::rebuilds` replaying `unify_index::unify` over a definition's case tree, cached; keying through `specialise.rs`. rt: the 7 layout sites on `stored`; `Bind::Rebuilt` lowering; the debug check (§6.2); a census of non-trivial rebuilds. Tests: lowering snapshots (`Fin`, `Vec`, `length`), the family examples on interpreter and native against the reference; std's `Fin`/`Vec` tests; 2025 day 4 measured | Opus (runtime representation for every backend, fed by the kernel's unifier) | 2.5-3.5 h |
| 2 | JS: the 16 layout sites on `stored`, rebuild lowering, `run --js` on the family examples | Sonnet | 1.5-2 h |
| then | SW-2398 finishes (below) | Opus | ~1 h left of its 1.5-2 h |
| then | nat-shaped-types.md stage 2 (identity natives for `Fin.toNat`, `Fin.ofNatLt`) and stage 3 (JS) | Sonnet | 1 h + 1-1.5 h |

This note's own stages: **about 4-5.5 lane-hours** [estimated]. Docs, in
stage 1: DESIGN.md:465 (indices are no longer stored by the fast
runtimes), indexed-families.md's "As built", and the runtime representation
where `Nat`'s is described. Not a language feature: no guide, syntax or
tour change; `docs/core.md` unchanged (§6.3).

**What it unlocks**: `Fin` as a machine number on every backend
(nat-shaped-types.md's 1.5-3x on 2025 day 3's search, and O(1)
`toNat`/`ofNatLt`) **[estimated there]**; `Fin`-indexed arrays become
reasonable to write (one bounds check per read instead of a walk), which
D3419's `Nat`-indexed distances index avoided; `Vec` cells a third smaller
and cheaper to build.

**What SW-2398's WIP branch (`bf4936b9e`) needs to merge** [checked: its
diff]:

1. Rebase onto stage 1; `nat_shape` counts `Ctor::stored` fields instead of
   non-`field_erased` ones (one closure), and its doc comment drops "`Fin`
   isn't".
2. `examples/accept/nat-shaped.sw`'s header comment ("`Fin` … isn't one of
   them yet") and the snapshot (`FSucc(4, FSucc(3, FZero(2)))` becomes the
   literal 2) updated; `Fin` cases added to the native agreement test.
3. The native test's step pin (530, now 526): settled after SW-2405 lands,
   which changes frames and steps for these shapes again. So SW-2398 merges
   after both this note's stage 1 and SW-2405.

## 9. Open questions

- **Q1. Go ahead with erasing determined fields on the fast runtimes**,
  overturning D141's stored fields there (implicit index parameters stay;
  the reference evaluator and kernel unchanged)? **[rec: yes]**: it is what
  D3423/D3424 need for `Fin`, every other system that has indexed families
  and cares about speed does some form of it, and the reference evaluator
  keeps checking the rebuilt values.
- **Q2. How the rebuild is found**: (A) replay the kernel's unification
  outside the kernel; (B) the kernel records it in the term; (C) the
  elaborator rewrites uses. **[rec: A]**: no kernel or term-format change,
  and it uses the kernel's own unifier, so it agrees with what was
  accepted.
- **Q3. Automatic, or opt-in?** (a) automatic, by the declaration, as
  D3424 decided for Nat-shaped types; (b) a declaration marks the fields
  (Rocq's `Extraction Implicit`); (c) quantities, with an error for a
  run-time read (Idris 2). **[rec: (a)]**: invisible to programs, nothing
  to learn, and `length`-style reads keep working.
- **Q4. The reference evaluator**: keep storing the fields there (a), or
  rebuild there too (b)? **[rec: (a)]**: it stays the plain reading of the
  kernel's terms, and so a check on the rebuilds.
- **Q5. The debug check** (store and compare in test builds) in stage 1:
  **[rec: yes]**; it costs a test-build-only branch in lowering.

## 10. Findings beside this note

1. **Index arguments nothing reads are still computed.** Callers evaluate
   implicit index arguments even for functions that only pass them on
   (`Fin.toNat`, `Vec.map`), and after this note, rebuilds are their only
   other reader. An inert-style analysis (like D2349's for proofs) that
   erases index parameters no runtime code reads, directly or through a
   rebuild, would remove `Fin.toNat [n := List.length xs] i`'s length. A
   design item, after stage 1.
2. **nat-shaped-types.md §1.1 and §2.3** said `Fin`'s implicit `n` is an
   erased field; it isn't (D141). Corrected there with a pointer here.

## Sources

- Brady, McBride, McKinna, "Inductive Families Need Not Store Their
  Indices", TYPES 2003, LNCS 3085 (2004), 115-129:
  <https://researchportal.hw.ac.uk/en/publications/inductive-families-need-not-store-their-indices/>.
- Agda, `Agda.TypeChecking.Forcing` module documentation (2.6.1.3):
  <https://hackage-content-origin.haskell.org/package/Agda-2.6.1.3/docs/Agda-TypeChecking-Forcing.html>.
- Agda release notes 2.5.4 and 2.6.1:
  <https://hackage.haskell.org/package/Agda-2.7.0.1/docs/doc/release-notes/2.5.4.md>,
  <https://hackage.haskell.org/package/Agda-2.7.0.1/docs/doc/release-notes/2.6.1.md>.
- Agda PR #6870 (issue #6867), forced arguments under `--erasure`:
  <https://github.com/agda/agda/pull/6870>.
- Agda 2.6.4 changelog (`--forced-argument-recursion`, issue #6654), via
  indexed-families.md source A2:
  <https://hackage.haskell.org/package/Agda-2.6.4/changelog>.
- Idris 0.9.19 manual, "Erasure By Usage Analysis":
  <https://idris.readthedocs.io/en/v0.9.19/reference/erasure.html>.
- Tejiščák, "Erasure in dependently typed programming" (PhD thesis, St
  Andrews): <https://research-repository.st-andrews.ac.uk/handle/10023/28867>.
- Idris 2 sources, `main`, read 8 November 2026: `libs/base/Data/Fin.idr`,
  `src/TTImp/ProcessData.idr`: <https://github.com/idris-lang/Idris2>;
  Idris 2 manual, "Type Driven Development with Idris: Updates Required":
  <https://idris2.readthedocs.io/en/stable/typedd/typedd.html>.
- Lean reference, "Inductive Types", Run-Time Representation:
  <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>.
- Rocq manual, "Program extraction" (`Extraction Implicit`):
  <https://rocq-prover.org/doc/master/refman/addendum/extraction.html>.
