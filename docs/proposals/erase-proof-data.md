# Proposal: erasing data that only proofs use (SW-2028)

Status: design note, waiting for Matt's decisions (D2900 to D2905). Written 7 Nov
2026, from the compute-once note's 2021 day 9 row (`docs/proposals/compute-once.md:42`,
`:435`) and the day's notes (`aoc/NOTES-2021.md:2004`, `:2141`).

## 0. Summary

**What users get.** A field or a parameter can be marked `ghost`: the kernel sees it
like any other value, proofs and `rfl` use it as they do now, and the program never
computes or stores it. In 2021 day 9 that turns an innocent helper that took 3.0 s
back into one that takes 0.8 s, with no "build it once" workaround. It also takes a
trap out of std: today every `Graph` builds its `states` list at run time, though
the only code that reads it is proofs and the searches' termination measures.

**The problem, plainly.** Stitchwort already throws away proofs and types when a
program runs. It decides what to throw away by looking at the type: a value whose type
is a proposition or a type is erased. `states: List s` is a list, so it's kept, even
though nothing that runs ever looks at it. You only find out from the timing.

**The recommendation.** Design C (§4.3): a `ghost` mark on record and constructor
fields, on definition parameters and on definitions. A kernel check ("ghost values are
used only where nothing runs") makes erasing them safe. The mark reuses the masks the
runtimes already follow for proofs, so lowering, the machine, native code and JS need
almost no change. Ruled out: inferring it from usage as the optimisation (B, §4.2),
which is invisible and fragile, though it's kept as a profiler hint. Also ruled out:
Lean's `Erased` encoding (D, §4.4), because the kernel can't compute with what's
inside.

## 1. The problem

std's graph type (`crates/elab/src/std/Graph/Search.sw:25-29`):

```stitchwort
type Graph (s: Type) = {
  edges: s → List (s, Nat),
  states: List s,
  listed: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ edges state → next ∈ states
}
```

`states` is there so the searches terminate. Each step settles one more of the listed
states, or shrinks the queue. Here's everything that reads it:

- the measures, `decreasing (Graph.unsettledIn (graph.universe sources) settled,
  queue.size)` (`Search.sw:276`) and `decreasing Graph.unsettledIn graph.states settled`
  (`:600`);
- `Graph.universe` (`:241`), used only in the measure above and in the types of proof
  arguments (`queued`, `:274`);
- proofs: `listed`, `Graph.visitFewer` (`:577`), `Graph.pushedQueued` (`:260`).

A `decreasing` definition runs its run body, `f.%step x (y c => f y c) c`, without the
fuel, so the measure isn't in what runs (`crates/elab/src/decreasing.rs:5-29`). The
proof arguments are erased by type. So **no code that runs reads `states`**. I checked
every `def` in `Search.sw` and every `.states` in `aoc/src`: none outside proofs.

But building a `Graph` computes it. The shared grid code builds it from every cell
(`aoc/src/Aoc/Common/GridGraph.sw:67-71`, `cellsGraph`: `(cells rows).map Pair.fst`),
and passes it through `stepGraph`'s parameter (`:15-20`). Day 9 first built the graph
once per low point. That made 240 lists of 10,000 positions, 2.3 s of a 3.0 s run
(`aoc/NOTES-2021.md:2004-2007`). The fix was to build it once (`Day09.sw:64-75`, with a
comment explaining why), and `cellsGraph`'s doc now says "build it once". Every future
grid day pays for this lesson again, or reads the comment.

This isn't the compute-once problem. Sharing the list would still compute it once per
run. Here the right number of times is zero.

## 2. What Stitchwort does today

All of this is read from the code.

- **Erasure is decided by type.** A parameter is erased if its type is a proposition or
  a type former (`crates/core/src/check.rs:3941-3955`, `telescope` and `is_erased`), and
  likewise a constructor's field (`check.rs:2722`: `field_erased` is `sort == Prop ||
  is_type_former`). So is a definition's result (`result_erased`, `check.rs:3947`),
  which is how a theorem isn't run.
- **Every runtime follows these masks.** The checker's evaluator, while running
  (`crates/core/src/erase.rs:1-13`, rules 1 to 3), and the shared erasure decisions for
  lowering and JS (`crates/rt/src/erasure.rs:14-68`, `DefShape`). Lowering a constructor
  skips the erased fields' arguments without evaluating them (`crates/rt/src/lower.rs:
  1071-1081`). A record with one runtime field is stored as that field
  (`crates/core/src/globals.rs:553-565`, `unboxed_field`, counting `field_erased`). JS
  omits erased fields (`crates/core/src/js_repr.rs:216`).
- **Why it's safe today** (`erase.rs:36-50`): a proof or a type never decides which way
  a computation of data goes. Types are never matched, and matching a proof into data
  is allowed only for subsingletons (`E-PROP-ELIM`, `check.rs:989-995`, which reads
  `field_sorts`, not `field_erased`). That argument depends on the *type*. For a
  `List`, nothing like it holds. So a new mark needs a new check.
- **Erased isn't irrelevant.** Conversion skips proof fields by `field_sorts == Prop`
  (proof irrelevance, `docs/proposals/proof-irrelevance.md` §5.5: "never use
  `field_erased` where `field_sorts == Prop` is meant"). Types are erased but compared.
  Ghost data must be the same: erased, but compared.
- **The kernel doesn't vouch for the runtimes** (`check.rs:1992-1997`: run bodies are
  "untrusted ... a proof never depends on what they compute"). That's about proofs. Here
  we need the runtimes to be right, and they rely on the kernel's masks.
- **Some runs can switch erasure off.** `test` and the counterexample search evaluate
  in the checker's machine with `erasure.running()` (`crates/driver/src/test_run.rs:231`,
  `crates/elab/src/counterexample/mod.rs:797`). `Erasure::set_disabled`
  (`erase.rs:150`) exists, today only for differential tests.

## 3. Requirements

1. **The kernel still sees the value.** `rfl`, unfolding and the measures compute with
   `graph.states` as they do now.
2. **Erasure never changes what a program computes.** Nothing that runs may need a ghost
   value, and that includes checking something about it at run time: a `Decidable`
   instance, a validator at the JS boundary, a derived `==`.
3. **It works with record eta** (just merged, `docs/proposals/record-eta.md` §6) **and
   with computed fields** (`docs/proposals/compute-once.md` §3.2).
4. Limits fail, never choose (D2543). Nothing here involves a limit. Erasure only
   removes work.

## 4. The designs

### 4.1 A. Restructure the program, as a documented pattern

**Build once.** What day 9 does now. It works, but a guide note doesn't stop the next
person, and the cost is still paid once per run (inferred: a few ms for day 9, more for
2021 day 15's 250,000-position `boxGraph`, `GridGraph.sw:44-48`).

**A thunk.** This works today with no language change: `states: () → List s`. Building a
graph makes a closure and never calls it. Proofs write `graph.states ()`, and the
kernel beta-reduces it, so requirement 1 holds. `stepGraph`'s parameter becomes a
thunk too. Costs:

- std's API gets noisier (`graph.states ()` in about 30 places in `Search.sw` and
  the grid proofs).
- It's a convention. Nothing stops runtime code calling it, and nothing says the
  closure keeps `rows` alive (it usually is anyway).
- It doesn't help a plain parameter that only proofs use.

**Restructure the termination argument.** This can't be done. The measures are `Nat`s
computed from the list, and the only alternative, a proof that some list exists (`∃
states, …` in `Prop`), can't be taken apart into data (`E-PROP-ELIM`, `check.rs:989`).
The same goes for `Acc` (`docs/core.md`, D140).

So A is a workaround, not a language answer. The thunk is the fallback if C is
declined.

### 4.2 B. Infer it, with no annotation (usage analysis)

**Change.** When a program is lowered, find every constructor field that no reachable
runtime code reads (a projection, a `case` binding that's used, the accessor called).
Then drop it from the layout and skip its argument at every construction. Also find
definition parameters that are used only in erased positions or passed to dropped
fields, and skip those arguments too (absence analysis). Day 9 needs both: the field is
`Graph.states`, and the parameter is `stepGraph`'s `states`, which `cellsGraph` computes
before the call.

It fits the architecture. Lowering is already whole-program, from
`erasure::reachable` (`crates/rt/src/erasure.rs:73-100`). Since everything pure is total
(`crates/rt/src/opt.rs:29-31`), dropping dead pure work can't change what's printed.
MLton does this ("useless" field elimination, whole-program; from memory). GHC's demand
analysis does the parameter half within a module.

**Why not:**

- **Invisible, and so fragile.** One `IO.print "${graph.states.length}"` while
  debugging, anywhere in the program, brings the whole 3 s back, with no error and no
  warning. The promise isn't written anywhere a reader can see.
- **It's per program, not per type.** Whether `Graph` stores `states` would depend on
  which program it's in. Exports, the image cache and the reference evaluator would
  all have to agree on the analysis.
- **Higher-order code defeats it.** `Graph.states` passed as a function value, or a
  field read through a polymorphic helper, has to be treated as live. Whether a field
  is dropped then depends on how the program happens to be written.
- **It doesn't cover the checker's machine.** `test` and the counterexample search
  evaluate terms there, not lowered code (§2).

The analysis is worth having as a **hint**, though. Under `run --profile`, print "field
`Graph.states`: built 240 times, never read at run time; mark it `ghost`". That's a
read of what happened, so it can't be wrong, and it goes with compute-once's profiler
line (stage 0b there).

### 4.3 C. Mark it `ghost` (Dafny's `ghost`, F*'s erased, Agda's and Idris's quantity 0)

**Change.** Three places can carry the mark:

```stitchwort
type Graph (s: Type) = {
  edges: s → List (s, Nat),
  ghost states: List s,                       -- a field
  listed: …
}

def stepGraph (enter: Position → Option Nat) (ghost states: List Position)   -- a parameter
    (complete: …): Graph Position := …

ghost def Graph.universe (graph: Graph s) (sources: List (s, Nat)): List s :=  -- a definition
  sources.map Pair.fst ++ graph.states
```

- **The kernel's view doesn't change.** A ghost field is a field and a ghost parameter
  is a parameter. Conversion compares ghost values like any data (§5.1). Requirement 1
  holds by construction.
- **The masks.** A ghost field sets `field_erased`, but never `field_sorts`. A ghost
  parameter sets its entry in the definition's erased parameters (`DefShape::params`,
  `erase.rs`'s `DefErasure::params`). A ghost definition sets `result_erased`, as a
  theorem does. The generated accessor of a ghost field (`Graph.states`) is a ghost
  definition. Every runtime then skips them the way it skips proofs today: arguments not
  evaluated, fields not stored, calls not made.
- **The check that makes it safe (E-GHOST).** Over the term that runs (the run body if
  there is one, else the body; not for theorems, ghost definitions or types), the kernel
  walks with one flag: are we in a runtime position or an erased one? A ghost variable
  (a parameter, or a pattern variable bound from a ghost field), a ghost definition, or a
  `Proj` of a ghost field in a runtime position is `E-GHOST`. These positions are erased:
  types and annotations; arguments at erased parameters (proofs, types, ghost
  parameters); erased fields of a constructor; `J`'s motive and proof; and the measure
  of a `decreasing` definition, which isn't in the run body at all. A `case` whose
  scrutinee is ghost is itself in a runtime position, so it's refused there. A `case` on
  a record that has a ghost field is fine, and the variable it binds is ghost.
- **Why it can't change results.** After the check, no runtime position mentions a
  ghost value. Its placeholder can only be passed to erased positions, which by today's
  argument (`erase.rs:36-50`) are never inspected. Requirement 2 follows. The check
  covers runtime checks *about* a ghost value too, because they're runtime code: `if h:
  graph.states.length = 3` builds a `Decidable` from the ghost list in a runtime
  position, so it's `E-GHOST`. A field validator (`FieldValidator`,
  `globals.rs:582`) is checked the same way. So is the JS boundary: an export whose
  type has a ghost field is `E-EXPORT`, since it could be neither decoded nor validated.
  I've decided that myself.
- **Derived instances.** A derived `==`, `Ord` or `Finite` would read a ghost field at
  run time. Skipping it would break `DecEq.sound` (two graphs that differ only in
  `states` would compare equal). So a type with a ghost field gets none of them
  (`E-INSTANCE-NONE`, "the field `states` is ghost"). The derived `Show` leaves the
  field out, as it does proof fields. I've decided this too; it's forced.
- **Tests and the counterexample search.** Both run in the checker's machine, which
  can run without erasure (§2). A test or a generated checker that fails the ghost check
  runs with erasure off, so `test "states listed" := graph.states.length == 10000`
  works, at the speed of a run that computes its proofs. `stitchwort run` has no such
  fallback, so `main` must pass the check. I've decided this myself: the user-visible
  rule is just that you can test ghost data.
- **Where the check lives: the kernel.** The masks it protects are kernel metadata,
  and every runtime trusts them. A bug in an elaborator-only check would show up as a
  program printing the wrong answer, with nothing to catch it. `E-PROP-ELIM`, which
  protects the proof masks, is in the kernel for the same reason. The cost is one linear
  walk per definition, and `set_run_body` (`check.rs:1998`) runs it on the run body.
  This is D2902. The elaborator runs the same check earlier to give a good message
  ("`states` is ghost; it's read here at run time; make `basinCount` ghost, or pass
  something that isn't").
- **Where ghost can't go (stage 1).** It can't go on lambda parameters or function
  types. The mark is on a definition's binders, not in its `Pi` type, so a function
  used first-class (`List.map stepGraph'`) takes the argument and ignores it, and the
  caller still computes it. That's correct, just not saved. Putting quantities in `Pi`
  (Agda's `(@0 x: A) → B`, Idris 2's `(0 x: A) → B`) is a change to the type theory,
  with arrow subtyping or conversions between the two arrows. Nothing needs it yet
  (D2903). A `let` whose value is ghost, in runtime code, is `E-GHOST` in stage 1, with
  a hint to inline it into the proof or make a ghost definition. I decided this myself;
  `ghost let` can come later.
- **Hashes.** Ghost marks are part of the declaration and hashed: they change what the
  kernel accepts and the runtime layout. That's an implementation decision, so I've made
  it. Migration cost doesn't count.

**Other systems.**

- **Dafny**: `ghost` variables, fields, parameters and functions, with a resolver
  check that ghost values appear only in "specification contexts". The verifier sees
  everything, and compiled code sees none of it (from memory).
- **F\***: `FStar.Ghost.erased a`, with `hide` and `reveal`. `reveal` is in the ghost
  effect `GTot`, so only ghost code can use it (from memory).
- **Agda**: `@0` (`@erased`) on arguments and record fields. Erased variables may be
  used only in erased positions, and they're still compared (erasure without
  irrelevance, unlike `.x`). Matching on an erased argument is restricted (from memory).
- **Idris 2**: quantity `0` on any binder, checked by its core's quantity checker,
  where types are erased contexts automatically
  (`docs/proposals/proof-irrelevance.md` §4.4).

C is the same idea as these, cut down to what Stitchwort needs: two quantities (ghost
and normal, no linear `1`), on definitions' binders rather than in function types, and
checked once over the term that runs.

### 4.4 D. Lean's way: `Subtype` and `Erased`

Lean's compiler erases only types and proofs, as Stitchwort does. `Subtype {x // p x}`
keeps `x` and erases the proof, so it doesn't help here. Mathlib's `Erased α` erases
data by encoding it as a predicate: a `PSigma` of `s: α → Prop` (a type former, so
erased) and a proof `∃ a, (a = ·) = s`. Getting the value out is `Erased.out`, a
`noncomputable` definition by `Classical.choose`. Lean's guard is that runtime code
can't call `noncomputable` definitions (`Mathlib/Data/Erased.lean`, from memory, not
re-checked).

In Stitchwort this fails requirement 1. `out` would be an axiom (there's no choice),
so `graph.states.out` never reduces. Then `unsettledIn` in the measure is stuck, and
`rfl` can't see the list. Without choice, the value can't be got out at all:
`E-PROP-ELIM` refuses `Exists` into data. **Ruled out.**

## 5. Interactions

### 5.1 Record eta

- **Eta types** (`record-eta.md` §6.1): condition 4, "at least one field is not a
  proof", reads `field_sorts`. A ghost field is not a proof, so it counts. `Graph` keeps
  eta. A record whose only non-proof fields are ghost (`{ ghost n: Nat, small: n < 5 }`)
  has eta in the kernel and no runtime fields. It's stored as a field-less constructor,
  and `unboxed_field` (`globals.rs:553`) returns `None`.
- **Rule 1** (`§6.3`, constructor against neutral) compares every field that isn't a
  proof, so ghost fields are compared. That has to be so: if two graphs that differ in
  `states` were convertible, `Graph.states` wouldn't be a function, and the kernel
  would prove `False`. This is Agda's #2170 trap (irrelevant *data* fields,
  `proof-irrelevance.md` §5.5). Ghost is erasure only, never irrelevance.
- **Rule 2** (a `case` on a neutral takes its branch) is kernel-only, "not while a
  program runs" (§6.4). It binds `Proj(D, i, x)` for a ghost field, and the ghost check
  treats that `Proj` as ghost, the same as the pattern variable.
- **Field access** stays a call of the accessor (§6.4, SW-1766). For a ghost field the
  accessor is a ghost definition, so `graph.states` in runtime code is `E-GHOST` at the
  call, with the message above.
- **Unboxing changes.** `Graph` goes from two runtime fields to one (`edges`), so it's
  stored as the function itself (D866). Layout only.

### 5.2 Computed fields (compute-once.md §3.2)

The two features answer opposite questions. A computed field is "compute this once,
because runtime code reads it often". A ghost field is "never compute this, because
runtime code never reads it". The guide's records section shows both, side by side,
with day 19 and day 9 as the examples. Rules:

- **A computed field can't read a ghost field** (`E-GHOST` in its definition, since
  it runs at construction). The note suggests a ghost method instead. `ghost computed`
  is refused: it would mean an ordinary ghost definition, so write that.
- **Ghost fields aren't captures.** An update that changes only ghost fields keeps every
  computed slot (`FieldDefault::captures`, compute-once §3.2), which follows from the
  rule above.
- **Unboxing counts both:** runtime fields are the non-erased fields plus the computed
  slots.
- **The eager-cost warning** in compute-once ("computed when the record is built; that's
  the trap of 2021 day 9's `states`", `compute-once.md:170`) gets its answer: if only
  proofs read it, make it `ghost`.

### 5.3 Proof irrelevance and `E-PROP-ELIM`

Neither changes. Both read `field_sorts` (`value.rs`'s proof masks, `check.rs:989-993`).
Ghost sets only `field_erased`. A `Prop` type with a ghost data field
(`type Hidden: Prop = | Hide (ghost x: Nat)`) is still refused large elimination,
because `x`'s sort is `Type`. One audit item: after this, `field_erased` and "is a proof"
differ for more fields, so stage 1 greps every reader of `field_erased` for one that
means "proof".

## 6. Recommendation, and day 9 under it

**Recommended: C, a `ghost` mark on fields, definition parameters and definitions,
checked by the kernel over the term that runs. Plus B's analysis as a `run --profile`
hint only.**

Why C over B: the promise is written where the reader looks, in the type and the
signature. Breaking it is an error at the line that broke it, not a silent 4× slowdown.
It's local and per definition, it covers the checker's machine as well as the lowered
runtimes, and it reuses the masks every backend already follows. Why C over A: A
leaves the trap in std, for every grid day. Why not D: the kernel couldn't compute with
the value.

What it costs: a keyword, a kernel walk per definition, a new error, and std's `Graph`
and the grid code marked. What it rules out for now: ghost lambda parameters and ghost
arrows in function types, ghost `let`s, and derived `==`, `<` and `Finite` on types
with ghost fields.

Day 9 under it. std:

```stitchwort
--| A graph for a shortest-path search: each state's edges, with their costs,
--| and a list of states that every edge leads to. The list is ghost: proofs and
--| the searches' termination use it, and a program never builds it.
type Graph (s: Type) = {
  edges: s → List (s, Nat),
  ghost states: List s,
  listed: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ edges state → next ∈ states
}

ghost def Graph.universe (graph: Graph s) (sources: List (s, Nat)): List s := sources.map Pair.fst ++ graph.states
```

`Graph.fromEdges` doesn't change: its `states` parameter is read at run time (the
`known` set) and stored in the ghost field, which is allowed. The measures, `queued` and
the theorems don't change.

The grid code: `stepGraph (enter) (ghost states: List Position) (complete: …)`.
`cellsGraph` and `boxGraph` don't change. Their `(cells rows).map Pair.fst` and
`positions height width` are now arguments to a ghost parameter, so they aren't
computed. The "build it once" sentence in `cellsGraph`'s doc goes.

The day (`aoc/src/Aoc/Year2021/Day09/Day09.sw:58-75`) becomes the version that was
written first:

```stitchwort
def HeightMap.graph (map: HeightMap): Graph Position := map.grid.graph enterOpen

--| The number of locations in the basin of `low`: those the flood fill from
--| it reaches. A 9 is in no basin (and a low point is a 9 only on a map of one
--| location).
def HeightMap.basinSize (map: HeightMap) (low: Position): Nat :=
  if map.isOpen low then (map.graph.breadthFirst [low]).size else 0

def solvePart2 (map: HeightMap): Nat := map.lowPoints.map (((low, _)) => map.basinSize low) |> largestThreeProduct
```

`basinSizes`, its comment and `basinSize`'s `graph` parameter go. Building the graph is
now a closure over `rows`, 240 times. `Proofs/Part2.sw:19` and `:24` drop the
`map.graph` argument, and nothing else in the proofs changes, since every lemma is
about `map.graph` (inferred; the lane checks it). Expected: about the 0.8 s run of the
build-once version, measured by the lane.

## 7. Questions for Matt

- **D2900: Is an explicit `ghost` mark (on fields, definition parameters and
  definitions) the language's answer to "data only proofs use", erased at run time and
  seen in full by the kernel?** [rec: yes. It fixes day 9 and the std `Graph` trap. It
  makes the promise visible, it's checked, and it follows Dafny, F\*, Agda and Idris.]
- **D2901: Syntax: the keyword `ghost` (`ghost states: List s`, `(ghost states: …)`,
  `ghost def`), rather than an attribute (`@[erased]`) or a quantity (`0 states`)?**
  [rec: `ghost`. It reads as what it's for, sits like compute-once's `computed`, and
  "erased" already means "proofs and types, by type" in our docs.]
- **D2902: The ghost check in the kernel, at admission and in `set_run_body`, rather
  than only in the elaborator?** [rec: kernel. It protects the masks every runtime
  trusts, as `E-PROP-ELIM` does, and costs one walk per definition.]
- **D2903: Stage 1 has no ghost lambda parameters and no ghost arrows in function
  types: the mark is on a definition's binders only?** [rec: yes. Quantities in `Pi`
  change the type theory, and nothing needs them yet. A first-class use is still
  correct, just not saved.]
- **D2904: Rule out inferring erasure from whole-program usage as an optimisation (B),
  keeping it only as a `run --profile` hint, and rule out Lean's choice-based
  `Erased` (D)?** [rec: yes. B is silent and fragile: one debug read brings the cost
  back. D hides the value from the kernel.]
- **D2905: If D2900 is no, make std's `Graph.states` a thunk (`() → List s`) as the
  documented pattern?** [rec: only then. It works today, but it's a convention, and
  it's noisier in thirty proof sites.]

Decided by me, as implementation details: the derived-instance rules and the export
rule (§4.3), tests with ghost reads running unerased, ghost marks hashed, no ghost
`let` in stage 1, and the elaborator pre-check for messages.

## 8. Tickets to file

In order. Stage 1 waits for D2900 to D2902.

1. **Stage 1a: ghost marks in the kernel** (Opus: kernel, soundness). Add the marks to
   `Ctor` fields, definition parameters and definitions, and hash them. Fold them into
   `field_erased`, `telescope`'s erased parameters and `result_erased`, never into
   `field_sorts`. Add the ghost check (E-GHOST) over the body or run body, with the
   positions in §4.3. Audit every reader of `field_erased` for one that means "proof"
   (§5.3). Opus, 90 min. Tests: new kernel unit tests in `crates/core/tests/it/` (a
   ghost read in a runtime position, under a `case`, through a `Proj`, inside a
   `Decidable` in an `if h:`, in a run body that the kernel body doesn't have, a
   `Prop` with a ghost data field still `E-PROP-ELIM`, eta comparing ghost fields),
   by `task test:one`.
2. **Stage 1b: syntax and elaboration** (Opus: core language). Parse `ghost` on
   fields, parameters and `def`. Make the accessor of a ghost field a ghost definition.
   Run the elaborator's pre-check, with the message naming the read and the fix.
   Refuse derived `==`, `Ord` and `Finite`, and leave the field out of `Show`. The
   export gets `E-EXPORT`. Update `docs/syntax.md`, the guide's records chapter (next
   to computed fields, if they've landed) and `stitchwort fmt`. Opus, 90 min. Tests:
   `examples/accept/ghost-*.sw` and `examples/reject/ghost-*.sw` via `task test:one --
   examples`, the guide example check, fmt round-trip, `snap:hashes` and
   `hash_stability` for the new examples.
3. **Stage 1c: runtimes.** Check that machine, native and JS lowering skip ghost
   arguments and fields through the existing masks. Run a test or counterexample
   checker that fails the ghost check with erasure off. Sonnet, 45 min (most of it
   is checking: the masks already drive lowering, `lower.rs:1071-1081`). Tests:
   `examples/extract/ghost-field.sw` with `-- run:` cases on the machine, `--native` and
   `--js` against `--reference`, and one `test` that reads a ghost field.
4. **Stage 2: std `Graph` and the grid code.** Mark `ghost states`, `ghost def
   Graph.universe` and `stepGraph`'s parameter. Drop "build it once" from
   `cellsGraph`'s doc. Then revert 2021 day 9 to the per-low-point form (§6) and time
   it. Sonnet, 60 min. Tests: the extract `bound_to_the_prelude` tests (std core
   edited), `task test:one -- year2021_day09`, `audit:touched -- Aoc.Year2021.Day09`,
   and the `Aoc.Common` grid tests. The other `Graph` days (2024 days 16, 18 and 20,
   2021 day 15, 2020 day 7) should need no change. The lane runs
   `audit:touched` only for the namespaces it edits.
5. **Stage 3 (optional): the profiler hint** "field built N times, never read at run
   time; mark it `ghost`", in `crates/rt/src/profile.rs`, next to compute-once's
   stage 0b line. Sonnet, 45 min. Tests: the profiler's unit tests, with one new
   example.

This doesn't replace any existing ticket I found. It absorbs the "erase proof-only
data" item in `aoc/NOTES-2021.md:2141` and the "out of scope" line of
`compute-once.md:435`.

Not covered: ghost lambda parameters and ghost arrows (D2903), ghost `let`, a linear
quantity, and measuring how much the other `Graph` days gain (I inferred it's small:
they build once already).
