# Parallel checking: what other provers do, and how it could fit Stitchwort (SW-4614)

**Status:** research note, Fable paper lane SW-4614, 22 November 2026, asked for by Matt
("I would do it at a formal level. I would survey the state of the art ... How might it fit
Stitchwort?"). Nothing was built, run or checked for it: the code was read at `1304e9793`, the
web sources on 22 November 2026, and the timings are this morning's from SW-4608. It informs a
decision about direction, which is Matt's; the questions are in [section 6](#6-decisions-for-matt).

**Updated 24 November 2026 (SW-4715, D3729)** for full proof irrelevance (D3722), interface
hashes (SW-4701) and digest-keyed cache entries (SW-4707): see
[section 8](#8-after-proof-irrelevance-sw-4715-24-november-2026), which replaces the
recommendation, the options' gains and the decisions below. The survey (section 1) and the
invariants (sections 2.3, 2.4) stand. What section 8 supersedes is marked **[superseded]**
where it sits.

Marks: **[verified]** read today in the primary source cited; **[secondary]** read in a source
that isn't the system's own (a forum, a later paper); **[not verified]** I believe it but did
not find or read a source today; **[measured]** a number from an earlier lane's run;
**[static]** computed from source text and those numbers by
[`parallel-checking/ns_graph.py`](parallel-checking/ns_graph.py); **[estimated]** my judgement.

## Summary

**The problem.** A cold check of all of `tools/fmt` takes 138 s and uses one core of ten. The
check is a loop over namespaces in one session on one thread
(`crates/driver/src/project.rs:319`, `check_in_order`).

**What others do.** Every mature prover parallelises at two levels, and they all rest on the
same idea: *a proof's statement is enough for everything after it, so the proof itself can be
checked later, elsewhere.*

| System | Files or modules in parallel | Proofs within a file in parallel | How independence is got | Reported gain |
|---|---|---|---|---|
| Lean 4 | yes (Lake) | yes, since v4.19 (May 2025): theorem bodies, kernel checks, code generation | the environment branches; the main branch sees a proof only as a task and blocks if it asks for more | none published that I found; Mathlib's import graph alone allows about 18x **[secondary]** |
| Rocq | yes (`make -j`) | yes: `Qed` proofs go to worker *processes*; `.vos`/`.vok` files | an opaque proof "shall behave exactly like an axiom" | 4x on 12 cores for the Odd Order Theorem (2015 paper) |
| Isabelle | yes (theory graph) | yes, since 2009: every top-level proof is a future | proofs are irrelevant in the logic; a theorem carries *promises* joined at the end of the theory | 3.0-3.2x on 4 cores, 5-6.5x on 8 |
| Agda | yes, since 2.9 (`-j`, "module granularity") | no | one isolated checker state per module thread | none found |
| Metamath, Dafny | per proof / per procedure | n/a | proofs are independent by construction | none checked |

**How Stitchwort differs.** Two things, one helpful and one not.

- *Helpful:* the check cache already stores a namespace's whole result in a form that doesn't
  depend on load order (declarations by full name and content hash, never by id), and loading
  it into another session is a tested path (a warm `tools/fmt` check, all 219 units from the
  cache, takes 2.1 to 4.1 s **[measured]**; section 3.1 says what that does and doesn't show). So "check namespace A in one session and hand the result to another"
  needs no new mechanism. The test sweeps already run one session per thread
  (`par_map_sessions`, `crates/driver/src/driver.rs:128`).
- **[superseded, section 8.1: theorems are sealed now, and a user's hash covers a theorem's
  statement only]** *Not helpful:* a Stitchwort theorem is **not** opaque. Its proof is part of its content
  hash, which every user's hash covers, and a later declaration can compute with it (`J`, a
  `case`, a comparison unfold it; `docs/core.md`, "Theorems stay folded too"). So the trick
  everyone else uses, "later declarations need only the statement", is false here as the
  language stands. It can be made true dynamically (block when someone asks for the proof, as
  Lean does) or by a language change (theorems opaque to the checker), and the second is a
  design decision of its own.

**How much is there to gain?** With this morning's per-namespace times (taken when the whole
check was 252 s, before today's speedups, so the shape is indicative only):

- **Namespaces in parallel:** `tools/fmt`'s 150 namespaces form a graph 25 levels deep whose
  slowest chain was 81 s of 237 s. That caps the gain at **2.9x** for the project part and
  **2.5x** with the standard library checked first on one core; 4 workers get 2.2x, 6 get 2.45x,
  and more than 6 add nothing **[static]**. AoC is the opposite shape: 291 namespaces, 5 levels
  deep, 106 wide, so a whole-AoC check would scale nearly with the cores **[static, no times]**.
- **Proofs in parallel as well:** at least 60% of `tools/fmt`'s declaration time is theorem
  bodies (155 s of 260 s in the 200 slowest declarations alone, 97% of that list **[static
  from measured]**). If proofs could run apart from the chain, the cap would be the largest
  single proof (32 s then), about 8x, so the ten cores would be the limit, not the graph
  **[estimated, an upper bound]**. Isabelle's and Rocq's real figures (3x on 4 cores, 5-6x on
  8, 4x on 12) say to expect roughly half of an ideal bound.

**Recommendation [superseded by section 8.4: option A is now stage 1 of a longer plan].**
Namespace-level parallelism on threads, one session per worker, results
handed over as check-cache entries (option A below). It reuses what exists, keeps the kernel
and values untouched (`Rc` stays), and its soundness argument is the check cache's. Leave
proof-level parallelism and shared (`Arc`) values as later, separate decisions: both touch the
kernel's evaluator or the language.

**First step, measurable, no compiler change:** (1) rerun `check --no-cache --timings=all` on
today's `main` and feed its unit table to the script, to replace the stale 2.5-2.9x with
today's bound (Overmind or the verifier; a lane may not run it); (2) a throwaway driver script
that runs `stitchwort check <namespace>` for ready namespaces as separate processes, several
at once, over one cache directory, and compares the cache's recorded hashes and the
diagnostics with a sequential run. That measures the real speedup, the replay overhead and
the memory, and tests determinism, before anything is designed in.

**For Matt [superseded by section 8.5]:** whether to pursue this now; whether a parallel `--no-cache` check may trust
results passed between sessions through the cache's encoding (it is what a warm check trusts
today); and, later, whether theorems should become opaque to the checker, which is what would
make proof-level parallelism simple.

---

## 1. Survey

For each system: what runs in parallel, how independence is established, how the kernel's
environment stays sound and ordered, how results stay deterministic, what is shared, reported
speedups, and limits. Sources are numbered in [section 7](#7-sources).

### 1.1 Lean 4

**Modules (Lake).** Lake builds a package's modules as jobs, each a Lean `Task`; a module is
built after its imports ("The root is built by recursively building its local imports" [L7]),
and up-to-date checks compare traces, which are hashes of the inputs [L7] **[verified]**. Each
module is elaborated by its own `lean` run and written as an `.olean`, which importers load as
compacted regions mapped at "an arbitrary but deterministic base address for `mmap`" [L2]
**[verified]**. That Lake runs these jobs concurrently is not stated in the documents I read
(the `Job` type is "The Lean `Task` object for the job" [L8]); I take it from the Zulip thread
below, where users report 800-1400% CPU during a Mathlib build **[secondary]**. The thread
count is process-wide (`LEAN_NUM_THREADS`), not a Lake option [L9] **[secondary]**.

**Within a file (since 2025).** Lean 4.18 (2 April 2025) "enables code generation to proceed
in parallel to further elaboration" (#6770) and "introduces the central parallelism API for
ensuring that helper declarations can be generated lazily ... without duplicating work or
creating conflicts across threads" (#7076) [L5]. Lean 4.19 (1 May 2025) "enables the
elaboration of theorem bodies, i.e. proofs, to happen in parallel to each other as well as to
other elaboration tasks" (#7084), with follow-ups making `match` equations, equation and
unfold lemma generators "compatible with parallelism" (#7247, #7261, #7348) [L4]
**[verified]**. The option is `Elab.async`: "perform elaboration using multiple threads where
possible"; it "defaults to `false` but (when not explicitly set) is overridden to `true` in
the Lean language server and cmdline" [L3] **[verified]**. PR #7084 says a theorem is
elaborated in parallel only when it is not in a `mutual` block (and `Elab.async` is on) [L6]
**[verified]**.

**How independence is established.** Not by analysis: by construction, with blocking as the
fallback. The elaborator's environment *branches* [L2] **[verified]**:

- `addConstAsync` "Starts the asynchronous addition of a constant to the environment"; the
  environment is split into a main branch and an async branch. The main branch has the
  constant's name and kind at once; its signature ("level params and type, potentially filled
  asynchronously") and its full info are tasks.
- A lookup on the main branch blocks if what it asks for isn't there yet: `find?` "blocks
  until the constant's info is fully available"; `findConstVal?` "blocks on everything but the
  constant's body". So code that needs only a theorem's statement never waits for its proof,
  and code that does look at the body waits and gets the same answer as a sequential run.
- An async branch may only add declarations named under its own declaration: "All constants
  added to this environment branch must have the name as a prefix" (`AsyncContext.declPrefix`).
  That makes generated names collision-free without coordination.
- Environment extensions (the tables metaprograms keep) declare how they behave across
  branches: `sync` ("Safest access mode, writes and reads the extension state to/from the full
  `checked` environment"), `local`, `mainOnly` (the default, which "panics when trying to
  modify the state on anything but the main branch"), `async`.

**The kernel's environment and its order.** "The kernel environment type
`Lean.Kernel.Environment` enforces a linear order on the addition of" declarations; "the
kernel environment really lives only in the right-most path, with all other paths merely
holding" an unfulfilled task [L2] **[verified]**. `Environment.checked` is the "Kernel
environment task that is fulfilled when all asynchronously elaborated declarations are"
finished. `addDecl` runs the kernel's type check itself as a task when `Elab.async` is on, for
a theorem, a definition, a one-definition mutual block, an opaque constant or an axiom;
anything else is "adding synchronously" [L1] **[verified]**. On a kernel failure the
declaration is added as an axiom, to "avoid follow-up errors" [L1], the same idea as
Stitchwort's stand-ins.

**Determinism.** Each forked task gets a child name generator (`mkChild`), so fresh names
don't depend on timing; heartbeats (the deterministic timeout count) are carried into the
task, "such that forking off an action doesn't suddenly allow it to succeed from a lower
heartbeat count"; a task's messages and info trees come back as a *snapshot tree* attached at
a fixed place, not in arrival order [L3] **[verified]**. Lazily generated helpers
(`realizeConst`) "will run using the given environment and options to ensure deterministic
results" [L2] **[verified]**.

**Shared.** Threads in one process share the immutable environment and all objects.
**[not verified]** (from memory of the Lean 4 runtime papers): Lean's reference counts are
atomic only for objects marked as shared between threads.

**Speedups.** I found no published figure for `Elab.async`. PR #7084 gives none [L6]. For
module-level parallelism, a November 2023 Zulip thread measured a Mathlib build on a 56-core
machine at 16 min 23 s of wall time for 253 min of CPU, about 16x, and a "longest pole" tool
put the import graph's bound (total time over critical path) at 18x; Scott Morrison's
conclusion was "In-file parallelism (coming!) will help here" [L9] **[secondary]**.

**Limits and bugs.** The rollout broke Mathlib at first (the PR carried `breaks-mathlib`
[L6]); metaprograms that read the info state "may need to call `InfoState.substituteLazy`"
(#7457), and a "parallelism regression where linters ... would no longer find such messages"
was fixed in the same release (#8101) [L4]; an `Elab.async` regression cancelled elaboration
tasks on edit (#7175) [L5] **[verified]**. The lesson for us: the hard part was not the
kernel but every table and tool that assumed one thread and one order.

### 1.2 Rocq (Coq)

**Files.** `rocq makefile` projects build with `make -j`; a `.vo` depends on the `.vo` files
it requires **[not verified today for `.vo`; verified for `.vos`/`.vok` below]**.

**Proofs, interactively (the STM).** Rocq "can separate" checking statements and definitions
from "the construction and checking of proofs objects" [R1] **[verified]**. The 2015 paper
(Barras, Tankink, Tassi, ITP 2015 [R4]) describes the design:

- The document is a DAG of states (nodes) and commands (edges), run by the *State Transaction
  Machine*; proofs are branches.
- The kernel was changed so an opaque proof is a delayed computation: "After an opaque proof
  enters the environment, it shall behave exactly like an axiom", and the type of opaque proofs
  became a function from the environment to a term. The trusted base grew by "less than 300
  lines (circa 2% of its previous size)".
- Workers are separate **processes**, because OCaml (then) had no shared-memory parallelism:
  "the most natural way to exploit parallel hardware is to split the work among different
  worker processes". The state is marshalled to them, with care about what can't be sent.

**Conditions** [R1] **[verified]**: "only opaque proofs (ending with Qed or Admitted) can be
processed asynchronously"; inside a section the proof must start with `Proof using`, because
otherwise the statement (which section variables it takes) is only known after the proof
("the presence of Proof using is needed to process proofs asynchronously in interactive
mode"); a proof expected to take under 0.03 s is not delegated.

**Universe constraints: the known soundness-shaped gap.** A proof can add universe
constraints, which are global. In interactive mode workers return proof objects, but "this
will not be automatically checked by the kernel of the main process"; one must ask for a full
check, and "Only then all the universe constraints are checked"; universe inconsistencies are
the errors "reported late" [R1] **[verified]**. In batch mode, `-vos` skips opaque proofs and
"fewer universe constraints are collected", so "At the end of the day, one still needs to
proof check all files by producing standard `.vo` files" [R2] **[verified]**. So Rocq's
parallel modes are *development* modes; the trusted result is still the sequential `.vo`
build (and `rocqchk`, an independent re-check of compiled files, which the manual does not
describe as parallel [R2]).

**Batch files.** `.vio` files (the 2015 design: statements now, proof tasks later) were
removed in 8.20 (PR #18424: "`.vos` files provide a viable alternative ... we have no plans to
address the remaining vio bugs") [R5] **[verified]**. Today: `rocq c -vos foo.v` writes the
interface, skipping opaque proofs; `rocq c -vok foo.v` checks the file fully against the
`.vos` files of what it requires. `foo.vok` does not depend on `bar.vok`, so "`make vos`
compiles all statements first, then `make -j vok` checks proofs in parallel"; the cost is that
"definitions are parsed and typechecked twice" [R2] **[verified]**.

**Within a proof.** `par:` "Applies `ltac_expr` to all focused goals in parallel", but "only
works on goals that don't contain existential variables" and the tactic "must either solve the
goal completely or do nothing"; workers are set by `-async-proofs-tac-j` [R3] **[verified]**.
The condition is the interesting part: shared unknowns between goals are exactly what breaks
independence.

**Speedups** [R4] **[verified, from the paper]**: the Odd Order Theorem, on Coq 8.4 one core "a
bit less than two and a half hours"; file-level on 12 cores about 12 minutes of latency limited
by file dependencies; with quick compilation plus proofs on 12 cores about 20 minutes in all,
"166% of the theoretical optimum"; the headline is "four times faster" at full checking on
twelve cores. Limits named: only `Qed` proofs; the granularity of proofs; memory ("each worker
needs roughly the same memory as the master" [R1]); the garbage collector at "more than 20% of
the time" on the largest files; not stable on Windows [R1].

### 1.3 Isabelle

The most developed, and the oldest. Wenzel, "Parallel Proof Checking in Isabelle/Isar" (2009
[I1]) **[verified, read in full]**:

- **Four layers:** the DAG of theories (loaded in parallel along independent paths);
  definitions and statements inside a theory ("we assume strictly sequential dependencies and
  refrain from any attempt at parallelizing specifications that happen to be logically
  independent ... because checking of toplevel specifications is usually fast"); **top-level
  proofs**, the main source of parallelism; nested sub-proofs (left in reserve).
- **Why proofs are independent:** "(1) checking proofs requires most of the total runtime, and
  (2) proofs are practically irrelevant in the sense that we merely need to know that
  certification was finished successfully at some point." In HOL "proofs are formally
  irrelevant by design of the core calculus".
- **The kernel change:** a theorem may carry *promises*, "treated like axioms with an explicit
  indication", each with a future proof; `future-thm: thm future → term → thm` turns a future
  proof and its stated result into a theorem at once. The cost: "we loose purely static
  integrity of LCF kernel results: entities of type thm may contain holes that might fail to
  be filled ... Explicit dynamic checking via join-proof is required". Integrity is recovered
  by joining all promises "at certain checkpoints of the theory loading process".
- **Futures** in ML (`future`, `join`, `cancel`), with a scheduler over a task queue with
  dependencies; a worker that joins an unfinished future runs other tasks meanwhile.
- **Shared memory**, one process, immutable data; "Imperative techniques require extreme care".
- **Results:** "quite good speedup factors of 3.2 for 4 cores" on sessions with many
  independent theories or proofs; "real-world speedup is still 3.0 for 4 cores in the best
  case"; under 1.3 for the main HOL session with proof terms; "≈ 5 for 8 worker threads" in
  early tests. Garbage collection was sequential and "about 5-15%" of the time, which Amdahl's
  law turns into the ceiling.
- **On dependent type theory**, from the same paper: "the more complex type-theory of Coq (and
  similar dependently-typed calculi) involves formal dependencies between proofs. This reduces
  the potential for proof parallelism, although the practical impact probably depends on the
  actual application." This is the point section 2 makes precise for Stitchwort.

Matthews and Wenzel (DAMP 2010 [I2]) **[verified]**: the 2010 implementation "is able to
address more than 8 cores effectively, while ... Isabelle2009 ... works best for 2-4 cores.
Scalability beyond 16 cores still poses some extra challenges"; "The maximum speedup is ≈ 5.0
... 6.5" on a 32-core machine, where "it does not make much sense to use all 32 cores";
bottleneck 1 is garbage collection. Later work (Wenzel, ITP 2013, "Shared-Memory
Multiprocessing for Interactive Theorem Proving"; I read only its abstract's summary, "2-32
cores; saturation of 8 cores is already routine" **[secondary]**) and the 2022 community
benchmark (Huch and Bode [I3]: best performance at "8 to 16 threads" **[verified, abstract]**)
agree: a ceiling around 5-6x, set by memory management and the sequential parts.

PIDE, the editor side, uses the same futures for asynchronous checking of a document being
edited; Rocq's 2015 work plugged into it [R4].

### 1.4 Others, briefly

- **Agda.** Since 2.9.0: `--parallel[=N]`, `-j[N]`, "Type check in parallel ... The default,
  -j1, means type checking is sequential. Parallelism has module granularity." [A1]
  **[verified]**. The implementation checks each non-main module in "a thread (with isolated TC
  state)", and "checking of the given module will block until all of its imports have been
  checked" [A2] **[verified]**. This is exactly option A below: one isolated checker state
  per module thread, results merged as decoded interfaces. No speedup figure found.
- **Metamath.** Proofs are independent given the statements before them, so verification
  splits freely: `metamath-knife` has `--jobs` ("Number of threads to use for verification"),
  splits large files into segments, and re-verifies incrementally by segment [M1]
  **[verified]**. The cleanest case: no elaboration, no shared unknowns.
- **Dafny/Boogie.** Each method is a separate verification condition for the SMT solver; from
  the command line methods are verified one at a time unless `/vcsCores` is used, and in the
  IDE "the default is concurrent execution of proof attempts" [D1] **[verified, the FAQ; the
  newer `--cores` flag's default not verified]**. Independence is by design: a method is
  verified against other methods' *specifications*, never their bodies.
- **F#** (not dependently typed, but the same engineering): graph-based type checking of the
  files of a project in parallel, with the graph found from the untyped syntax tree by a trie
  of names, "a super-set of the actual dependency graph" [F1] **[verified]**. Stitchwort's
  `namespace_edges` is the same kind of pre-pass.
- **Typed Racket / Hindley-Milner research.** Newton et al., PPoPP 2016: "8.46× parallel
  speedup on 14 cores" for Typed Racket's checker using deterministic-by-construction LVars
  [P1] **[secondary: the conference listing, not the paper]**.
- **F\*, Idris 2, HOL4, HOL Light.** **[not verified]** I found no primary documentation
  today. From memory: F\* writes a `.checked` file per module and parallelism is `make -j`
  over them; HOL4's `Holmake` takes `-j`; Idris 2 and HOL Light check sequentially. Treat
  these as unconfirmed.
- **Research on parallel elaboration of dependent types itself:** I found none beyond the
  systems above. The published designs all parallelise *between* declarations; none
  parallelises unification inside one.

### 1.5 What the survey says

1. Everyone has module-level parallelism, and it is limited by the import graph (Mathlib:
   about 18x; Rocq's Odd Order: "limited by file dependencies").
2. Everyone who went further did the same thing: split a declaration into a *statement*,
   available at once, and a *proof*, a future. The kernel treats a pending proof as an axiom
   or a promise and the final environment is complete only after a join.
3. Independence is never inferred: it holds by a rule of the language (opaque `Qed`,
   irrelevant HOL proofs), and where it might not hold the main thread blocks (Lean's `find?`).
4. The costs were in determinism and tooling (names, messages, tables, linters), in memory
   (Rocq's workers, Isabelle's collector), and in soundness corners where a proof has a global
   effect (Rocq's universe constraints).
5. Real speedups are 3x on 4 cores and 5-6x on 8.

## 2. The formal level: what independence a dependently typed checker needs

Notation. An *environment* `Σ` is a sequence of declarations, each with a name, a statement
(type) and perhaps a body. The kernel's judgement `Σ ⊢ d` says declaration `d` is accepted
after `Σ`. *Elaboration* is a function from source text and the elaborator's state to
declarations and messages; it calls the kernel and the evaluator on `Σ`.

### 2.1 What a later declaration can observe of an earlier one

For a later declaration `e` and an earlier `d`, checking `e` can depend on:

1. **`d`'s statement**, if `e` mentions `d`.
2. **`d`'s body**, if conversion or evaluation unfolds `d` while checking `e`. For a
   transparent definition this is the normal case: its body matters to everything after it.
3. **Facts derived from `d`'s body** that are stored on `d`: in Stitchwort, the entry arity,
   the inert proof parameters (`docs/core.md` line 175: a caller's `byComputing` "can come to
   depend on the body ignoring a proof"), whether it folds, its group.
4. **`d`'s identity for hashing and caching**: in Stitchwort a hash "covers everything it
   depends on" (`docs/core.md`, "Tests and content hashes"), body included.
5. **Whether `d` succeeded.** In Stitchwort a failed `def` or `theorem` is replaced by a
   *stand-in* assumption of its statement and its users "are never finished" (`docs/core.md`,
   "Stand-ins"); a declaration that uses a failed one that has no stand-in waits
   (`E-USES-FAILED`).
6. **The elaborator's tables** that `d` wrote: names, instances, records, lifted helpers,
   `@[walk]` lemmas, which library files have been loaded.
7. **Nothing else, if the design is right**: not `d`'s numeric id, not the order of unrelated
   declarations, not how warm the evaluator's caches are.

### 2.2 Theorems in Stitchwort are not opaque

**[superseded, 24 Nov 2026]** This section describes the language before D3722. Lemma B below
now holds by rule, with no condition: section 8.1.

In Lean, Rocq (`Qed`) and Isabelle, item 2 is empty for theorems by a rule of the system. In
Stitchwort it is not:

- "There's no definitional proof irrelevance: two different proof terms aren't automatically
  equal" (`docs/core.md` line 145). Comparison skips proofs only at *proof positions* (line
  276).
- A theorem applied to its arguments stays folded, but "only three things look inside a proof:
  a `case` on it ..., `J`, and a comparison; each unfolds a folded call first" (line 266;
  `folds`, `crates/core/src/value.rs:2819`). So `J` along a theorem's proof computes with the
  proof's body. Opacity is a separate, explicit feature (`opaque def`, "Opaque definitions"),
  and only "A theorem with [an `unfolding` list] is submitted opaque".
- A theorem's hash covers "whether it's a theorem, its type and its body", and every user's
  hash covers the theorem's. (A *proofless* hash exists beside it, `proofless_hash`,
  `crates/core/src/hash.rs:134`, in which "A definition whose result is a proof is its type
  alone"; it "decides nothing the kernel accepts, and nothing is cached by it".)

So the statement/proof split is available in Stitchwort only under a *demand* condition:

> **Lemma B (body independence, dynamic).** Let `d` be a theorem with statement `T`. Checking
> `e` after `Σ, d` gives the same verdict, terms and messages as checking `e` after
> `Σ, (d : T, no body)`, provided the check of `e` never (i) unfolds a call of `d`, (ii) reads
> `d`'s content hash, or (iii) walks `d`'s body (reliance on assumptions, `axioms`). The
> existing *assumption* form (`check::assume`) is exactly "`d : T`, no body, never unfolds".

Whether (i) ever happens in `tools/fmt`, std or AoC is an empirical question nobody has
measured; a counter in the three unfolding sites would answer it. (ii) happens when `e`'s own
hash is computed, which can wait until `d` is done, since hashes are computed on demand and
memoised (`hash.rs:144`), unless something during `e`'s elaboration asks for a hash (an
`unfolding` list is "hashed in a canonical order" of hashes; a group's members are ordered by
shape hash).

Two ways to make Lemma B usable: **block on demand** (if `e` hits (i)-(iii), wait for `d`'s
proof; needs threads that share `d`, so needs option D below), or **make it a rule**
(theorems opaque to the checker, hashes of users cover the statement only or wait for the
join). The second is a language and kernel change with its own consequences (proofs by `J`
along a theorem would need the theorem listed in `unfolding`, or would be stuck).

### 2.3 Definitions, groups and order

> **Lemma W (weakening).** If `Σ ⊢ e` and `Σ'` is a well-formed environment containing `Σ`'s
> declarations that `e` depends on, with the same content, then `Σ' ⊢ e`, with the same
> elaborated terms and content hashes. Needs: the kernel's rules consult only declarations
> reachable from the term (true of conversion and unfolding); rules switched on globally are
> switched on in every session before any user code (the `Nat.addZero`/`addSucc` rules,
> `nat_add::register`, and the built-in bindings are in the always-loaded core).

> **Lemma O (order).** The kernel requires a signature to mention only final declarations and
> a body only final ones and its own group (`docs/core.md`, "Groups of definitions"). So any
> order of environment extension that respects the dependency DAG of strongly connected
> components is acceptable to it, and by Lemma W gives each component the same verdict. A
> mutual group is one indivisible unit: "Install, all or nothing".

> **Lemma H (hashes).** Content hashes ignore names, ids, locations and order (data types
> excepted: nominal), so two sessions that admit the same components in different DAG-respecting
> orders compute equal hashes for equal content. The cache relies on this already: entries
> refer to declarations "by full path and the content hash they are expected to have, never
> by load-order ids" (`crates/elab/src/cache/mod.rs:13`).

What Lemma O does *not* give: equal ids, equal iteration order of id-keyed tables, or equal
messages if a message's order or wording depends on ids. Those are the next invariant.

### 2.4 The invariants a parallel design must keep

Let `C(N)` be the dependency closure of namespace `N`. A sequential cold check elaborates
namespaces in `canonical_order` (`crates/driver/src/project.rs:1235`: each after what it uses,
ties by name), all in one session.

- **I1 (closure only).** The result of elaborating `N` (declarations, hashes, messages,
  tables written) is a function of `N`'s sources and the results of `C(N)`, and of nothing
  else that happens to be loaded. Already assumed: a namespace's cache key is "the hash of its
  sources ... and the keys of the namespaces it depends on (a Merkle chain)"
  (`cache/mod.rs:27`), and library files were made to obey it (SW-1354, SW-1362: "its result
  doesn't depend on what else the run loads").
- **I2 (order within the closure).** The result does not depend on the relative order in which
  the members of `C(N)` entered the session, beyond the DAG. Either true (needs an audit of
  every id-ordered iteration: instance search, `auto`, name suggestions), or made irrelevant
  by always loading `C(N)` in the project's canonical order, restricted to `C(N)`. The editor
  already deviates from the canonical order (`load_namespaces_for` puts the edited namespace
  last, `project.rs:566`), so I2 is already leaned on.
- **I3 (replay ≡ elaboration).** A session that got `C(N)` by replaying entries behaves, for
  `N`, as one that elaborated `C(N)`. This is the check cache's contract
  (`docs/proposals/check-cache-trust.md`; the differential tests pin `refused == 0`).
- **I4 (local names).** Generated names are scoped to their owner and numbered within it
  (`owner.%matchN`, `crates/elab/src/lift.rs:679`; assumption labels are owner plus hole
  number), never from a session-wide counter. Compare Lean's `declPrefix` rule.
- **I5 (no cross-declaration unknowns).** Metavariables and postponed checks live in the
  attempt and the declaration (`state::Attempt`, `state::Decl`, "emptied after it",
  `crates/elab/src/lib.rs:404`); the kernel "holds no metavariables"
  (`crates/core/src/globals.rs:745`). So there is nothing like Rocq's shared existential
  variables between declarations, and the unit of parallelism can be as small as a component.
- **I6 (budgets).** Each component is "one operation, with its own resource limits"
  (`crates/elab/src/module.rs:515`). For determinism the *step count* of a component must not
  depend on session history, or a component near its limit could pass in one schedule and
  fail in another. Memo tables (glued calls' shared unfoldings, the read-back memo, hash
  caches) are the risk: they change when work is done, and I have **not verified** that they
  never change how many steps are counted across declarations. The same question already
  exists between a cold and a warm check.
- **I7 (reporting).** Messages are collected per namespace and printed in canonical order;
  step totals and timings are summed per declaration, not read off a shared counter.

> **Theorem (namespace-level).** Given I1-I7, a schedule that elaborates each namespace `N` in
> any session holding the results of `C(N)` (elaborated or replayed) yields, for every `N`,
> the same declarations, hashes, cache entry and messages as the sequential canonical check;
> and every declaration has been accepted by the kernel in exactly one session.

> **Theorem (proof-level).** Given also Lemma B's condition for every later declaration (by
> rule or by blocking), the bodies of theorems may be elaborated and checked in any order
> after their statements, against any environment containing what they depend on; the final
> environment is complete once every proof has been joined, and a failed proof turns its
> theorem into the stand-in it would have been.

## 3. Stitchwort today

### 3.1 How a check is organised

- **Driver.** `Session` = sources + one `Elaborator` (`crates/driver/src/driver.rs:43`).
  A project check analyses the files into namespaces with edges (`namespace_edges`,
  `crates/elab/src/project.rs:260`: an import's path, an imported item that is a namespace,
  and qualified references), orders them (`canonical_order`) and checks them one after
  another in the one session (`check_in_order`, `project.rs:319`;
  `check_project_namespace`, `:439`). A namespace's declarations are split into strongly
  connected components and checked in dependency order, each component one operation
  (`module.rs:501-516`).
- **Kernel.** `Kernel` = `env` (the declarations), `machine` (evaluator modes, the budget),
  `caches` ("What is derived from the environment, and can be worked out again")
  (`crates/core/src/globals.rs:751`). No universe constraints: levels are numbers and there
  is no cumulativity (`docs/core.md`, "Universes"), so Rocq's late-universe-error problem has
  no counterpart here.
- **Values are `Rc`.** `Value` holds `Rc<BigUint>`, `Rc<Unfolding>`, shared spines
  (`crates/core/src/value.rs:24-52`); `Def` holds `Option<Rc<Term>>`, `Rc<[DefId]>`
  (`globals.rs:24`). In `crates/core` and `crates/elab` there are about 1,640 uses of `Rc`,
  290 of `Cell`/`RefCell`, 33 of `Arc` (the cancellation flag and the like). Nothing in a
  session is `Send`.
- **Thread-locals** (about 40 `thread_local!` blocks): free lists and placeholders for
  dropping deep values (`value.rs:210`, `:672`; `term.rs:267`), the current declaration and
  span stack for reports (`budget.rs:129`, `:144`), step phases (`budget.rs:238`), the
  reference evaluator's test switches (`reference.rs:53-96`), recorded kernel rejections
  (`crates/elab/src/kernel.rs:35`), the failed-declaration keys of the component being
  checked (`module.rs:3238`). All are per-thread working state of one session: correct with
  one session per thread, and none is a process-wide table.
- **Budgets.** `Budget` (`crates/core/src/budget.rs:485`) is in the machine, uses `Cell`s, and
  is started per component; the cancellation flag is the one `Arc<AtomicBool>` in it.
- **Sessions on threads exist already.** The test sweeps: `par_map`
  (`driver.rs:95`), `par_map_sessions` (`:128`: one session per worker thread, rewound to
  fresh before each item), up to `test_threads` = min(cores, 8) "each session holds tens of
  MB" (`:82`). The language server: one checker thread and a pool of search workers, each
  with its own session (`crates/lsp/src/lib.rs:480-500`). Sessions rewind: `mark`/`rewind`,
  `mark_fresh`/`rewind_fresh` (`crates/driver/src/rewind.rs:49-91`).
- **The check cache** (`crates/elab/src/cache/mod.rs`): one entry per library file or project
  namespace, holding "everything loading the unit adds that later code reads"; keyed by text
  and dependency keys before anything is elaborated; loaded by *replay* through the kernel's
  trusted admission, in the order elaboration made the declarations. Entries are written
  atomically (a temporary file, then a rename: `crates/driver/src/check_cache.rs`,
  `write_atomically`). Limits that matter here: "Only units without errors are written", and
  a namespace that has or relies on an open goal is never stored.
- **Cost of replay [measured, SW-4410,
  `docs/proposals/check-cache-across-updates.md` "Measured"]:** a warm `tools/fmt` check with
  exact entries, 219 units: 2.1 s, 0.74 GB; a session carrying every entry over (trusted, with
  the decode self-check): 4.1 s, 1.34 GB; a kernel re-check of every entry: 42.6 s, 1.55 GB;
  cold: 340 s and 3.85 GB then (252 s and 3.25 GB this morning, SW-4608; 138 s now). **Caveat:**
  a plain warm `check` leaves out namespaces "it can report from their cache entries without
  loading them" (`plan_skips`, `project.rs:398`), so the 2.1 s run may have replayed few of
  them; I don't know whether the 4.1 s run skipped any. So "a full replay of `tools/fmt` costs
  **2 to 4 s and 0.7 to 1.3 GB**" is the range these runs support, not a measurement of
  replay itself; `STITCHWORT_SKIP_UNNEEDED=0` on a warm check would measure it.
- **The playground** is the same crates compiled to `wasm32` (`crates/web`), one thread.

### 3.2 The namespace graphs [static]

`python3 -I docs/proposals/parallel-checking/ns_graph.py SRC [UNITS_CSV]` reads the `.sw`
files and rebuilds the edges as `namespace_edges` does, from text (so approximately: see the
script's header), then weighs each namespace by its elaboration plus kernel time in
`docs/reviews/SW-4608/fmt-units.csv`. **Those times are this morning's, from the 252 s run,
before SW-4609 to SW-4637 cut the check to 138 s; the cuts were in the largest proofs, several
of them on the critical path, so today's numbers will differ.**

| Project | Namespaces | Edges | Depth | Widest level |
|---|---:|---:|---:|---:|
| `tools/fmt` | 150 | 1,222 | 25 | 15 |
| `aoc` | 291 | 473 | 5 | 106 |
| `games/rogue` | 3 | 2 | 2 | 2 |

`tools/fmt`, weighted (236.6 s of project work, 23.9 s of core and library files):

- **Critical path 81.3 s over 16 namespaces**: `Syntax` 4.3, `Fmt` 1.2, `Syntax.SharedFacts`,
  `Fmt.CalmProofs` 1.5, `Fmt.SpellProofs` 2.1, `Fmt.JoinProofs` 1.9, `Fmt.TreeJoinProofs` 0.8,
  `Fmt.OutputStatements` 4.4, `Fmt.FileLexProofs` 13.3, `Fmt.OutputFileProofs` 5.2,
  **`Fmt.SettleOutputProofs` 41.7**, `Fmt.HearProofs` 0.3, `Fmt.StandsProofs` 1.5,
  `Fmt.ElementsProofs` 1.0, `Fmt.TopStatements` 1.3, `Fmt.CommentsKeptProof` 0.8.
- **Bound: 2.91x** (work over critical path), for the project part.
- A greedy schedule (each ready namespace to the first free worker, ties by name):

  | Workers | Project part | Speedup | With the library block first, sequential | Speedup |
  |---:|---:|---:|---:|---:|
  | 1 | 236.6 s | 1.00x | 260.5 s | 1.00x |
  | 2 | 135.6 s | 1.75x | 159.5 s | 1.63x |
  | 4 | 94.5 s | 2.50x | 118.4 s | 2.20x |
  | 6 | 82.5 s | 2.87x | 106.4 s | 2.45x |
  | 8 | 81.4 s | 2.91x | 105.3 s | 2.47x |
  | 10 | 81.3 s | 2.91x | 105.2 s | 2.48x |

  This leaves out each worker's cost of loading what a namespace depends on (section 4, A).

- One namespace, one proof: half the critical path was `Fmt.SettleOutputProofs`, and 32 s of
  that was the single theorem `standsEachFile`. Namespace-level parallelism can never beat
  the slowest namespace; splitting a large proof namespace helps exactly as much as it
  shortens the chain.

**Standard library.** Its files have no usable import graph in their text (45 of 133 have an
`import`; files load on demand when a name is used, and which files a unit needs "is only
known once it is elaborated", `cache/mod.rs:31`), so I treated it as a sequential block:
9% of the `tools/fmt` check, but 87-98% of a cold check of one AoC day **[measured, SW-4608]**.
For a cold std, the library's own order is where parallelism would have to be found; in
normal use it is cached and costs 0.43-0.49 s.

**AoC.** No whole-AoC per-namespace times are in the repo, so no weighted bound. The shape
(depth 5, 106 namespaces on one level: the days are independent of each other, each a short
chain of Spec, solution, Proofs, Tests over `Aoc.Common`) means a whole-AoC `check --no-cache`,
which Overmind runs on every push, should scale close to the number of workers once std is
loaded **[estimated]**.

### 3.3 How much is proof bodies [static from measured]

`fmt-decls-top200.csv` has the 200 slowest declarations: 158.9 s of the 259.5 s of declaration
time. Looking each up in the sources: **188 are theorems, 154.7 s** (127.6 s elaboration,
27.1 s kernel); 5 type groups 2.3 s; 6 definitions 1.6 s. So theorem bodies are at least 60%
of the whole check and 97% of the slow tail; the other 12,900 declarations (100 s) were not
classified. If theorem bodies ran apart from the namespace chain, the chain would carry only
statements and definitions, and the limit would become the largest proof: 32.5 s then
(`standsEachFile`), a bound of about 8x at this morning's weights **[estimated upper bound]**.

## 4. Options

### A. Namespaces in parallel: a session per worker thread, results passed as cache entries

**What changes.** The driver, not the kernel or the elaborator's core. A scheduler walks the
namespace DAG; each ready namespace goes to a worker thread that owns a `Session`. The worker
makes sure its session holds the namespace's closure by replaying entries, elaborates the
namespace, and publishes its entry: to the store as now, and, for `--no-cache` and for
namespaces the store refuses, to an in-memory map for this run. The main thread prints
messages in canonical order. The `Store` handed to each session must be usable from several
threads (today it is used through `Rc`; the directory store itself is plain files with atomic
writes).

Things to settle in a design:

- *Which order a worker's session loads a closure in.* Strictest: the project's canonical
  order restricted to the closure, rewinding a kept session to the longest shared prefix
  (I2 then holds trivially). Cheapest: keep sessions and add what is missing in any DAG order
  (needs I2 audited). Start strict and measure the rewinding.
- *Namespaces with errors or open goals* are not cacheable today (`tools/fmt` sets
  `open-goals: warn`). Their results must still reach dependents: either an in-memory entry
  kind that carries stand-ins and assumptions (the cache's "stage 5" is the same work), or
  dependents elaborate such a namespace again themselves (correct, wasteful only when there
  are errors).
- *Library files loaded on demand*: two workers may want the same uncached file at once. A
  claim per unit (the first elaborates, the others wait and replay) avoids the duplicate work.
- *`--timings`, step totals, progress and cancellation* become per-worker and are merged.

**Soundness.** By the namespace-level theorem: each declaration is accepted by the kernel in
the one session that elaborated it; other sessions take it by trusted replay, which is what
every warm check does today. Nothing new is trusted, but more rests on it: **with this
option, `--no-cache` no longer means "one kernel saw everything in one environment"**; it
means "every declaration was checked by this build's kernel once, and moved between sessions
by the cache's encoding". That is I3, guarded by the differential tests and the decode
self-check. A stricter mode (re-check on replay) exists (`--recheck`, 42 s for all of
`tools/fmt` in one session **[measured, SW-4410]**) but would cost each worker more than it saves. This is a trust
question, so it is Matt's.

**Determinism.** Hashes: Lemma H. Cache entries and keys: keys are computed from text before
elaboration; an entry's content depends on I1-I3. Messages: I7. Step counts: I6, the one I
could not settle by reading. Generated names: I4 holds. A cheap, strong test exists: run the
parallel check and the sequential one and compare every entry's bytes and every message.

**Memory.** Each worker holds its closure plus the namespace being elaborated. A session with
all of `tools/fmt` loaded from the cache is 0.7 to 1.3 GB (section 3.1); a cold sequential
check peaked at 3.25 GB. Six workers late in the graph would hold up to six such sessions plus
their working peaks: perhaps 6-12 GB **[estimated]** on the 32 GB machine. This is Rocq's "each worker needs roughly the
same memory as the master", and the reason to cap workers by memory as well as cores (and why
lanes sharing the machine matter: three build lanes each running a 6-worker check is not
free).

**Replay overhead.** About 2 to 4 s for a worker to load the whole project once (section
3.1); with strict canonical-prefix rewinding, more, depending on how often a worker's next
namespace shares little with its last. Bounded above by 150 full replays, 300 to 600
CPU-seconds spread over the workers **[estimated, pessimistic: most closures are far smaller
than the project]**; the experiment below measures it.

**Editor and playground.** The language server already checks on its own thread with its own
session; parallel loading of a project when it opens would use the same scheduler, and edits
stay as they are (one namespace rechecked). The playground has no threads (wasm32, one
instance): threads there need shared memory, which needs a cross-origin isolated page [W1]
**[verified]**, or Web Workers each with their own instance passing entries as bytes, which
this option's "sessions share nothing but entries" design happens to fit. Not needed at
first: playground programs are small.

**Speedup [static, stale weights].** `tools/fmt` cold: 2.2x on 4 workers, 2.45x on 6, ceiling
2.5x (2.9x if the library is warm). On today's 138 s that would be 55-65 s if the shape were
unchanged, which it isn't; rerun to know. Whole-AoC cold: near-linear in workers after std
**[estimated]**. A warm or one-namespace check: nothing (already seconds, or one namespace).

**Size and risk.** Medium: driver and store work, a scheduler, merging of reports; no kernel
change, no change to terms, hashes or the cache format unless errors are to be carried. Risk
is in I1, I2 and I6 turning out false somewhere; each failure is found by the byte-compare
test, and each would also be a latent check-cache bug today.

### B. Theorem bodies in parallel after their statements, within a namespace

**What changes.** The elaborator elaborates every statement of a component first (it already
does signatures before bodies within a group), installs each theorem as a *promise* (the
assumption form: statement, no body), carries on, and elaborates the bodies as tasks; at the
end of the namespace it joins them, turning each promise into the theorem or its stand-in.

**[superseded, 24 Nov 2026]** B2 below is what was decided and built (D3722: theorems are
sealed, with no `unfolding` opt-out). Section 8.3 gives B as it stands now.

**Soundness.** By the proof-level theorem, *if* Lemma B's condition holds. In Stitchwort it
does not hold by rule (section 2.2). So B needs one of:

- **B1, block on demand:** an unfold of a promise, or a read of its hash, waits for the proof.
  That needs the waiting thread and the proving thread to share the declaration, so shared
  values: option D first.
- **B2, a rule:** theorems are opaque to the checker (never unfolded while checking, unless
  listed in `unfolding`), and a user's hash waits for the join. Then a promise and a finished
  theorem are indistinguishable to later declarations, and bodies can even be checked in
  separate sessions (each replays the statements-only environment, as Rocq's `.vos` then
  `.vok`). This changes what programs are accepted: any proof that today computes through a
  theorem's body with `J` or a `case` would need the theorem named in `unfolding`. How many
  do is unknown. **A language change, so a design note and Matt's decision.**

Also to handle either way: `--only` and reliance (`relied_on`) walk bodies; a failed proof
discovered late must give the same messages as today (users of a stand-in "are never
finished"; today they are elaborated *after* the failure is known, and may word things
differently); `@[walk]` lemmas and other theorem-reading tactics read statements only
**[not verified]**.

**Speedup.** On top of A, the bound moves from the namespace chain to the largest proof:
up to about 8x at this morning's weights, in practice perhaps 4-6x on ten cores going by
Isabelle and Rocq **[estimated]**. Without A (bodies in parallel inside one namespace, the
namespaces still in sequence) it would already cut the slow namespaces to their largest
proof each.

**Size and risk.** Large. B2 touches the kernel's unfolding rule, hashing, `docs/core.md`,
the guide, and possibly many proofs. B1 needs D.

### C. Worker processes, as Rocq

**What changes.** As A, but each worker is a `stitchwort` process and the cache directory on
disk is the only channel (for `--no-cache`, a temporary one).

**For:** crash isolation (a stack overflow aborts a process, `driver.rs:63-69`, and would take
only one worker with it); memory is returned when a worker exits; it can be tried today with
a script and no compiler change. **Against:** each process loads the core and replays its
closure from scratch (about 0.1 s for the core, up to 2 to 4 s for a full closure, times 150
namespaces: up to 300 to 600 CPU-seconds **[estimated, pessimistic]**, against 237 s of real
work),
unless workers are long-lived, which needs a protocol; nothing in memory can be passed, so
namespaces with errors must be re-elaborated by dependents; no use in the language server or
the playground. Rocq chose processes because OCaml had no shared-memory threads [R4]; Rust
has them, and Agda, in the same position as us, chose threads with isolated state [A2].

**Use:** as the experiment (below), not the end state.

### D. Values that can cross threads (`Arc`) against `Rc` with a kernel per thread

A-C keep every value inside one thread. D makes the environment shareable: one environment,
many threads reading it, as Lean and Isabelle have.

**What it would buy:** no replay and no duplicate memory per worker; B1 (blocking on a
pending proof); component-level parallelism within a namespace.

**What it costs.** `Rc` to `Arc` at about 1,640 sites and every `Cell`/`RefCell` on a shared
path (a glued call's unfolding is computed once and "then shared by every copy": that is a
write through a shared pointer) to a lock or an atomic. "Unlike `Rc<T>`, `Arc<T>` uses atomic
operations for its reference counting ... atomic operations are more expensive than ordinary
memory accesses" [W2] **[verified]**, and value clones, drops and allocation are already
27-31% of the checking profile **[measured, SW-4608]**, so every single-threaded check would
slow down: by how much is unknown; 10-30% is my guess **[estimated, unmeasured]**. It is a
rewrite of the kernel's evaluator's memory model: Opus work with a Fable review, weeks of
agent time, and it competes with the allocation work SW-4608 proposed (item 5) for the same
code.

**A middle form:** share only *terms* and declarations (immutable after admission) behind
`Arc`, and keep *values* per thread in `Rc`, each thread evaluating shared terms into its own
values and keeping its own caches. Sharing would then cost atomics only on terms, not in the
evaluator's inner loop. It removes replay and most duplicate memory, but `Def` holds a
`ty_value: Value` and caches hold values, so the split is real work too. Not sized.

**Recommendation on D:** not now. A needs none of it; decide D only if A's measured replay
and memory costs hurt, or if B1 is wanted.

### Comparison

| | A: namespaces, threads | B: proof bodies | C: processes | D: shared values |
|---|---|---|---|---|
| Kernel or language change | none | yes (B2) or needs D (B1) | none | evaluator's memory model |
| Soundness rests on | check cache's contract (I3) | Lemma B by rule or by blocking | as A | thread-safety of the evaluator |
| `tools/fmt` cold, estimate | 2.2-2.5x (stale weights) | up to ~8x bound with A; 4-6x likely | below A (replay per process) | enables B1; itself 1x or slower |
| Whole AoC cold | near workers | little more | as A, less | - |
| Memory | workers × (closure + peak) | as A, or shared with D | as A | one environment |
| Editor / playground | fits; playground later via workers | editor benefits most | neither | threads only with isolation headers |
| Size | medium | large | small as a script | very large |
| Risk | latent order/closure dependence | acceptance changes | low | high |

## 5. Recommendation

**[superseded by section 8.4]** Kept for the record: its measurements were run (the two
addenda below, and SW-4645's count), and its item 3 was decided as D3722.

1. **Measure first (no compiler change, two background jobs for the verifier or Overmind):**
   - Rerun `check --no-cache --timings=all` of `tools/fmt` on today's `main`, parse the unit
     table as SW-4608 did, and run `ns_graph.py` on it: today's critical path and bound. Also
     once for whole AoC, which has never been weighed.
   - A throwaway script (option C as an experiment): topologically schedule
     `stitchwort check <namespace>` processes, 4 and 6 at a time, over one fresh cache
     directory; record wall time, summed CPU, peak memory; then compare the cache entries'
     recorded hashes and all diagnostics with a sequential run's. The outcome is a real lower
     bound on the speedup (processes pay the most replay), the replay overhead, and a first
     determinism test of I1-I3. (A warm check with `STITCHWORT_SKIP_UNNEEDED=0` beside it gives
     the cost of one full replay.) Predicted from this morning's weights: about 2x at 4
     processes if replay is cheap; if it comes out near 1x, replay or memory dominates and A
     needs kept sessions to pay.
   - Optional and cheap: a counter of how often a theorem's proof is unfolded during a check
     (the three sites in `docs/core.md` line 266). Zero across `tools/fmt`, std and AoC would
     make B2 nearly free to adopt; a large number would say B needs blocking.
2. **If the numbers hold, build A** behind `check --jobs N` (default 1 until the byte-compare
   test has run clean on std, AoC and `tools/fmt` for a while): design note for the scheduler,
   the order rule, error-carrying entries and the trust wording; then the build.
3. **Keep B and D as separate later questions**, B2 first as a language design note if the
   counter says it is cheap, since B is where the larger factor is and every other prover got
   there by making proofs opaque.

Independent of all this, the survey's simplest lesson applies today: the bound is set by the
slowest chain, and half of this morning's chain was one namespace holding one 32-second
proof. Speeding up or splitting the namespaces on the critical path raises the bound for any
later parallel design, and `ns_graph.py` says which they are.

## 6. Decisions for Matt

**[superseded by section 8.5]** Question 1's measurements were run; question 3 was decided
(D3722, sealed theorems); question 2 is asked again there.

1. **Direction:** pursue parallel checking now, starting with the two measurements?
   [rec: yes to the measurements; decide on building A when they are in.]
2. **Trust:** may a parallel `--no-cache` check take another worker's namespace by trusted
   replay (as every warm check does), so that `--no-cache` means "each declaration checked
   once by this build's kernel" rather than "all in one environment"? [rec: yes, with the
   byte-for-byte comparison against the sequential check kept as a standing test, and the
   sequential check still available.]
3. **Later, a language question:** should theorems be opaque to the checker (their proofs
   never unfolded unless named in `unfolding`), which every surveyed prover has in some form
   and which makes proof-level parallelism simple? [rec: no decision now; measure how often
   proofs are unfolded first.]

## 7. Sources

All read on 22 November 2026.

Lean:
- [L1] `src/Lean/AddDecl.lean`, lean4 `master`: <https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/AddDecl.lean>
- [L2] `src/Lean/Environment.lean`, lean4 `master` (Note [Environment Branches], `addConstAsync`, `AsyncContext`, `EnvExtension.AsyncMode`, `.olean` loading): <https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Environment.lean>
- [L3] `src/Lean/CoreM.lean`, lean4 `master` (`Elab.async`, `wrapAsync`, `wrapAsyncAsSnapshot`, `logSnapshotTask`): <https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/CoreM.lean>
- [L4] Lean 4.19.0 release notes: <https://lean-lang.org/doc/reference/latest/releases/v4.19.0>
- [L5] Lean 4.18.0 release notes: <https://lean-lang.org/doc/reference/latest/releases/v4.18.0>
- [L6] lean4 PR #7084, "feat: elaborate theorem bodies in parallel" (merged 14 March 2025): <https://github.com/leanprover/lean4/pull/7084>
- [L7] Lake README: <https://raw.githubusercontent.com/leanprover/lean4/master/src/lake/README.md>
- [L8] `src/lake/Lake/Build/Job/Basic.lean`: <https://raw.githubusercontent.com/leanprover/lean4/master/src/lake/Lake/Build/Job/Basic.lean>
- [L9] Zulip archive, "Lake parallel builds" (October-November 2023): <https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Lake.20parallel.20builds.html>

Rocq:
- [R1] Reference manual 9.1, "Asynchronous and Parallel Proof Processing": <https://rocq-prover.org/doc/v9.1/refman/addendum/parallel-proof-processing.html>
- [R2] Reference manual 9.1, command-line tools ("Compiled interfaces (produced using `-vos`)", `rocqchk`): <https://rocq-prover.org/doc/v9.1/refman/practical-tools/coq-commands.html>
- [R3] Reference manual 9.1, Ltac (`par:`): <https://rocq-prover.org/doc/v9.1/refman/proof-engine/ltac.html>
- [R4] Barras, Tankink, Tassi, "Asynchronous processing of Coq documents: from the kernel up to the user interface", ITP 2015: <https://arxiv.org/abs/1506.05605>
- [R5] PR #18424, "[stm] Remove support for .vio files" (merged 17 April 2024, milestone 8.20+rc1): <https://github.com/coq/coq/pull/18424>
- Barras et al., "Pervasive Parallelism in Highly-Trustable Interactive Theorem Proving Systems", CICM 2013 (the Paral-ITP project overview; abstract only): <https://arxiv.org/abs/1305.7360>

Isabelle:
- [I1] Wenzel, "Parallel Proof Checking in Isabelle/Isar", 2009 (the author's copy is dated 2009/6/30; the venue, PLMMS 2009, is from the file's metadata, not its text): <https://www21.in.tum.de/~wenzelm/papers/parallel-isabelle.pdf>
- [I2] Matthews and Wenzel, "Efficient Parallel Programming in Poly/ML and Isabelle/ML", DAMP 2010: <https://www21.in.tum.de/~wenzelm/papers/parallel-ml.pdf>
- [I3] Huch and Bode, "The Isabelle Community Benchmark", 2022: <https://arxiv.org/abs/2209.13894>

Others:
- [A1] Agda command-line options (`--parallel`, added in 2.9.0): <https://agda.readthedocs.io/en/latest/tools/command-line-options.html>
- [A2] Agda source documentation, `Agda.Interaction.Imports` (`TCWorkers`, `chaseModule`): <https://agda.github.io/agda/Agda-Interaction-Imports.html>
- [M1] metamath-knife README: <https://raw.githubusercontent.com/metamath/metamath-knife/main/README.md>
- [D1] Dafny FAQ, "Does Dafny verify methods in parallel?": <https://dafny.org/dafny/HowToFAQ/FAQParallel>
- [F1] "A new F# compiler feature: graph-based type-checking", .NET blog, November 2023: <https://devblogs.microsoft.com/dotnet/a-new-fsharp-compiler-feature-graphbased-typechecking/>
- [P1] Newton, Ağacan, Fogg, Tobin-Hochstadt, "Parallel Type-checking with Haskell using Saturating LVars and Stream Generators", PPoPP 2016: <https://ppopp16.sigplan.org/details/PPoPP-2016-papers/13/Parallel-Type-checking-with-Haskell-using-Saturating-LVars-and-Stream-Generators->
- [W1] MDN, `SharedArrayBuffer`, "Security requirements": <https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/SharedArrayBuffer>
- [W2] Rust standard library, `std::sync::Arc`: <https://doc.rust-lang.org/std/sync/struct.Arc.html>

### What I could not verify

- That Lake runs module jobs concurrently, from Lake's own documentation (only from users'
  reports [L9]); and any official speedup figure for Lean's `Elab.async`.
- Lean's kernel never unfolding theorems, and its reference counting being atomic only for
  shared objects (both from memory).
- Rocq: how universe constraints of delegated proofs are handled inside the kernel (the 2015
  paper as I read it doesn't say; the manual only says they are checked late); the default of
  `-async-proofs-tac-j`; that plain `.vo` builds parallelise with `make -j` (not looked up).
- Isabelle: Wenzel's ITP 2013 paper (abstract summary only); the venue of [I1].
- F\*, Idris 2, HOL4, HOL Light: nothing primary found.
- Dafny's current `--cores` default; the PPoPP 2016 paper's text (listing only).
- In Stitchwort: I6 (whether a component's step count can depend on session history), I2
  (whether any result depends on the order unrelated namespaces were loaded), how often a
  theorem's proof is unfolded during checking, and whether today's 138 s check has the same
  critical path as this morning's 252 s one. `ns_graph.py`'s edges are rebuilt from text and
  were not compared with the compiler's own.

## Addendum: fresh timings (22 Nov, evening; measured by the orchestrator)

A cold `check --no-cache --timings=all` of `tools/fmt` on `main` after SW-4637 (146 s wall, release build, nice 19, load about 6), fed to `ns_graph.py` (unit table in `parallel-checking/fmt-units-22nov-pm.csv`): library and core 16.8 s, project 127.9 s, critical path 41.6 s over 20 namespaces, bound 3.07x on the project. With the library first on one core: 4 workers 2.22x, 6 workers 2.40x, 10 workers 2.47x (estimated from the unit times, not run).

Half the critical path is one namespace, `Syntax.ReadBackHungTop` (20.4 s), and nearly all of that is two example theorems checked by computation in the kernel: `readsBackHungListExample` (12.4 s, 147M steps, 12.2 s kernel) and `readsBackHungSignExample` (7.6 s, 95M steps). Making those cheaper (SW-4647) shortens the critical path to about 21 s, raising the project bound to about 6x.

## Addendum: first measured run, processes (22 Nov, evening; orchestrator, SW-4644's par_check.py)

All 150 `tools/fmt` namespaces as separate `stitchwort check` processes over one cache, in dependency order, after one `check --std Std` fill (22 s, not counted below), on `main` after SW-4647 and SW-1803; release build, nice 10, load about 3 at the start. Logs in `parallel-checking/runs/`.

| | wall | sum of process times | namespaces' own time | reloading overhead |
|---|---|---|---|---|
| sequential, one process | 111 s | | | |
| 4 processes | 103 s (1.08x) | 329 s | 96 s | 233 s (1.6 s a process on average, up to 3.5 s) |
| 6 processes | 101 s (1.10x) | 429 s | 130 s | 299 s |

The parallel run's diagnostics and all 258 cache entries were byte for byte the same as the sequential run's (4 processes, `--compare`): the check cache's results don't depend on order or process, as section 2 assumed. But processes gain almost nothing: each one reloads every namespace it depends on from the cache, which costs more than most namespaces' own checking (median well under a second), and at 6 processes even the own time rises (contention for memory bandwidth and cores). Peak memory per process was up to 1.1 GB.

So option (c), processes, is ruled out as the way to get the speedup, and option (a) only pays if workers don't each reload the world: threads in one process sharing what's already loaded (an immutable, shareable environment, Lean's approach), or a much cheaper load. The bound with that overhead removed is the 3x to 6x estimated above. This makes the `Rc` question (option d) and replay cost (SW-4645) the next things to understand.

## 8. After proof irrelevance (SW-4715, 24 November 2026)

Fable paper lane, asked for by D3729. The code was read at `fda6878dd`; nothing was built, and
no check was run. Marks as at the top of the note; **[verified]** here means read today at the
file and line given. The gains are **[static]** (from `fmt-units-22nov-pm.csv`, taken before
SW-4647 shortened the slowest namespace, so stale in the same way as before) or
**[estimated]**; `parallel-checking/measure_shares.sh` gives today's figures and is written
for the orchestrator to run (**not run by this lane**: it is a whole-project check).

### Summary

**The problem.** A cold check of `tools/fmt` is one thread for about two minutes. The first
note found the one trick every other prover uses, "what comes later needs only a theorem's
statement", was false here, and the first measured run showed separate processes gain nothing
(1.08x), because each one loads everything below it again.

**What changed.** The trick is true now. A theorem's proof is never unfolded while anything is
checked, a reference to a theorem hashes as its statement, and a namespace's cache key covers
the *interface* of what it depends on, not the proofs. So a namespace can be checked against
its dependencies' statements, and whether their proofs have been checked yet can't change the
result.

**The plan, in three stages**, each on threads with one session per worker, values left as
`Rc`:

1. **Namespaces in parallel** (option A, as before): `check --jobs N`. Workers keep their
   sessions, so each loads a namespace at most once, not once per namespace as the processes
   did. Estimate for `tools/fmt` cold: **2.2x to 2.5x** with the library cold, up to 3x with
   it cached **[static]**; whole AoC close to the number of workers **[estimated]**.
2. **Load only interfaces.** A worker that needs a dependency loads its statements and
   definitions and leaves its proofs out: less to load and less memory per worker
   **[estimated; the share of an entry that is proofs is not measured]**.
3. **Statements first.** Each namespace publishes its interface (everything but its proofs)
   as soon as that is checked; the namespaces above start from it, and every namespace's
   proofs are then checked side by side. The chain that limits stage 1 then carries only
   statements and definitions. Estimate for `tools/fmt` cold on 8 workers: **2.6x to 3.6x**
   with the library cold, **3.3x to 5.5x** on the project part **[estimated from static
   figures; the spread is the unknown share of time that isn't proofs]**.

Proofs *inside* one namespace on several workers, and shared (`Arc`) values, stay out: the
first buys little once stage 3 is in (it only lowers the floor set by the largest namespace),
and the second is still a rewrite of the evaluator's memory.

**For Matt:** the end state (stage 3, with `Rc` kept); the trust change stage 1 makes to
`--no-cache`; and the trust change stage 3 makes (a theorem is used before its own proof has
been checked, and the run is only "checked" when every proof has passed). Section 8.5.

### 8.1 What proof irrelevance and digests changed

**Gone:**

| Obstacle in the first note | Now | Evidence |
|---|---|---|
| A later declaration can unfold a theorem's proof (`J`, `case`, comparison); Lemma B held only "if the check never unfolds it" | A call of anything whose type is a proposition never unfolds while checking (rule F), and no `unfolding` list may name a theorem, so there is no opt-out. Lemma B holds for every theorem, with no condition | **[verified]** `value::frozen`, `crates/core/src/value.rs:3435`; every unfolding goes through `body_seen`, `:3453`, which returns nothing for a frozen definition; `docs/core.md:174` (rule 6) and `:284` (rule F). Before sealing, SW-4645 counted 63,049 such unfoldings in a `tools/fmt` check **[measured, merge `fc5932786`]**; the counters went with the code they counted (`f0af26180`) |
| Comparing two proofs looks inside them | Two values marked as proofs are equal and nothing inside either is read (rule I), before anything else in conversion | **[verified]** `value::by_rule_i`, `value.rs:4534`; `docs/core.md` "Proof irrelevance" |
| A user's hash covers the theorem's proof, so a hash asked for while elaborating would have to wait for the proof | A reference to a final theorem with a proof hashes as the tag `theorem` and its statement | **[verified]** `hash::has_interface` and `interface_hash`, `crates/core/src/hash.rs:235-256`; `docs/core.md:571` |
| Facts read off a proof's body and kept on the theorem (inert proof parameters) | Proof parameters are read off the type's marks; "no list of positions, no inert analysis" | **[verified in the spec]** `docs/core.md`, "Proof irrelevance"; kernel code not re-read |
| A namespace's cache key covers everything below it, proofs included | The key covers each dependency's *interface digest*: its entry less sealed proofs, positions and its own messages. An edited proof re-checks 1 namespace, not 54 (31.0 s to 5.3 s) | **[measured by the orchestrator, 23 Nov]** `interface-digest-cache.md`, "As built (stage A)" |
| Whether results depend on which process or order checked a namespace | 258 entries byte for byte the same between a sequential check and four processes | **[measured]** the 22 Nov addendum above |

**Still there:**

- **Values are `Rc`; nothing in a session can cross a thread.** 1,774 uses of `Rc`, 375 of
  `Cell`/`RefCell`, 33 of `Arc` in `crates/core/src` and `crates/elab/src` today (1,640, 290
  and 33 on 22 Nov) **[verified, grep]**. The cache store is handed to a session as
  `Rc<dyn Store>` (`crates/elab/src/cache/mod.rs:412`; the trait, `:123`). So every design
  below keeps one session per thread, and what crosses threads is bytes: entries.
- **A dependency has to be loaded into each session that uses it.** This is what sank the
  process run: 233 of 329 CPU-seconds were loading **[measured, addendum]**. It is a cost of
  starting each namespace from an empty session, not of sessions as such: a worker that keeps
  its session loads each namespace at most once (section 8.3, A).
- **The kernel has no form for "a theorem whose proof is elsewhere".** Trusted replay admits
  a statement (`check::admit_trusted_def`, `crates/core/src/check.rs:4085`) and then installs
  the bodies (`admit_trusted_group`, `:4114`); between the two the theorem is pending, and
  nothing may refer to a pending declaration. The nearest existing form is the assumption
  (`check::assume`, `:3054`), which is final at once and never unfolds, but it hashes by its
  own tag and label, so a user's hash would differ from the one it has once the proof is
  there (`has_interface` asks for `body.is_some()` and no assumption, `hash.rs:237`). Stages
  2 and 3 need this form: a small kernel addition, and a trust decision (8.5).
- **The elaborator asks "does it have a body?" in seven places** (`reading.rs:1886`,
  `auto.rs:1547`, `module.rs:3219`, `interfaces.rs:1029` and `:1300`, `opaque.rs:467`,
  `rewrite/repeatedly.rs:1745`) **[verified, grep; I read the first three]**. `auto_eligible`
  (`module.rs:3218`) reads a missing body as "not finished checking", so a theorem admitted
  without its proof would silently stop being a candidate. The new form must answer these as
  a finished theorem does.
- **Session state that isn't in an entry.** `Session` (`crates/elab/src/state/session.rs:26-144`)
  is as the digest note lists it: the project's namespace list and `project_names` (from
  syntax, set whole), `library_reach` (rebuilt from entries' needs), and `derive_waiting`
  (not cached, an accepted stale note). Its `Cell`s and `RefCell`s (`instance_waits`,
  `blocked`, `paths`) are per-session working state. Nothing here is new since the digest
  note's section 2.2 **[verified by reading the struct]**.
- **A namespace's library files are found from its syntax before any declaration is
  checked** (`dependencies`, then `set_library_reach`, `crates/elab/src/module.rs:461-462`),
  so which proof is elaborated first can't change which instances are in reach
  **[verified for the reach; not verified that no library file is ever loaded later, during
  a body]**.
- **What a proof leaves behind.** A `match` or local definition in a proof becomes a helper
  declaration with rows in `lifted`, `match_columns` and `helper_keys`
  (`state/tables.rs:51`, `:80`, `:131`); 4,996 such helpers in `tools/fmt`, a third of its
  theorems owning one **[measured/estimated, digest note "As built"]**. Until the cache's
  stage C (SW-4713) defines them as proof-private, they are part of a namespace's interface
  digest, so the interface isn't known until the proofs are done. **Stage 3 depends on stage
  C.**
- **Error messages can depend on everything loaded**, not only on what a namespace uses
  (`E-UNKNOWN-FIELD` "names the namespace that would add a missing function";
  `crates/driver/src/project.rs:312-318`, which is why a plain `check` that left namespaces
  out starts again, loading all, when one has an error or a goal) **[verified]**. So
  invariant I1 holds for clean namespaces only. A parallel check does what that code does:
  on any error or open goal it reports from a sequential check (8.3).
- **Step counts depend on history.** "The steps a declaration's check takes can depend on
  which earlier check already forced a call in a kept type, so on whether those were checked
  or replayed from the cache. Results don't" (`docs/core.md:272`) **[verified in the spec]**.
  That settles invariant I6, the one the first note could not: step counts are *not* a
  function of the declaration alone, so a declaration within a few steps of its limit could
  pass under one schedule and run out under another. This is already so between a cold and a
  warm check. It can't make a wrong result accepted; it can make a run fail with
  `E-RESOURCE` that another would pass. `--timings` step totals will differ between
  schedules for the same reason.
- **Reliance (open goals, axioms) is a walk over proofs** in the live session
  (`assumption::relied_on`). A session that left proofs out can't do it. In the plan below
  only complete sessions report reliance: a parallel check falls back to a sequential one
  when there is a goal, and `axioms` and `audit` load everything, as now.
- **Only theorems are sealed for hashing.** A `def` whose type is a proposition is frozen by
  rule F too, but `has_interface` asks for `def.theorem` (`hash.rs:237`), so such a
  definition's body is still part of its users' hashes and of the digest **[verified]**.
  It costs cut-off, not correctness.
- **The editor** rewinds to the first changed namespace and checks one namespace per step
  (`crates/driver/src/live.rs:1-18`); within a namespace everything after an edit is checked
  again. Unchanged; 8.3 says where each option touches it.
- **The playground** is one thread of wasm. Unchanged, and not a target.

### 8.2 The formal picture now

Lemma B without its condition:

> **Lemma B′ (sealing).** Let `d` be a theorem with statement `T`, and let `Σ, d` and
> `Σ, d°` be the environment with `d` proved and with `d°`: the same name, path and
> statement, marked a proof, final, with no body, and hashed as `d`'s interface hash. Then
> elaborating and checking any later declaration `e` gives the same terms, hashes and
> verdict after either, provided the elaborator's own readers treat `d°` as a finished
> theorem (the seven body tests of 8.1).

Why: evaluation never unfolds `d` (rule F reads `Def::proof`, which is set from the type);
conversion never looks inside a call of `d` (rule I reads marks); rules K and S compute from
a cast's ends or a proposition's shape and never from the proof (`docs/core.md`, "Rules K and
S"); `e`'s hash reads `d`'s interface hash. What still reads `d`'s body is outside checking:
running a program (erased first), the reliance walk, `axioms`, `audit`, `--timings` sizes,
and one error note (`equation_notes.rs:207`, digest note 2.1). **[argued from the verified
facts above; the kernel was audited for "nothing reads a sealed proof" by SW-4700's review,
not by this lane]**

A stand-in (the assumption that replaces a theorem whose proof failed) differs from `d°`
only in its hash and its label. So if `d`'s proof later fails, what was checked against `d°`
was checked correctly *as terms*, but its hashes and its "finished" status are wrong, and it
has to be reported as relying on a failed declaration. The plan below does not try to patch
that up: a failed proof sends the run to the sequential check.

The theorems of section 2.4 become:

> **Namespace-level (stage 1).** As before: given I1 to I5 and I7 for clean namespaces, any
> schedule that checks each namespace in a session holding its closure gives the entries and
> messages of the sequential check.

> **Statements first (stage 3).** Let `iface(N)` be the entry of `N` less its sealed proofs
> and what only they reach (the cache's stage C definition). Suppose every namespace `N` is
> checked in full in some session that holds `iface(D)` for each `D` in its closure, that
> the check has no error and no open goal, and that the interface each of those sessions
> computes for `N` has the digest of the `iface(N)` the others were given. Then every
> declaration is the one a sequential check makes, and every proof has been accepted by the
> kernel against true statements.

Proof sketch: by induction up the namespace order. `N`'s session differs from the sequential
one only in holding `d°` for `d` (Lemma B′) and in lacking proof-private helpers, which
nothing outside their proof can reach (stage C's definition, the digest note's P1). So `N`'s
check produces the sequential entry. The digest test closes the loop: the interface the
others relied on *is* the one `N`'s full check produced. No cycle is possible: a proof in `N`
can only use statements from `N`'s own sequential prefix (its own session checks `N` in the
usual order) and from namespaces below it.

That last point is what a within-namespace design has to arrange by hand. If the proofs of
one namespace were checked in a session holding *all* of that namespace's statements, a
tactic could pick up a later theorem (`auto` limits itself to declarations "declared above",
`module.rs:3218-3224`, by position; a scan such as `reading.rs:1882-1889` goes over
every definition in the environment), and two proofs could each use the other. Lean and
Isabelle avoid this by giving each proof the environment as it stood at its statement. With
`Rc` sessions that means a worker walking the namespace forward, replaying statements and
elaborating only its share of the proofs.

### 8.3 The options again

Figures use the 22 Nov evening table: library and core 16.8 s, project 127.9 s, critical
path 41.6 s, largest namespace 20.4 s (`Syntax.ReadBackHungTop`, since cut by SW-4647; the
next is 8.5 s) **[measured then; static below]**.

#### A. Namespaces in parallel, sessions kept (stage 1)

*What it is.* The first note's option A, with the measured lesson applied: workers are
threads that each keep one session for the whole run. A worker given namespace `N` loads
whatever of `N`'s closure its session lacks (from the entries other workers published),
checks `N`, and publishes `N`'s entry. With the cache on, entries go through the store as
now; with `--no-cache`, through an in-memory map for the run. Keys need each dependency's
digest, which is in the entry's header and is known when the dependency finishes, which is
when `N` becomes ready anyway (digest note, section 5). The sweeps already run sessions on
threads this way (`par_map_sessions`, `crates/driver/src/driver.rs:128`).

*Errors and goals.* If any namespace reports an error or an open goal, the parallel run
stops handing out work and the driver runs the ordinary sequential check, which replays the
clean entries just written and re-checks the rest. So every message a user sees in a failing
run comes from the sequential code, and I1's weakness for errors (8.1) doesn't arise. Cost:
a failing run is no faster than now, except for what the cache kept. `tools/fmt` sets
`open-goals: warn`, so while it has a `?` it gets no gain; stage D of the digest cache is
what would change that.

*Why the result equals a sequential check.* The namespace-level theorem. I3 (replay equals
elaboration) is the cache's contract. I2 (order within the closure) is leaned on more than
by the process run: a kept session receives namespaces in the order its work arrived, not in
canonical order. Evidence that this is safe: a plain `check` already replays entries into
sessions that skipped other namespaces (the digest note's P4), and the editor loads the
edited namespace last (`project.rs:559`). The standing test is the one the process run used:
every entry and every message byte for byte against the sequential check.

*Gain.* `tools/fmt` cold **[static]**: 4 workers 2.22x, 6 workers 2.40x, 10 workers 2.47x
with the library checked first on one core; 2.64x, 2.93x, 3.07x on the project part (library
cached). Less the loading: each worker loads each namespace at most once, so at most one
whole-project replay per worker (2 to 4 s and 0.7 to 1.3 GB each **[measured for one
replay]**), in parallel, against the 233 s the processes paid **[estimated; stage 1's first
measurement]**. Since SW-4647 the critical path is shorter (the addendum estimated about 21 s
and a bound near 6x **[estimated then; not re-measured]**), so today's figure is probably
better than these. Whole AoC: 291 namespaces, depth 5, 106 on one level, so close to the
worker count once the library is loaded **[estimated; never weighed]**. That is the check
Overmind runs on every push.

*Cost and risk.* Driver work: a scheduler, a store usable from several threads, merged
reports, `--timings` and progress per worker, cancellation. No kernel or evaluator change.
Memory: up to workers × (0.7 to 1.3 GB plus the working peak), so 8 workers may hold 6 to
10 GB **[estimated]**; the worker count needs a memory cap as well as a core cap, and lanes
sharing the machine count against it. Risk: I2 false somewhere; found by the byte-compare
test, and each such case is also a latent cache bug today.

*Trust.* As the first note said: `--no-cache` would mean "every declaration was checked once
by this build's kernel, and moved between sessions in the cache's encoding", not "one kernel
saw everything in one environment". Decision 2 in 8.5.

#### N1. Load only interfaces (stage 2)

*What it is.* When a worker loads a dependency, it admits each sealed theorem by its
statement and skips the proof, using the new kernel form `d°` of Lemma B′. The entry's layout
marks which bodies are sealed (the digest pass already knows: it is the same predicate,
`has_interface`); after the cache's stage C the proof-private helpers are skipped too.

*Why the result is the same.* Lemma B′, for a dependency whose proofs *have* been checked (by
the worker that published the entry). Nothing unproved is used: this stage changes what a
session holds, not what has been checked.

*Gain.* Lower loading time and memory per worker, by the share of an entry that is sealed
proofs and their helpers **[not measured; probably most of it, since at least 60% of the
checking time is proofs]**. It also helps every warm check and the editor's start-up, which
replay the same entries. No change to the bounds of A.

*Cost and risk.* The kernel form (small: an admission with no body that is final and hashes
as the interface), the seven body tests, and a rule for who may load this way: any session
that will report reliance, run a program, or answer `axioms` or `audit` must load proofs.
The risk is a reader of proofs that was missed, which would report "no axioms" or "finished"
from a session without the proofs. This needs its own short design note and a Fable review,
since it is the trusted base.

#### N2. Statements first, proofs side by side (stage 3)

*What it is.* Rocq's `.vos` then `.vok`, and Cargo's pipelined builds, at namespace level.
Two kinds of work per namespace:

- an **interface pass**: check `N` leaving out each sealed theorem's proof (admit `d°`
  instead), against the interfaces below; publish `iface(N)` with its digest;
- a **full check**: check `N` as today, proofs included, against the interfaces below;
  publish the entry; compare its interface digest with the interface pass's.

The interface passes follow the namespace graph (through stage 1's scheduler); a full check
needs only the interface passes of its closure, so the 150 full checks are independent of
each other. The run is "checked" when every full check has passed and every digest matched.
A proof failure, an open goal or a digest mismatch sends the run to the sequential check, as
in A.

*Why the result is the same.* The statements-first theorem of 8.2. The digest comparison is
the join: it is what Isabelle's "all promises fulfilled" and Rocq's "then build the `.vo`"
are, done per namespace with a check that already exists (`--recheck` recomputes digests).

*Gain.* Wall time is about `L + I + max((P + I_cpu)/W, biggest namespace)`: the library
`L`, the interface passes along their chain `I`, then all the work spread over `W` workers.
The unknown is how much of the time is not proofs. The first note's figure is "at least 60%
is proofs"; `interface_share.py` on the old top-200 table gives 93% proofs for those 200
declarations **[static; the other 12,900 declarations are not in any table]**. Taking 7% to
40% as the range for the rest, with `P` = 127.9 s, 8 workers and the interface chain at the
same share of the 41.6 s critical path: `I` is 3 to 17 s, and the work spread over the
workers is 17 to 22 s, against a floor of 20.4 s from the largest namespace as it was then.
So the project part is 23 to 39 s, **3.3x to 5.5x**, and the whole cold check 40 to 56 s of
144.7 s, **2.6x to 3.6x** **[estimated]**. The library block is then a third of the run; it is normally cached, and
checking it in parallel is the same problem again one level down (its files have static
edges from the index, digest note 1.5). On AoC: nothing beyond A; its graph is already flat.

What the figures don't show: stage 1's bound falls as a project's chain grows (`tools/fmt`
is 25 levels deep and each proof slice adds to the chain), while stage 3's does not, because
proofs are off the chain wherever they sit. And on a re-check after a statement low down has
changed, everything above it is checked side by side.

*Cost and risk.* Statements and definitions are elaborated twice (once in each pass), as
Rocq's are; that is the `I_cpu` above. It needs stage 1's scheduler, N1's kernel form (now
used for theorems whose proofs have *not* yet been checked), and the cache's stage C, so
that proof helpers aren't part of the interface. Risk: an interface pass that differs from
the full check's interface. The digest comparison catches every such case as a mismatch,
loudly, at the cost of a sequential re-run; it can't be a silently wrong result unless the
digest itself leaves out something a dependant reads, which is the digest cache's own risk
(its section 2.4), not a new one.

*Trust.* For the length of a run, sessions hold theorems nobody has proved yet. Nothing is
reported as checked until the join. Decision 3 in 8.5.

#### B. Proofs of one namespace on several workers

*What it is.* After N2, the floor is the largest namespace's full check. B splits that: each
worker walks the namespace forward, replays the interface pass's declarations, and
elaborates only its share of the proofs, so each proof sees exactly the declarations before
it (8.2's last paragraph).

*Gain.* It lowers the floor from the largest namespace (20.4 s then, 8.5 s for the next) to
the largest single proof. With 8 workers the proofs phase is about 16 s anyway, so on
`tools/fmt` today this buys little **[estimated]**. The same machinery is what would let the
editor re-check only the proof being edited instead of the rest of its namespace (digest
note, section 4).

*Cost and risk.* Per-declaration records in entries, forward-only replay in workers, an
audit that everything a proof leaves behind is private, and messages merged in source order.
Larger than N2 and with more ways to differ from the sequential check.

*Recommendation.* Not now. Splitting an oversized proof namespace gets the same effect with
no compiler work; revisit B for the editor.

#### C. Worker processes

Ruled out by measurement (1.08x at 4 processes, 1.10x at 6; addendum). Unchanged.

#### D. Shared (`Arc`) values

Unchanged: a rewrite of the evaluator's memory model, now 1,774 `Rc` sites, with an unknown
slowdown of every single-threaded check. Proof irrelevance removed the one thing D was
needed *for* in the first note (B1, blocking on a proof someone unfolds: nothing unfolds a
proof now). What D would still buy is no loading and no duplicate memory per worker; N1 goes
after the same cost far more cheaply. Not recommended.

#### Comparison

| | A (stage 1) | N1 (stage 2) | N2 (stage 3) | B | D |
|---|---|---|---|---|---|
| What runs side by side | namespaces, along the graph | as A | interfaces along the graph; all proofs | proofs within a namespace too | anything |
| `tools/fmt` cold, library cold | 2.2x to 2.5x **[static]** | as A, less loading | 2.6x to 3.6x **[estimated]** | little more on 8 workers | not sized |
| Project part (library cached) | 2.6x to 3.1x **[static]** | as A | 3.3x to 5.5x **[estimated]** | cores-limited | |
| Whole AoC | near workers **[estimated]** | as A | as A | as A | |
| Result equals sequential because | cache contract, I2 | Lemma B′ | Lemma B′, digest join | B′, prefix rule | thread-safe evaluator |
| Kernel or evaluator change | none | one admission form | same form | same form | memory model |
| New trust | entries between sessions under `--no-cache` | sessions without proofs must not report reliance | theorems used before their proofs are checked; verdict at the join | as N2 | |
| Needs first | nothing | a short design and review | stage 1, N1, cache stage C | N2 | |
| Size | medium | small to medium | medium | large | very large |

### 8.4 Recommended end state and build plan

**End state:** stage 3. One process, a session per worker thread, `Rc` values; workers load
interfaces; each namespace's interface is published before its proofs are checked; a run is
checked when every proof has passed and every interface digest matched; any error, goal or
mismatch is reported by the sequential check. B and D stay out unless the editor (B) or
measured loading costs (D) call for them.

**Measure first** (the orchestrator; one script, about 5 minutes of machine time for
`tools/fmt` going by the 111 to 146 s cold checks above):

    docs/proposals/parallel-checking/measure_shares.sh target/release/stitchwort tools/fmt OUT crates/elab/src/std

and the same for `aoc` (never weighed; expect several minutes). How to read it:

- *Part 1, "bound":* what stage 1 can give on the project part. If it is under about 2x for
  `tools/fmt`, stage 1 is worth building for AoC and Overmind alone, and stage 3 matters
  more.
- *Part 2, "the rest":* the share that is not proofs, a lower bound on the interface pass.
  Under about 20%: stage 3's upper figures apply. Over about 40%: stage 3 adds little over
  stage 1 and should wait.
- *Part 3:* seconds and memory for one worker to hold the whole project; times the worker
  count, it is stage 1's loading cost and memory at worst.

The script was syntax-checked only; `interface_share.py` was run on the old top-200 table
(169 of the 200 are theorems under today's names, 93% of their time; the first note's hand
count was 188 and 97%, and the difference is declarations renamed since).

**Stages** (estimates in agent time, set from SW-4701's 32 minutes and SW-4707's brief of 90
for comparable Opus work; **[estimated]**):

| Stage | What | Measure when done | Who, estimate |
|---|---|---|---|
| 1a | `check --jobs N`, cache on: scheduler over the namespace graph, kept sessions on threads, a store usable across threads, messages in canonical order, fall back to the sequential check on any error or goal. Default stays 1 | `tools/fmt` and whole AoC, cold library cached, 4 and 8 jobs: wall time, peak memory, and every entry and message byte for byte against `--jobs 1`. Prediction: 2.6x to 3.1x on `tools/fmt`'s project part **[static]** | Opus, 90 min; Fable review of the driver's trust wording, 30 min |
| 1b | `--no-cache` through an in-memory map; `--timings`, progress and cancellation merged; the byte-compare as a standing test on a small project | the same, with `--no-cache` | Opus or Sonnet, 60 min |
| 2 | Design note for the "theorem whose proof is elsewhere" form and interface-only loading (who may load without proofs), reviewed; then the build | loading time and memory per worker before and after | Fable paper 40 min; Opus 90 min; Fable review |
| 3 | Interface pass and digest join, after the cache's stage C (SW-4713) is built | as 1a; prediction 3.3x to 5.5x on the project part **[estimated]** | Fable paper 40 min; Opus 120 min; Fable review |

Stage 1 changes no kernel code and can start once Matt has answered decisions 1 and 2.
Stages 2 and 3 each start with a note of their own, because they change what the trusted
base holds; this note is not that design.

**Orchestrator's calls, not Matt's** (noted so they aren't lost): `--jobs` defaults to 1
until the byte-compare has been clean for a while on std, AoC and `tools/fmt`; the default
worker count is capped by memory as well as cores; a failing run falls back to the
sequential check.

### 8.5 Decisions for Matt

The orchestrator numbers these.

1. **The end state: statements first, on threads, without shared values.**
   *The problem:* a cold check uses one core of ten, and checking namespaces side by side is
   limited by the longest chain of namespaces, which in `tools/fmt` is long and gets longer
   with every slice of proofs.
   *The change:* build towards stage 3: each namespace's statements and definitions are
   checked first and published, and all the proofs are then checked side by side against
   them. Values stay as they are (`Rc`); no rewrite of the evaluator.
   *What it should do:* a cold `tools/fmt` check about 3 to 5 times faster on the project
   part, and whole AoC close to the number of workers **[estimated]**; stage 1 alone gives
   about 2.5 to 3 times **[static]**.
   **[rec: yes to the end state; build stage 1 now and decide stage 3 when stage 1 and the
   script's "the rest" figure are in]**

2. **Trust, stage 1: what `--no-cache` means.**
   *The problem:* today `check --no-cache` means one kernel saw every declaration in one
   environment. Workers can't share an environment, so each takes the others' results in the
   cache's encoding, unchecked, as every warm check does.
   *The change:* a parallel `--no-cache` means "each declaration was checked once by this
   build's kernel; results moved between workers as cache entries". `--jobs 1` keeps today's
   meaning.
   *What it should do:* nothing visible unless the cache's encoding has a bug, in which case
   a parallel check could accept what a sequential one refuses. The guard is a standing test
   that compares every entry and message with the sequential check, and Overmind's rolling
   check staying on `--jobs 1`.
   **[rec: yes, with both guards]**

3. **Trust, stage 3: using a theorem before its proof has been checked.**
   *The problem:* to check proofs side by side, a namespace has to be checked against
   theorems below it whose proofs are still running, or haven't started.
   *The change:* the kernel gets one new kind of entry, "this statement, proof to follow",
   which behaves exactly as a proved theorem does to everything that uses it (nothing can
   look inside a proof any more, so nothing can tell the difference). The run reports
   "checked" only after every proof has passed and each namespace's interface has been
   confirmed against the one the others used; if any proof fails, the whole run is reported
   by the ordinary sequential check.
   *What it should do:* make stage 3 possible. The risk is a report of "checked" that didn't
   wait for a proof. Every other prover that checks proofs in parallel has this same form
   (Isabelle's promises, Lean's tasks, Rocq's `.vos`), and Rocq's version is the one known
   to have needed a full re-check to be trusted (section 1.2).
   **[rec: yes in principle, as the end state needs it; the exact form gets its own design
   note and Fable review before any build (stage 2), and that note comes back to you]**

### 8.6 What I could not verify

- Any gain: nothing was run. Today's namespace times, the share of time that isn't proofs,
  whole-AoC times and the cost of one full load are all for `measure_shares.sh`.
- That a kept session gives the same entries when its dependencies arrive in a non-canonical
  order (I2). Supported by P4 and the editor; tested only by stage 1's byte-compare.
- That nothing but the seven body tests distinguishes a theorem with no body from a proved
  one in the elaborator, and the kernel half of Lemma B′ in `crates/core` (taken from the
  spec and SW-4700's review).
- That no library file is loaded during a body's elaboration, after the up-front loads.
- How much of an entry's bytes and load time is sealed proofs (N1's gain).
- Whether `measure_shares.sh` runs as written: its check command (`check --no-cache
  --timings=all` from the project folder, with `STITCHWORT_STEP_PHASES=1` for
  `parse_timings.py`) is taken from `docs/workflow.md` and the parser's header, not tried.
- Whether Matt answered the first note's trust question (section 6, question 2); it is asked
  again as decision 2.

### Measured 24 Nov 2026 (orchestrator, measure_shares.sh, main at stage A; machine shared with lanes, so times are indicative, shares firmer)

- tools/fmt: theorems 77.6% of declaration time (84.7 of 109.1 s), the rest 22.4%; largest theorem 3.8 s; namespace-level bound 2.5x on the project part (2.1x with the library block first, which is about 16 s); one full load from the cache 4.8 s, 1.2 GB.
- aoc: theorems 67.1%, the rest 32.9%; namespace-level 5.9x on 8 workers for the project part (2.7x with the library block first); one full load 4.8 s, 0.7 GB.
- So "the rest" is under the 40% line in section 8: stage 3 stays worth planning. The library block becomes the next limit. Raw output: [measured-2026-11-24/shares.txt](parallel-checking/measured-2026-11-24/shares.txt).

## 9. Stage 1 design (SW-4718)

Fable paper lane, after D3730 ("yes, proceed": the end state is stage 3, build stage 1 now).
The code was read at `d0cdc7e88`; nothing was built and no check was run. Marks: **[verified]**
read today at the file and line given; **[measured]** by an earlier run, cited;
**[estimated]**; **[not verified]**. It is designed for "yes" to D3731 (a parallel
`--no-cache` moves results between workers as cache entries); 9.6 says what a "no" changes,
which is little. The cache's stage C (SW-4714) is being built in `crates/elab/src/cache/mod.rs`;
this design calls that file's existing entry points and changes none of them.

### 9.1 The design in one paragraph

`check --jobs N` is **a parallel fill of the check cache, followed by today's check,
unchanged**. Workers are threads, each with its own session; a worker given a namespace
replays what it lacks of the namespace's dependencies from the cache, checks the namespace,
and its entry is written by the code that writes it today. When no more namespaces can be
filled, the main thread runs the ordinary sequential project check over the same store. That
last pass finds an entry for every namespace that was clean, so it reports them from their
entries (a plain `check` doesn't even load them), and it checks for itself whatever the
workers could not write: anything with an error, an open goal or a syntax error, and
everything that uses one. With `--no-cache` the store is a map in memory that lives for the
run, and the disk cache is neither read nor written.

So everything the user sees (messages, their order, the summary line, the exit code) is
produced by the code that produces it today, and "parallel equals sequential" is the claim
the cache already makes and tests: a check over entries equals a check that elaborated. The
first note's merged-reports design (workers send their diagnostics, the main thread merges
them) is dropped: it would re-implement `check_in_order`'s filtering
(`crates/driver/src/project.rs:319-389`: syntax errors first, what a broken namespace hides,
statement style from the files' text) and carry positions between sessions whose file ids
differ. The price of the last pass is one warm check: 2.1 s for `tools/fmt` when nothing
needs loading **[measured, SW-4410, older build]**, at most one full load, 4.8 s and 1.2 GB
**[measured 24 Nov]**, when something does. It can be removed later if it shows in the
measure; stage 3 needs a join at the same place anyway.

### 9.2 What the user sees

| | With `--jobs N`, N > 1 |
|---|---|
| The flag | `check --jobs N` (`-j N`), or `--jobs auto`; `STITCHWORT_JOBS` for scripts. A project check of everything, of namespaces or of subtrees. |
| Default | 1 now. Later `auto`, once the byte-compare (9.5) has been clean on std, AoC and `tools/fmt` under Overmind for a while: the orchestrator's call. `auto` is min(cores, 8, memory / 2 GB), from the measure. |
| Messages, summary, exit code | The last pass's, so exactly a sequential check's: canonical order (`project.rs:343`), `checked N namespaces of P` (`crates/cli/src/main.rs:2421`), exit 1 on an error or goal, 3 on `E-RESOURCE` (`main.rs:1740-1750`). |
| "Still checking" notes | Printed live by whichever worker is checking the slow declaration; the same notes as a sequential cold check prints, since each is set off by the declaration's own step count (`crates/elab/src/progress.rs:1-13`), but in the order they happen. The last pass prints none for what it replays. The sink is one global function already (`progress.rs:29`). |
| Ctrl-C, `kill` | As now: the signal thread prints `check stopped early ... while checking X` and exits 3 (`main.rs:1789-1798`); X is one of the declarations being checked, which `progress.rs:33-35` already says. Entries are written by rename (`check_cache.rs`, `write_atomically`), so a killed run leaves a valid, partly filled cache, and the next run carries on from it. |
| `--timings` | Works: the row tables are process-wide (`ROWS`, `DECL_ROWS`, `crates/elab/src/timings.rs:147-148`), only the open frames are per thread (`:143-146`). Three small changes (9.5, step 4): a worker's replays of dependencies are summed into one row per worker, `worker 3: loading`; a `(cached)` row is dropped when the same namespace has a real row; the last line gives the jobs, the wall time and the sum of unit times, since "outside the units" (`:447-452`) is meaningless across threads. Rows come in the order work finished. Step counts can differ from a sequential run's (9.4). |
| `--no-cache` | Allowed with `--jobs` (D3731): the in-memory store. Nothing on disk is read or written. |
| `--recheck`, `--carry-over`, `--only`, `--expand*`, `--no-project-cache`, a file target | One job, whatever `--jobs` says (with `--timings`, the summary line says why). `--recheck` re-checks every entry it loads, which each worker would repeat; carried-over entries make everything written after them inexact (`cache/mod.rs:445`); `--only` namespaces have no key (`cache/mod.rs:977-980`); the others don't use namespace entries. Not an error, so that the default can become `auto` without breaking these. |
| `--index`, `--counterexamples` | Work: the last pass loads everything (`Load::Everything`, `main.rs:2383-2387`), from the entries just written. |
| `test`, `run`, `build`, `axioms`, `audit`, `doc` | Not in stage 1. The fill is one driver function (9.3) that any of them can call before its own load; `test` is the one worth doing next (a follow-up ticket). |
| The editor (`stitchwort lsp`, `crates/driver/src/live.rs`) | Unchanged. `LiveProject` checks one namespace per step and "nothing here reads files or starts threads" (`live.rs:17-18`); the place for the fill is the server's start-up on a project with a cold cache, with the server's cancellation flag given to the workers. A follow-up ticket, after stage 1 is measured. Built as 9.9 (SW-4760). |
| Cancellation inside a run | One shared stop flag. Workers look at it between namespaces, and it is installed in each worker's budget (`Budget::set_cancel_flag`, `crates/core/src/budget.rs:10-12`) so a stop also ends a namespace part-way; a cancelled namespace is never written (`cache/mod.rs:1144`). Stage 1 sets it only when a worker panics; the editor sets it at shutdown, not on a keystroke (9.9). |

### 9.3 The scheduler

**Set-up, on the main thread.** Read the project's files once, as now, into
`Vec<(String, String)>` (plain text, shared with the workers by reference). Analyse them,
resolve the target, compute the canonical order (`load_analysis_for`, `project.rs:106-230`).
Open the store before any worker starts, so the directory's salt exists (`check_cache.rs:271`
makes the header on first use; two workers making it at once could disagree). Then decide
whether to fill at all: not if a rule of 9.2 says one job, and not if fewer than two
namespaces lack a usable entry (`plan_namespace`, `cache/mod.rs:757`, says which without
loading anything). A warm check is therefore exactly today's.

**Workers.** `N` threads on the check's 64 MiB stack (`main.rs:1100`, through
`driver::with_session`, `driver.rs:71`, so the session's limits match its thread). Each makes
a session with the main session's options, opens its own handle on the store, analyses the
shared texts itself (`project::analyse`, `project.rs:892`) and does the same preparation
(namespace sources, `project.rs:261-264`). Workers share no values. Each has its own analysis
because a session's file ids are its own, and nothing an entry holds depends on them: entries
name files by name and positions as (file, byte range) (`cache/mod.rs:12-14`). The parse is
repeated per worker; what it costs is in `--timings`' "outside the units" figure **[not
measured here]**.

- *The directory store* needs no sharing: `CheckCache` is a folder of files written by rename,
  with a per-handle listing cache in a `RefCell` (`check_cache.rs:103-123`), so each worker
  opens its own (`CheckCache::at`, `:64`). `Rc<dyn Store>` stays as it is
  (`cache/mod.rs:412`).
- *The in-memory store* (`--no-cache`): one `Arc<Mutex<HashMap<(unit, key), Arc<[u8]>>>>`
  with this build's compiler and kernel fingerprints and a salt made for the run; each
  thread wraps the `Arc` in its own `Rc<dyn Store>`. For `tools/fmt` it holds about 260
  entries; the disk cache there is 325 MB for 1,138 files of several builds **[measured,
  `du` today]**, so one build's is perhaps 80 to 150 MB **[estimated]**.

**A job.** A worker given namespace `N` calls, for each namespace of `N`'s closure its
session lacks, in canonical order, and then for `N` itself, the function the sequential
check calls: `Session::check_project_namespace` (`project.rs:439`). For a dependency that
finds the entry another worker wrote and replays it (`elaborate_namespace_cached`,
`cache/mod.rs:1028-1093`); for `N` it misses, elaborates, and writes the entry if `N` is
clean (`:1140-1175`). The worker tells the scheduler whether an entry now exists (the
session's `namespace_written` or `namespace_hits` went up, `cache/mod.rs:165-167`). If not,
it rewinds its session to before `N` (`mark` and `rewind`, as `project.rs:281-292` does), so
no later job runs in a session holding a failed namespace. A worker keeps its session for
the whole run: it loads any namespace at most once. That is the difference from the process
run, which paid 233 of 329 CPU-seconds reloading **[measured, 22 Nov addendum]**.

**Ready, and left.** A namespace is *ready* when every namespace it uses directly has an
entry written in this run or found by the plan. It is *left* (to the last pass) if it has a
syntax error, or a worker checked it and wrote nothing (an error, a goal, something the
encoder can't store), or it uses a namespace that is left. Nothing else stops: after a
failure the rest of the graph is still filled side by side, and the last pass checks only
the failed namespaces and what is above them. (Section 8.3 had the whole run stop at the
first failure; this is cheaper for a failing run and simpler. `tools/fmt` with a `?` in it
keeps the gain for everything not above the `?`.)

**Picking.** An idle worker takes, among the ready namespaces, the one with the longest
chain of namespaces above it (the critical path matters most; counted in namespaces, since
times aren't known beforehand), then the one whose closure it has most of already (less to
load, and less held twice), then the first in canonical order. With `STITCHWORT_JOBS_SEED`
set, a seeded random ready namespace instead: for the stress test (9.5). Nothing that is
reported depends on the pick.

**Library files.** They load on demand inside a namespace's check, each with its own entry
(`cache/mod.rs:617-627`), and which ones a namespace needs is only known as it is elaborated
(`cache/mod.rs:38-42`). With a cold library, several workers would elaborate the same file at
once: correct (each writes the same bytes by rename), and no slower in wall time than "the
library first on one core", but wasted CPU and memory on a shared machine. So the store
handle each worker gets is wrapped in a claim table, shared and in memory: a read of a
`std.` unit that finds no entry claims it and returns nothing (the worker elaborates and
writes it, as now); a read of a unit another worker has claimed waits until that worker
writes it or finishes its job, then reads again. No deadlock: a worker waits only for a file
below one it holds or, holding none, for any file, and the library's file graph has no cycle
(`cache/mod.rs:563-564`, "the index is checked"). This also checks different library files
side by side, which "library first on one core" (the 2.1x figure) did not assume. It is all
in the driver; the elaborator sees a store.

**What a worker loads, and memory.** Only closures of the namespaces it is given. In the
worst case every worker ends up holding the whole project: for `tools/fmt` 4.8 s of loading
and 1.2 GB each **[measured: one full load]**, plus its working peak, plus the main
session's last pass (up to another 1.2 GB if it has to load). So 8 jobs on `tools/fmt` may
reach 12 to 16 GB, 4 jobs 6 to 8 GB **[estimated; the measure gives the real figure]**; AoC
is flat, so a worker holds the shared namespaces and its own days, well under its 0.7 GB
full load. Stage 1 has no cap inside a run beyond the job count: `auto` allows 2 GB a job,
and lanes never pass `--jobs` (the load rules in `CLAUDE.md` assume one core per check). If
the measure shows 8 jobs over budget, the follow-up is a worker that starts its session
afresh (`rewind_fresh`, `crates/driver/src/rewind.rs`) when its next job shares little with
what it holds; stage 2 (load only interfaces) is the real answer. Worker sessions are
forgotten, not dropped, at the end, as the CLI's is (`main.rs:2718-2720`).

**The end.** When nothing is ready or running, the workers stop and the main session runs
`load_analysis_for` as today, with the same store.

### 9.4 Why the result is the sequential one

Compare `check --jobs N` with `check --jobs 1` on the same sources and the same starting
cache.

1. **Messages, order, summary, exit code.** Produced by the last pass, which is the
   sequential check run over a cache that now holds more entries. So the claim reduces to
   one the cache already makes: a check over entries reports what a check that elaborated
   reports. The parts, **[verified]**: an entry holds the namespace's own warnings
   (`cache/mod.rs:1159-1163`); doc-link warnings are never cached and are made again
   (`:1090-1095`, and a namespace with doc links is always loaded, `project.rs:418`);
   statement-style warnings are made again from the text for a namespace that is left out
   (`project.rs:344-353`) or loaded (`:476-477`); only clean namespaces have entries
   (`cache/mod.rs:1140-1144`), so every error and goal is reported by a namespace the last
   pass elaborates itself; and if one of those follows a namespace that was left out, the
   pass starts again with everything loaded (`project.rs:357-361`, `:289-296`), because an
   error's text can name any loaded namespace. That rule is what makes invariant I1's
   weakness for errors (section 8.1) harmless, and it is today's code.
2. **Entries and hashes.** Each entry is written by `elaborate_namespace_cached` in a
   session that holds the namespace's closure by replay. Its key is the same in every
   session: text, modes, and each dependency's digest (`namespace_cache_key`,
   `cache/mod.rs:965-1022`), and a session has the digest of whatever it replayed or wrote
   (`:1066`, `:1166`). Its bytes are the same as a sequential check's by the invariants of
   section 2.4: I3 (replay equals elaboration; the differential test,
   `crates/driver/tests/projects/check_cache.rs:5-11`), I4 (names are local), and I2 (the
   order the closure arrived in doesn't matter). I2 is the one this design leans on more
   than anything before it: 258 entries were byte for byte equal between a sequential check
   and four processes **[measured, 22 Nov]**, but each of those processes loaded its closure
   in canonical order. A kept session loads in the order its jobs came. The standing test
   and the random schedules (9.5) are the evidence for it; nothing I read contradicts it,
   and entries name declarations "by full path and the interface hash ..., never by
   load-order ids" (`cache/mod.rs:12-13`).
3. **A worker that is wrong costs time, not correctness, with the cache on.** If a worker
   computes a different key from the main session's (a file changed on disk mid-run is
   impossible, since texts are shared; a bug is not), the last pass misses and elaborates
   the namespace itself. If a worker panics, the stop flag ends the fill and the last pass
   meets the same panic on the main thread, reported as now. If an entry fails to replay,
   that is counted (`refused`, `late_misses`, `cache/mod.rs:180-189`) and the namespace is
   elaborated. What the design cannot catch is an entry that replays cleanly and is wrong:
   that is the cache's trust, unchanged with the cache on, and D3731's subject with
   `--no-cache`.
4. **`E-RESOURCE`: stated, not solved.** "The steps a declaration's check takes can depend
   on which earlier check already forced a call in a kept type, so on whether those were
   checked or replayed from the cache. Results don't" (`docs/core.md:272`). A worker checks
   each namespace against replayed dependencies; a sequential cold check checks it against
   elaborated ones. So a declaration within that margin of its step limit could pass in one
   and stop with `E-RESOURCE` in the other. Three cases. A worker stops where a sequential
   check would pass: the namespace is left, and the last pass checks it, again against
   replayed dependencies, so it probably stops too: `--jobs N` reports `E-RESOURCE` where
   `--jobs 1 --no-cache` passes. The reverse: `--jobs N` passes where a cold sequential
   check stops. Neither accepts anything false; both exist today between a cold check and
   the check after an edit, which also runs against replayed dependencies. So the exact
   statement is: **`--jobs N` gives each namespace the verdict of a check after an edit to
   it, not of a cold check**, and the two differ only for a declaration within a kept
   type's forcing cost of its limit of 10 billion steps. The byte-compare shows whether any
   declaration in the repo is there **[not verified: none known]**. Making step counts
   independent of history (charging a kept type's forcing to nobody, or always to its
   owner) would remove the case for cold against warm as well; it is kernel work and a
   separate ticket, not stage 1.
5. **Not the same, by design:** `--timings` (times, row order, step counts), the order of
   "still checking" notes against other output, and `STITCHWORT_CACHE_DEBUG` lines.

### 9.5 Build plan (SW-4719, Opus)

No kernel change, no change to terms, hashes, keys or the entry format. `crates/core` and
`crates/elab/src/cache/` are not edited (SW-4714 is working there).

| Step | What | Files |
|---|---|---|
| 1 | Split `load_analysis_for` into "prepare" (target, order, namespace sources; `project.rs:106-261`) and "check" (`:262-310`), behaviour unchanged, so a worker can prepare without checking | `crates/driver/src/project.rs` |
| 2 | `parallel.rs`: the scheduler (a `Mutex` and `Condvar` over per-namespace state, as `par_map_with_at_most` does for a list, `driver.rs:180-200`), workers, the job loop, the stop flag, the seeded pick; `Session::fill_in_parallel(files, project, target, jobs, make_session, make_store)` returning counts (filled, left, namespaces a worker had to elaborate twice) | new `crates/driver/src/parallel.rs`; `driver.rs` for the session constructor a worker uses |
| 3 | The in-memory store and the library claim table, as `Store` wrappers | `crates/driver/src/check_cache.rs` |
| 4 | `--jobs`, `-j`, `STITCHWORT_JOBS`, the one-job rules of 9.2; `--timings`: loading rows, the `(cached)` duplicate, the summary line | `crates/cli/src/main.rs`, `crates/elab/src/timings.rs` |
| 5 | Tests (below) | new `crates/driver/tests/projects/parallel.rs` |
| 6 | Docs: the flag in the guide's command page and `docs/testing.md` if it names check's flags; the trust wording where `--no-cache` is called "the full check" (`cache/mod.rs:22-24` is a doc comment in SW-4714's file: leave a note for the orchestrator to apply after it merges; `docs/proposals/check-cache-trust.md`); a performance-log entry with the measure (D3444) | docs |

**Tests** (each a named test, seconds; the lane runs only these):

- *Byte-compare, standing.* On two or three small multi-namespace projects (ones under
  `examples/projects/accept/`, which `crates/driver/tests/projects/check_cache.rs:273`
  already uses, and `docs/proposals/parallel-checking/tests/par_project` copied into the
  test's own fixtures, not into `examples/`, which the examples suite sweeps), one with a
  diamond and a chain: check with 1 job into cache A; with 4 jobs into cache B, given A's
  `check/header` first so the salts agree; with 4 jobs into memory. Assert: rendered
  diagnostics equal; A and B hold the same file names and bytes; the last pass's session
  dumps the same as the sequential one (`cache::canonical_dump`, as `check_cache.rs:22`
  uses it); `refused`, `late_misses` and "elaborated twice" are 0; the fill really ran
  (filled > 0).
- *Random schedules.* The same compare under `STITCHWORT_JOBS_SEED` = 0..20, jobs 3, on the
  smallest fixture: cheap, and it is the test of I2.
- *Failures.* A fixture with an error in a middle namespace, one with a goal
  (`open-goals: warn`), one with a syntax error: diagnostics and exit as with 1 job; the
  namespaces not above the failure have entries; nothing above it does.
- *The one-job rules:* `--recheck --jobs 4` runs no fill.
- *Claims:* two workers needing one uncached library file elaborate it once (count
  `misses` for `std.` units across workers).

Whole-project compares are not a lane's: `tools/fmt`, AoC and std go in the measure below,
and afterwards in Overmind's rolling check as a second run with `--jobs 4` whose output and
cache are compared with the `--jobs 1` run it already does (which stays the reference:
D3731's second guard).

**The measure** (the orchestrator or Overmind; about 12 minutes of machine time for
`tools/fmt`, more for `aoc` **[estimated from 110 to 146 s cold checks]**):

    docs/proposals/parallel-checking/measure_jobs.sh target/release/stitchwort tools/fmt OUT

It runs the cold check with 1, 4 and 8 jobs three ways (cache and library cold; library
filled first with `check --std Std`; `--no-cache`), prints wall time and peak memory for
each, and compares every run's output and cache folder with the 1-job run's. Written
against the flag as designed and syntax-checked only: it can't run until SW-4719 exists.
Predictions to hold it to: `tools/fmt`, library filled, 4 jobs about 2.2x and 8 jobs about
2.4x of the project part (bound 2.5x **[measured 24 Nov]**), less 2 to 5 s for the last
pass; cold library, about 2.1x or a little better with claims; AoC, library filled, 8 jobs
4x to 5.9x **[bound measured; the rest estimated]**.

**Estimate.** About 700 to 900 lines of Rust and 300 of tests, in the driver and CLI, with
one judgement-heavy part (the scheduler's states). Past Opus lanes of this kind: SW-4707
took 43 minutes against 90, SW-4701 32. **Expected: 75 minutes**, stop and report at 110.
A natural half-way commit is steps 1, 2 and the first test with the directory store
(about 45 minutes); steps 3 to 6 follow on the same branch. Then a Fable review of the
driver's trust wording and of the scheduler's "written" test (that a namespace is never
called filled without an entry), 20 minutes.

**Risks, in order.**

1. I2 fails somewhere (an id-ordered walk that reaches an entry's bytes). Found by the
   random-schedule test or the whole-project compare; each case is also a cache bug today
   (the editor already loads out of order, `project.rs:559`). With the cache on it costs a
   differing entry, not a wrong message, since messages come from the last pass.
2. The gain is below the static figure because loading, duplicated memory traffic and the
   last pass eat it (the process run's own time rose 35% at 6 processes **[measured]**).
   The measure decides; stage 2 is the remedy.
3. Memory at 8 jobs on `tools/fmt`.
4. A deadlock in the claim table despite the argument above. The test covers the simple
   case; a bounded wait that falls back to elaborating is a cheap belt, and changes no
   result.

### 9.6 If D3731 is "no"

Then `--jobs N` with `--no-cache` runs one job, and the in-memory store (half of step 3 and
one test) isn't built; everything else stands. With the cache on, a parallel check trusts
nothing a second `check` in the same folder doesn't trust today: it is the same sequence,
entries written and then read, inside one process. The cost of "no" is that the one check
people run cold on purpose, `--no-cache`, stays at one core; Overmind's uncached whole-AoC
check is the main one.

Under "yes", what `--no-cache --jobs N` promises, exactly: no entry from disk is used; each
entry in the run's memory was written by a worker only after this build's kernel had
accepted every declaration in it (`cache/mod.rs:1140-1167`); the last pass reports a
namespace as checked only from such an entry or from its own check. A declaration may be
checked more than once (a library file two workers both needed before claims, a namespace
the last pass elaborates again), never zero times.

### 9.7 Decisions for Matt

None beyond D3731. The rest are the orchestrator's, with my recommendations: default 1 now,
`auto` later (min of cores, 8 and memory / 2 GB); the one-job rules of 9.2 as quiet
fall-backs, not errors; Overmind's rolling check keeps `--jobs 1` as the reference and adds
a compared `--jobs 4` run; lanes never pass `--jobs`; `test` and the editor's start-up as
follow-up tickets after the measure.

One thing to tell Matt, not ask: the `E-RESOURCE` statement of 9.4 item 4. It is today's
behaviour of a check after an edit, now also the behaviour of a parallel cold check, and
removing it is kernel work that would get its own note.

### 9.8 What I could not verify

- Any timing: nothing was run. The last pass's cost on today's build (2.1 s is SW-4410's),
  the parse a worker repeats, and peak memory are the measure's.
- I2 for kept sessions (9.4 item 2).
- That syntax trees can't be shared between threads; I assumed not and gave each worker its
  own analysis, which is also what keeps file ids apart. (`crates/syntax` has `Rc` only in
  `source.rs` and `stack.rs` by grep, so sharing may be possible later.)
- That every clean namespace of `tools/fmt` and AoC gets an entry today (none
  "uncacheable"): a namespace the encoder can't store is left to the last pass with
  everything above it, which is correct but loses the gain there. The fill's counts show
  it.
- That signals stay blocked in threads started after the signal thread is set up
  (`main.rs:1776-1802`); standard for thread signal masks, not read through.
- `measure_jobs.sh` beyond `bash -n`.

### 9.9 The editor's start-up fill (SW-4760)

Built after stage 3, by an Opus lane; the editor row of 9.2 said where it goes. **Off by
default**: whether it becomes the default is Matt's decision, on the numbers below.

**What it does.** When `stitchwort lsp` first loads a project whose check cache is on disk
(`crates/lsp/src/lib.rs`, `load_project`) and the setting asks for two or more workers, it
starts one thread that runs `parallel::fill` over the project, everything as the target,
with that many workers (stage 3: interface job, then proof job, per namespace). The fill
reads the files from disk (`Source::fill_files`; the playground's in-memory projects have
none, so the browser never fills) and writes entries through the project's ordinary
`CheckCache`. The workers' sessions are made as the editor's are (`session_for`: navigation
and expression types), since entries are keyed by what they record (`+nav+ty`) and an entry
made without navigation would never be found by the editor. Each project is filled at most
once in the server's life.

**The editor beside it.** Nothing in `live.rs` changes but one method
(`LiveProject::next_namespace`, the namespace the next step checks, planning first as the
step would). Before each step of a project, the checker asks the fill's `Watch` whether
the fill may still write that namespace's entry (its proof job is waiting or running; until
the fill has planned, every namespace counts). If so, and every file of the project is as
on disk, it doesn't step: it waits for an edit for up to 20 ms (`FILL_POLL`) and asks
again. Once the fill has written the entry (or left the namespace, or ended), the step runs
and replays it, or checks the namespace itself if there is nothing to replay. So the
checker never checks a namespace a worker is checking, and its steps pick up entries as
they appear. Requests are answered on the main thread throughout, from what has been
published, as during any check.

**Unsaved edits.** The fill keys entries by the text on disk. An edit doesn't cancel it:
its entries stay right for the disk text, and the edited namespace's step simply doesn't
find one for the edited text. While any file differs from the disk, the checker doesn't
wait for the fill at all and steps as without it (a namespace both check is then checked
twice, which costs time only).

**Cancellation.** One flag for all fills, set when the server shuts down (`serve_from`,
after `Main::run`), given to the fill as `Jobs::cancel`. It becomes each worker's
cancellation flag (as the panic flag of 9.2 was), so a namespace being checked stops
part-way and isn't written (`cache/mod.rs`, the `cancelled()` tests before and after
encoding); workers waiting for a job look at it every 50 ms (`STOP_POLL`). The server then
joins the fill thread before it returns. A panic inside the fill ends the fill, not the
server; the checker checks what the fill didn't write.

**Memory.** The command line leaves the workers' sessions allocated, since the process is
about to end; the server frees them (`Jobs::free_sessions`). Peak memory is the editor's
session plus the workers' (measured below).

**The setting.** `startupWorkers` in the server's settings (`initializationOptions` and
`workspace/didChangeConfiguration`): `"off"`, `"auto"` (the default) or a number; read when
a project is loaded. VS Code: `stitchwort.startupWorkers`. Other editors:
`STITCHWORT_STARTUP_WORKERS`, which the editor's setting overrides. `auto` is
`parallel::auto_jobs()`: min(cores, 8, memory / 2 GB), at least 1 (the rule of 9.2; the
first code for it, which `check --jobs auto` can use too).

**What the user sees.** Only the speed: every diagnostic is published by the editor's own
steps, as before, from a check or from an entry, and an entry gives what the check gave
(the cache's existing claim). The test `a_startup_fill_gives_the_same_diagnostics`
(`crates/cli/tests/server/lsp.rs`) compares every file's diagnostics, an error and an open
goal among them, with the fill off and on; `shutdown_during_a_startup_fill_writes_nothing_partial`
shuts down while a namespace is being filled and finds no entry for it or what uses it, and
no temporary file.

**Measured** (25 Nov, `measured-2026-11-25/lsp-startup.txt`, `measure_lsp_startup.sh` driving
`lsp_startup.py`, a small LSP client; release build, Speedwell shared with other lanes).
`tools/fmt` with the project's entries cold and the library's warm; the client opens
`Fmt/CommentsKeptProof.sw`, which has 139 of the 150 namespaces below it, and times its
first diagnostics and the moment every one of the 191 source files has been published:

| Fill | Run | First diagnostics | Whole project | Peak memory |
|---|---|---|---|---|
| off | 1 | 133.3 s | 141.5 s | 2.99 GB |
| off | 2 | 140.1 s | 147.3 s | 3.05 GB |
| `auto` (8 workers) | 1 | 55.4 s | 57.9 s | 6.92 GB |
| `auto` (8 workers) | 2 | 32.8 s | 34.9 s | 7.00 GB |

So **about 2.5x to 4x sooner** for both numbers; the slower "on" run ran at a load average
near 50 from other lanes, the faster one near 10. The fill itself took 48.2 s and 28.9 s
(150 namespaces filled, none left); the rest is the editor replaying 150 entries after it,
a few seconds, and its own load of the library before the first step. Memory is the
price: **about 7 GB at the peak against 3 GB**, the editor's session plus eight workers'
(they record navigation, which the command line's don't; its stage 3 run peaked at 6.1 to
6.3 GB, `stage3-vs-stage1.txt`). The fill's memory is freed when it ends.

**Not done, and limits.**

- The editor loads every library file itself when it loads a project
  (`LiveProject::new_except`), on its own thread, before its first step. With the library
  cold, that runs beside the fill, which loads the library files it needs through its own
  claims, so some library files are elaborated twice. Measured only with the library warm.
- While the checker waits for the fill on one project, it doesn't step other workspaces
  (another project, a file on its own); they wait for the fill too.
- One fill per project per server: a project loaded again (a `stitchwort.yaml` change) is
  not filled again. A fill is not restarted by a later setting change.
- The default was Matt's decision: D3739, Matt, 25 Nov 2026: on by default, `auto` (a smaller
  fixed number such as 4 would halve the extra memory; `off` switches the fill off).

## 10. Stage 2 design: the stated theorem, and loading without proofs (SW-4727)

Fable paper lane, after D3730 (the end state is stage 3, whose kernel form "comes back to
him") and D3731. The code was read at `5aa4c8604`; nothing was built and no check was run.
Marks: **[verified]** read today at the file and line given; **[measured]** by an earlier
run, cited; **[estimated]**; **[not verified]**. Stage 1 (section 9, SW-4719) and the
digest cache's stages A and C (SW-4707, SW-4714) are merged and taken as given.

### 10.1 Summary

**The problem.** Each worker of `check --jobs N` loads its dependencies whole, proofs
included: 4.8 s and 1.2 GB for all of `tools/fmt` **[measured 24 Nov]**, though nothing a
worker then does may look at one of those proofs. And stage 3 needs a namespace checked
against theorems below it whose proofs are still being checked on another thread. The
kernel can't hold either: a final theorem always has its proof.

**The change.** One new kernel form, a **stated theorem**: a theorem that is final, has its
statement and has no proof in this session. To everything that uses it, it is the proved
theorem: it never unfolded anyway, it compares equal to any proof of its statement anyway,
and it hashes as a proved theorem's reference does. Only two kernel functions make one.
Stage 2 uses the first: a cache entry is split into an interface part and a proofs part,
and a session that only needs to check against a dependency reads the first part alone.
Every stated theorem in stage 2 is one whose proof this build's kernel has already
checked, in the session that wrote the entry: nothing is promised, less is read.

**What it should do.** Less loading time and memory per worker and for the check after an
edit **[estimated; the share of an entry that is proofs is step 0's measure]**; and it is
the form stage 3 needs, where it does carry a promise. The verdict stays where stage 1 put
it: the last pass, today's sequential check, which believes only whole entries.

**For Matt:** one decision, the form and its two rules (10.7).

### 10.2 The kernel form

**What it is.** Not a new declaration kind and not an assumption: a flag on a theorem,
`Def::stated`. A stated theorem has `theorem` set, `state == Final`, its type, its proof
mark (`Def::proof`, always true: its type is a proposition), no body, no group, arity 0
and no assumption label; the last three are as `check::assume` leaves a constant
(`crates/core/src/check.rs:3054-3112` **[verified]**). The name avoids "promise", which
the code already uses for something else (`Promise::ProofsOnly`, `hash.rs:143`).

Why not the alternatives:

| Alternative | Why not |
|---|---|
| A new kind of assumption (`AssumptionKind::Stated`) | An assumption hashes by its own tag and label (`hash.rs:180-203` **[verified]**), on purpose: filling a `?` must change every user's hash. A stated theorem must do the opposite. And `relied_on` reports every assumption as a gap, so every reader of reliance would need the exception |
| A dummy body | Every reader of bodies (reliance, `axioms`, the encoder, the runtimes) would read it as the proof |
| A lazy body, decoded when first read (Lean's `.olean`, Rocq's delayed opaque proof) | Good for stage 2 alone, and worth keeping in mind as a later refinement of it. But stage 3's theorem has no proof anywhere yet, so the lazy read would have to block on another thread, inside kernel data. The flag serves both stages, and "the proofs aren't here" stays a fact a caller can test |

**Who can make one.** Two kernel functions, nothing else:

1. `check::admit_trusted_stated(name, path, ty, span)`, beside `admit_trusted_def`
   (`check.rs:4085`) on the cache's trust boundary: the same structural checks (the type
   refers only to final declarations, `case` only in a tree), then final at once with the
   flag. Stage 2 uses only this one. It is called only by the cache's replay, for an entry
   this build wrote after checking the proof.
2. `check::leave_stated(id)`, for stage 3: turns a *pending* theorem, whose statement
   `declare_def` has just checked (a type, a proposition), into a stated one instead of
   `define_group` giving it a body. Not built in stage 2.

Source can't write one, and nothing turns a stated theorem back: it isn't pending, so
`define_group`, `retype_def`, `set_run_body`, `add_validator` and the native registrations
refuse it as they refuse an assumption (`docs/core.md`, "It never gets a body"
**[verified in the spec]**). A session that needs the proofs loads the namespace again in
full (10.4); it doesn't patch a body in.

**Typing rule.** None new. `Σ, t° : T` where `T` is a proposition in `Σ`: the rule for an
assumption, which is the rule for a variable of type `T` bound outside every declaration
(`docs/core.md`, "Why it's sound"). The kernel's judgement for a declaration that mentions
stated theorems `t₁° … tₙ°` is "well typed given `t₁: T₁ … tₙ: Tₙ`", a premise for each.
What stage 2 adds is the reason each premise holds: the same build's kernel checked a
proof of `Tᵢ` before the entry that carries `tᵢ°` was written (10.3).

**Conversion and evaluation.** A call of one is neutral and never unfolds (`body_seen` is
empty, as for any theorem under rule F: `value.rs:3435-3457` **[verified]**), two calls
are equal by rule I whatever their arguments' proofs, and rules K and S read only marks.
So far it is exactly a proved theorem. Three places in the kernel read a definition's body
*without* going through `body_seen`, and so can tell the two apart today
**[verified by grep of `.body` in `crates/core/src`, each site read]**:

- `value::next_parameter` (`value.rs:5429-5441`): for a definition applied to fewer
  arguments than its arity, the implicitness and proof mark of its next lambda, read off
  the body. Conversion's eta for definitions uses it (`push_eta`, `value.rs:5407`), and so
  does the unifier's (`crates/elab/src/unify.rs:2795-2808`). For a theorem this reads the
  shape of the *proof* (`theorem t: (n: Nat) -> P n := n => …` has arity 1;
  `:= otherLemma` has arity 0). **This is a hole in rule 6 ("no other declaration ever
  sees a theorem's proof") that exists today**, apart from this design: a proof rewritten
  from lambdas to a bare lemma keeps its namespace's interface digest, and a dependant
  that compared a partial application of it took a different path. I could not build a
  case where the verdict or a term differs: when both sides are marked proofs rule I
  answers first, and against an unmarked value the two paths (compare `t a` with `h`, or
  `t a x` with `h x`) seem to agree **[argued, not verified; not probed]**. The fix is the
  same either way: `next_parameter` returns nothing for a frozen definition, so eta never
  reads a proof, stated or not. It is a change to conversion, so it goes through the
  soundness set and a review (step 1).
- `value::erases_result` (`value.rs:3731-3735`): while a program runs, "has a body, or is
  an assumption". A stated theorem must count too (its type erases), though sessions that
  run load proofs anyway (10.4).
- `hash::def_hash` returns `None` without a body (`hash.rs:205-207`). The replay already
  puts each declaration's recorded full hash in the kernel's hash cache
  (`cache/mod.rs:3913-3925` **[verified]**), so a stated theorem's full hash is the
  entry's; the interface part of the entry keeps it.

`slot_type` and `case_tree` (`value.rs:2943`, `:3359`) read the body of the definition
being unfolded, which is never a theorem while checking.

**Hashing.** `has_interface` (`hash.rs:235-238`) becomes: a final theorem that is no
assumption and either has a proof or is stated. `interface_hash` is then unchanged code:
the tag `theorem` and the type (`hash.rs:245-258`). So **a stated theorem's interface hash
already equals the proved theorem's**, by construction, and every user's hash, every
dependency record (`cache/mod.rs:3563-3577`) and every digest is the same whichever the
session holds. That is the property an assumption could not give.

**A theorem in a group.** A group's hash covers every member's whole declaration
(`hash.rs:18-28`, `group_hashes`, `:340-392` **[verified]**), so a computing definition
checked in one group with a theorem has that theorem's proof in its own hash. Rule: a
theorem is loaded as stated only if every other member of its group is too, or is a
proof-private helper that is left out (10.4). Otherwise the whole group loads with its
bodies. The writer decides, per entry; the reader does what the entry says.

**What may refer to one.** Anything that may refer to a theorem. What must *not* happen is
a report that depends on the missing proof. The readers of proofs outside checking, and
the rule for each:

| Reader | Rule |
|---|---|
| Reliance on open goals and stand-ins (`assumption::relied_on`, `mentions`, `assumption.rs:144-154`) | A stated theorem is a leaf that relies on nothing. Sound by invariant W (10.3), and only by it |
| `axioms`, `audit` (the walk over bodies, `crates/driver/src/axioms.rs:270-280`) | No invariant covers `Quot.sound`: an entry is written whatever axioms its proofs use. These load proofs (10.4), and the walk **fails closed**: reaching a stated theorem is an internal error, never "no axioms" |
| `run`, `test`, `build`, the runtimes' lowering, JS | Load proofs. Proofs are erased before a run, so this is caution, not need **[not verified that no run path reads a proof body]** |
| The encoder (`cache/mod.rs:2483` refuses a namespace holding "any final definition without a body") | Unchanged: it looks at the namespace's *own* declarations, which stage 2 never states |
| `--recheck`, carried-over entries (they re-check or re-hash bodies, `cache/mod.rs:3819-3840`) | Load proofs |
| `--timings` sizes, `--index`, `--counterexamples`, the editor, `doc` | Load proofs (they are `Load::Everything` already, `project.rs:39-48`) |
| The elaborator's seven "has it a body?" tests (`reading.rs:1886`, `auto.rs:1547`, `opaque.rs:467`, `interfaces.rs:1029`, `:1300`, `module.rs:3219`, `rewrite/repeatedly.rs:1745` **[verified, all seven read]**) | Each means "is it finished?" or "is it an assumption?", not "show me the body". They move to one accessor, `Def::defined()`: has a body or is stated. Two of them decide candidates (`auto_eligible`, the `@[reading]` instance scan), so a miss here would change a result, not only a message |

Beyond those seven, the elaborator's readers of a body's *content* are 40-odd sites in 28
files **[counted by grep, not each read]**. That none reads a *dependency's sealed proof*
while checking is the digest cache's property P2 (`interface-digest-cache.md` 2.1), which
every warm check since stage A has relied on: if it failed, an edited proof below would
already leave a stale entry above. Stage 2 leans on P2 harder (always, not only after a
proof edit), and its byte-compare tests are a new test of it.

**Universes, axioms, anything global a proof could add.** Rocq's gap (section 1.2) was
that a proof adds universe constraints, which are global, so skipping proofs collects
fewer. Stitchwort has none: universes are "numbered, no polymorphism, no cumulativity"
(`docs/core.md:22`, `:51-67` **[verified]**), there is no constraint store, and a proof's
check leaves nothing in the kernel but its own term. What a proof leaves in the
*elaborator* is the real analogue, and it matters for stage 3, not stage 2 (10.5).

### 10.3 The trust argument

**Invariant W (an entry is written by a session with no gap).** A namespace's entry is
written only when its check reported no error and no goal *and* the count of unfinished
declarations did not rise (`cache/mod.rs:1143-1147` **[verified]**), where a declaration
that relies on any assumption, through any body, is counted as unfinished when its
component is checked (`assume.rs:478`; `docs/core.md`, "Reliance"). And an entry is found only under a key made from each
dependency's digest, which a session has only for a dependency it replayed or wrote, so
never for one with a goal or an error (digest note 2.3, rule 3). So in any session, a
namespace that came from an entry has a closure of namespaces that all came from entries
or were checked clean in this session.

**Claim (stage 2).** A check that loads dependencies as stated theorems accepts nothing a
check that loads them whole refuses, and reports "finished" for nothing that relies on an
open goal or a failed proof.

1. *Every stated theorem was proved.* Stage 2 makes one only by replaying an entry, and an
   entry holds only declarations this build's kernel accepted, proofs included, before it
   was written (`cache/mod.rs:1140-1175`; 9.6). With `--no-cache --jobs N` the entry is in
   the run's memory and was written in this run (D3731). So each premise `tᵢ: Tᵢ` of 10.2
   has a checked proof. There is no promise to discharge.
2. *That proof was checked against true statements.* By induction up the namespace order:
   the session that checked `tᵢ`'s proof held its dependencies whole or stated, and the
   stated ones are covered by the induction hypothesis.
3. *The check of a dependant is the same check.* The kernel half is 10.2's list: after
   step 1 no kernel path reads a frozen definition's body. The elaborator half is P2 and
   the seven tests.
4. *Reliance.* By W, the proofs left out reach no assumption, so "relies on nothing" for a
   stated theorem is true, by induction again (the writer's own walk went through stated
   theorems of *its* dependencies, which W covers).
5. *What it trusts:* the cache, as any replay does, and no more. It reads less of an entry
   whose whole is already trusted. The one new thing an entry can lie about is which
   bodies are proofs, and a wrong split can only leave out a body that the kernel then
   treats as absent: `admit_trusted_stated` refuses a type that
   isn't a proposition by the kernel's own mark (`def_mark`, `check.rs:2970`, worked out
   from the type on the trusted path too), so nothing that computes can be stated; and a
   `def` of proposition type passed off as a theorem changes its users' recorded hashes,
   which the replay compares (`cache/mod.rs:3563-3577`).

**What can break it**, and what catches each:

| Break | Effect | Caught by |
|---|---|---|
| A stated theorem that was never proved | Unsound | Can't arise in stage 2 (item 1). In stage 3 it is the join, 10.5 |
| A kernel path that reads a frozen body (`next_parameter` is the one known) | A dependant's check takes another path: other steps, conceivably another verdict | Step 1 removes the known one; the soundness set; byte-compare of every entry against a whole load |
| An elaborator reader of a dependency's proof (P2 false somewhere, or an eighth body test) | A different entry or message from the sequential check's | Byte-compare tests (10.6); already a stale-cache bug today if it exists |
| W false: an entry written for a namespace that relies on a goal | "Finished" reported over a gap | W is today's rule and already load-bearing (a namespace left out by a plain `check` is never walked at all); a fixture with a goal two namespaces down (10.6) |
| `axioms` or `audit` run in a session without proofs | "No axioms" wrongly | Those commands load proofs, and the walk fails closed |
| `E-RESOURCE` near the limit | A run stops, or passes, where the other wouldn't | Not solved, as 9.4 item 4: a session that replays less forces kept types at other moments, so step counts shift. Nothing false is accepted |
| A wrong split in an entry | A refused replay, then a whole load or a fresh check | `refused` stays 0 in the tests |

### 10.4 Loading without proofs

**The entry.** Today an entry has one node table, in first-use order, shared by every type,
body and table row (`cache/codec.rs:234`, `:616-680`; `cache/mod.rs:3581-3600`
**[verified]**), so a reader can't skip proofs. The entry becomes two parts:

- **Part A, the interface:** everything a dependant can read. All records and tables as
  now, except that a *stated-on-load* theorem's record has no body and no group list, and
  proof-private helpers (stage C's definition, `digest_plan`, `cache/mod.rs:2156-2200`)
  have no record and no rows. Its node table holds only what those mention. Each record
  keeps its full hash.
- **Part B, the proofs:** more nodes (which may refer back into A's), then the bodies and
  group lists left out of A, and the private helpers' records and rows.

The encoder gets this by writing the left-out bodies last, so their nodes come last. Which
bodies are left out is the digest pass's answer already (`sealed`, `cache/mod.rs:2659-2666`,
and the plan's private set), plus the group rule of 10.2. A whole load reads A then B and
installs exactly what it installs today; a load without proofs reads A, checks B's length
and seal, and stops. Own declarations are named by position in the entry
(`cache/mod.rs:3581-3584`), and leaving helpers out shifts positions, so the reader maps
"position in the entry" to "id in this session"; a reference in part A to a declaration
that was left out fails the decode ("can't be loaded without proofs"), which falls back to
a whole load. `FORMAT` is bumped. Library files' entries get the same two parts.

**Who loads which.** A session option, proofs or no proofs, default proofs:

| Session | Loads | When |
|---|---|---|
| A fill worker (`parallel.rs`), for a namespace's dependencies | without proofs | step 2 |
| A plain `check` (`Load::Diagnostics`) loading the dependencies of what it must check again | without proofs | step 3, once step 2's compare has been clean |
| The same check, once any loaded namespace has an error or a goal and it starts again with everything loaded (`project.rs:357-361`) | **with** proofs | always: every message a user reads comes from a session as today's |
| Everything else (`Load::Everything`: `test`, `run`, `build`, `axioms`, `audit`, `doc`, `--index`, the editor), `--recheck`, carried-over entries | with proofs | always, for now |

A session never mixes the two for one namespace, and never upgrades in place: if it needs
proofs after loading without, it rewinds and loads again.

**The gain.** Per worker, the loading time and memory that part B accounts for. Not known:
theorems are 77.6% of `tools/fmt`'s checking time **[measured 24 Nov]**, 5,563 theorems
own about 5,000 `%match` helpers **[SW-4707]**, so I expect part B to be well over half
the nodes, and a load to fall from 4.8 s and 1.2 GB to somewhere between 1.5 and 3 s and
0.4 and 0.7 GB **[estimated, weakly: a replay also pays for names, tables and the
dependency records, which stay]**. Step 0 measures the split before anything is built
(per the standing lesson that proof tooling's savings came in below their sketches). The
same gain goes to the check after an edit (5.3 s for one edited proof **[measured 23
Nov]**; how much of that is loading is not measured) and, later, to the editor's start.

### 10.5 Stage 3 in outline

Not designed here; this is what the form has to support, and what stage 3's own note must
settle.

**Two kinds of work per namespace**, both through stage 1's scheduler:

- an *interface pass*: elaborate `N` against the interfaces below, and for each theorem
  that can be deferred call `leave_stated` instead of elaborating its proof; publish
  `iface(N)`, part A alone, under its own unit kind, with the digest it computes;
- a *full check*: today's check of `N` against the interfaces below; it writes `N`'s whole
  entry as now.

Interface passes follow the namespace graph; a full check waits only for the interface
passes of its closure, so the proofs of all namespaces run side by side.

**The join is the key chain, and the judge is still the last pass.** A namespace's key is
made from its dependencies' digests. A full check of `M` that ran against `iface(N)`
writes `M`'s entry under `iface(N)`'s digest. The last pass (today's sequential check,
9.1) reads only whole entries, and has a digest for `N` only from `N`'s whole entry. So it
finds `M`'s entry exactly when `N`'s full check passed, clean, *with the digest the
interface pass claimed*. If `N`'s proof failed, or has a goal, or the interface pass
differed from the full check, `M`'s entry is simply not found, and the last pass checks
`N`, `M` and what is above them itself, in order, with today's messages (`N`'s error, and
"relies on `t`, which has an error" above it). Interface entries are a separate unit kind
that only fill workers read. So "a promise never discharged" costs a sequential re-check,
never a wrong "checked": nothing has to remember to join. That is the difference from
Isabelle, where a theorem value carries its holes and integrity is a dynamic check at
checkpoints, and from Rocq's interactive mode, where the main kernel does not check what
workers return unless asked.

**What is reported when a proof fails:** exactly a sequential check's output, from the last
pass. The cost is that the failed namespace and everything above it are checked on one
thread, as in stage 1.

**The real risk: what a proof leaves in the interface.** Rocq needs `Proof using` because
a statement inside a section isn't known until its proof is. Our analogue: the interface
digest covers things only elaborating a proof produces. Stage C removed the commonest (a
`match` helper only a proof reaches). Still in the digest, and made by proofs: a local
`def` or `theorem` in a proof (nameable as `t.go` from another namespace), equations made
on demand (`equations_done`, `state/tables.rs:66`), a helper that an `unfolding` list
names, anything a tactic adds to a table **[the first is verified in stage C's table; the
others not verified]**. For any namespace where a proof does one of these the interface
pass's digest differs from the full check's, loudly, and that namespace and everything
above it fall to the last pass. Stage 3's note must start with a pilot: an interface pass
by hand (proofs replaced by a stated theorem) over `tools/fmt`, counting how many of the
150 namespaces match. If few match, the fix is in the digest (more made proof-private) or
in a syntactic rule for which proofs can't be deferred, and that is the design.

**Fallback.** Any mismatch, error, goal, panic or refused entry: the last pass, as stage 1.
`--jobs 1` never runs an interface pass.

**Predicted gain** from today's measure **[estimated]**: `tools/fmt`'s project part is
93.9 s on one thread; stage 1's bound is 37.1 s (2.5x), set by the chain. The project's
work that isn't theorems is about 8.6 s (24.5 s of "the rest" less 15.9 s of library and
core), and theorem statements perhaps 4 to 13 s more (5% to 15% of 84.7 s; not measured).
So the interface passes are 13 to 21 s of work, some of it side by side: 6 to 15 s of wall
time. The proofs are about 85 s over 8 workers, 11 s, against a floor of 8.7 s (the
largest namespace). With 2 to 5 s for the last pass: **19 to 33 s, 2.8x to 4.9x**, against
stage 1's 2.5x before its overheads; with the library cold (16 s more, one thread), 2.2x to
3.1x. The library block is then the largest single piece, as section 8 said.

### 10.6 Build plan for stage 2

| Step | What | Files | Who, estimate |
|---|---|---|---|
| 0 | Measure the split. Under `STITCHWORT_CACHE_DEBUG`, the "written" line (`cache/mod.rs:1169`, which already prints the digest's shape) also prints the entry's node count and the digest pass's (the digest pass is the entry less sealed bodies and private helpers, so the ratio is part B's share). The orchestrator runs one cold `tools/fmt` check with it and `measure_load.sh` (below) for the before figures. **Gate:** under about 40% of nodes in part B, stage 2's loading gain is small; build step 1 only, for stage 3 | `crates/elab/src/cache/mod.rs` | Sonnet, 15 min. **Built (SW-4729):** the "written" line now ends with the entry's bytes and nodes and the proofs', positions', navigation's and warnings' bytes against the interface's; `docs/proposals/parallel-checking/measure_cache_split.sh BINARY REPO OUT` for the totals. Proofs are bytes, not nodes (an entry's nodes are shared by address, the digest's by content, so node counts aren't comparable) |
| 1 | The kernel form: `Def::stated`, `Def::defined()`, `admit_trusted_stated`, `has_interface`, `erases_result`, `next_parameter` giving nothing for a frozen definition; the reliance walk's comment and W; the axioms walk failing closed; the seven tests onto `defined()`; `docs/core.md` (a "Stated theorems" part under "Definitions", rule 6's hole closed, the eta change). No caller yet outside tests | `crates/core/src/{globals,check,hash,value,assumption}.rs`, `crates/driver/src/axioms.rs`, the seven elaborator sites, `docs/core.md` | Opus, 40 min; Fable review, 20 min |
| 2 | The entry in two parts (`FORMAT` bump), the decode without part B with the position map, the session option; fill workers load dependencies without proofs | `crates/elab/src/cache/{mod,codec}.rs`, `crates/elab/src/state/session.rs`, `crates/driver/src/parallel.rs` | Opus, 50 min |
| 3 | A plain `check` loads without proofs; the restart on an error or goal loads with; `docs/proposals/check-cache-trust.md`, the guide's performance notes, a performance-log entry (D3444) | `crates/driver/src/project.rs`, docs | Sonnet, 25 min; then the Fable review covers 2 and 3, 25 min |

Estimates are agent time, set from SW-4719 (Opus, 50 + 11 min against 75) and SW-4707 (43
against 90). Steps 2 and 3 edit `cache/mod.rs`, so they run after anything else in flight
there.

**Tests** (each named, seconds; a lane runs only these, plus, for step 1, the whole of
`examples::soundness`, which is the standing rule for a kernel change):

- *Kernel, step 1.* A stated theorem and the proved one have the same interface hash; a
  dependant's term hashes the same against either; `define_group`, `retype_def`,
  `set_run_body` and an `unfolding` list refuse a stated theorem; `admit_trusted_stated`
  refuses a type that isn't final. For the eta change: an example that compares a partial
  application of a theorem with an unmarked value, checked with the proof written as
  lambdas and as a bare lemma, same verdict and same hash of the dependant; and the
  byte-compare below. If any existing hash snapshot moves, stop and report: the argument
  of 10.2 says none should.
- *Byte-compare, step 2.* `parallel.rs`'s tests again with workers loading without proofs:
  every entry and message equal to one job's; `refused`, `late_misses` and "elaborated
  twice" 0. Plus one fixture built for this: a theorem in a group with a computing
  definition (loads whole), a recursive theorem with a private helper, an `instance`
  theorem found by `auto` from the namespace above, a `@[reading]` theorem.
- *Whole against without, step 2.* For each fixture, load the project once each way and
  compare `cache::canonical_dump` of everything but the proofs left out.
- *Reliance, step 3.* `D` has a `?` in a proof, `M` uses that theorem, `N` uses `M`'s
  lemma: goals reported, counts and exit as today, with one job and four. And the reverse:
  fill the `?`, check again, all finished.
- *Fail closed.* `axioms` on a session made without proofs is an internal error, not an
  empty list (a unit test; no command can reach it).

**Measure** (the orchestrator; about 6 minutes of machine time, from the 110 s cold checks):

    docs/proposals/parallel-checking/measure_load.sh target/release/stitchwort tools/fmt OUT

before step 2 and after step 3: time and peak memory of one whole-project load from a warm
cache, with and without proofs once the option exists (it tries `STITCHWORT_LOAD_PROOFS=0`,
the name step 2 should give the debugging switch), and `measure_jobs.sh` again for 4 and 8
jobs. Syntax-checked only. Predictions to hold it to: load 1.5 to 3 s and 0.4 to 0.7 GB;
8 jobs on `tools/fmt` under 8 GB.

**Orchestrator's calls, with my recommendations:** two parts in one file, not two files;
private helpers left out in step 2 if step 0 shows they are over a fifth of part B, else
bodies only (no position map needed); `test` and the editor stay on whole loads until
someone measures a need; the lazy body as a later refinement, if whole loads still hurt.

### 10.7 Decision for Matt

**The stated theorem.**

*The problem.* When several workers check a project side by side, each loads everything
below the file it is checking, proofs and all: nearly five seconds and over a gigabyte per
worker on the formatter. It never looks at those proofs; since proofs were sealed, nothing can. And
the next stage, where every file's proofs are checked side by side, needs a worker to
check against a theorem whose proof another worker hasn't finished. The kernel has no way
to hold a theorem without its proof.

*The change.* The kernel gets one new kind of entry: "this statement is a theorem; its
proof isn't loaded here". Everything that uses it treats it exactly as a proved theorem.
Two rules come with it. First, in this stage it is only ever made from the saved result of
a check in which the kernel did check the proof: nothing unproved is used, only less is
loaded. Second, anything that reports on proofs themselves (which axioms a result rests
on, `audit`, running tests and programs) always loads the proofs, and refuses to answer
rather than guess if it finds one missing. One small change rides along: comparing a
partly applied theorem no longer peeks at how its proof begins, which is the last place
the checker could see into a proof at all.

*What it should do.* Workers load faster and use less memory (my guess is half or better;
a 15-minute measurement comes first and decides whether the loading part is worth
building now). It is also the piece stage 3 stands on. There, "checked" is still decided
at the end by today's one-at-a-time check, which believes only fully checked files; a
proof that fails, or never ran, costs a slower run, never a wrong answer.

**[rec: yes]** The orchestrator's calls are listed in 10.6. Stage 3 gets its own note,
starting from a pilot, and its use of this form (a theorem whose proof truly hasn't been
checked yet) comes back to you then.

### 10.8 What I could not verify

- That `next_parameter`'s read of a proof's lambdas can't change a verdict or a term
  today. Argued in 10.2; no probe was built. If it can, it is a staleness bug in the
  digest cache now, and step 1 fixes it either way.
- The share of an entry, and of a load's time and memory, that is proofs (step 0).
- The 40-odd readers of body content in the elaborator, beyond the seven tests: taken
  from P2 and SW-4700's review, not re-read.
- That nothing on a run path reads a proof body (so `test` and `run` stay on whole loads).
- Which proof by-products other than `%match` helpers reach the digest (10.5): equations
  made on demand and `unfolding` lists naming helpers are named from the tables' list, not
  traced.
- That a library file's entry splits as a namespace's does (same encoder; not read for
  differences).
- `measure_load.sh` beyond `bash -n`.

## 11. Stage 3 pilot (SW-4730, 24 Nov 2026)

The stage 3 design built on this pilot is [parallel-checking-stage-3.md](parallel-checking-stage-3.md) (SW-4753).

Opus lane. The pilot 10.5 asks for: an interface pass by hand, and how many namespaces
give the same interface digest without their proofs as with them.

### 11.1 Method

`STITCHWORT_INTERFACE_PILOT=1` on `check` (or a comma-separated list of namespaces) runs,
for each project namespace it selects, two passes from the same point
(`crates/elab/src/cache/pilot.rs`, the hook in `Session::check_project_namespace`):

- an **interface pass**: the namespace is elaborated as usual except that each lone
  theorem (a component of one, not recursive, not `decreasing`) has its statement
  elaborated and declared, and its proof not elaborated: the theorem is admitted with a
  stand-in body (`Prop`) through `admit_trusted_group`. Its digest is computed as the
  cache computes it (`digest_stream`, the stream `interface_digest` hashes); then the
  session is rewound to before the namespace (and the failed-declarations log, which a
  rewind doesn't cover, is trimmed);
- the **full check**: the ordinary check, elaborated rather than replayed (so it has a
  stream to describe), which writes its entry as usual.

It prints one line per namespace, `interface-pilot: NS: match (…)` or `… differs
[causes: …]` with a line for each difference: own declarations by path with their
interface hash, names, data types, each elaborator table's rows added (by the
declaration they belong to), and the interface pass's errors. Off, it changes nothing
but one `Option` test per group; on, the reported diagnostics are the full check's (a
CLI test, `interface_pilot_says_what_a_proof_leaves_in_the_interface`, compares the
summary with a run without it).

**Why not the stated theorem or `--only`.** `check --only` (`skip_theorems`) leaves a
theorem out altogether, statement too, so the interface differs by construction.
`admit_trusted_stated` (SW-4734) is the form stage 3 will use (`leave_stated`, 10.5),
but it pushes a new definition rather than settling the one `signature` declared, and
the encoder refuses a definition with no body or group, so the digest couldn't be
computed without changing the encoder. The stand-in gives the same digest a stated
theorem would: for a sealed theorem the digest writes its name, path, flags, `unfolding`
references, type and the `sealed` mark, and references to it hash its statement
(`has_interface` holds for both). Nothing reads the stand-in: the digest skips sealed
bodies, other declarations see theorems through `computing_body`, and the pass is
rewound. It is still `admit_trusted_group` outside the cache's trust boundary, under a
debug switch: fine for measurement, not for stage 3.

`docs/proposals/parallel-checking/measure_interface_pilot.sh BINARY PROJECT OUT` runs it
over a whole project with a fresh cache and prints matches out of total, the differing
namespaces grouped by their set of causes, how many namespaces each cause touches, and
how many proofs were left out and how many elaborated anyway. About twice a cold check.

### 11.2 Results

**[measured]** A lane may not check a whole project, so `tools/fmt` was run on single
targets, each with its whole closure piloted: `Fmt.Kinds` (4 namespaces), `Fmt.SpellProofs`
(6), `Fmt.SpacingProofs` (27) and `Fmt.ElementsProofs` (102, which contains the others).
That is 102 of `tools/fmt`'s 150 namespaces, `Syntax` and `Fmt` included:

| | namespaces |
|---|---|
| match | 100 |
| differ: an `equation_skips` row (`t induct`) only the full check makes | 2 (`Syntax.ParseWalk`, `Syntax.FollowsBase`) |

Over those 102, the interface pass left out 3,301 proofs and elaborated 908 written
theorems' proofs anyway (recursive, mutual or `decreasing`): 22% of the written
theorems. The `Fmt.ElementsProofs` run took 77 s with both passes. The whole of
`tools/fmt` and `aoc` are the orchestrator's (the script).

A test project (the CLI test's, and a few more by hand) shows each cause that could be
written:

| Case | Result |
|---|---|
| a theorem proved by `byComputing`; one that uses another namespace's theorem | match |
| a `match` in a proof (the helper is proof-private since stage C) | match |
| a proof that names a library equation (`List.filter.eq2`) | match: the equations were already made when the library file loaded |
| a local `def` or `theorem` in a proof (`t.go`), not used elsewhere | differs: `proof-local-def` and `names` |
| the same, named from another declaration (`holder.go 1 = 2`, an `opaque def` using it) | differs: the interface pass fails on those declarations (`E-UNKNOWN-FIELD`) and has no digest |

### 11.3 The causes, and what they mean for the design

1. **A rows-only by-product: `equation_skips` for a theorem whose proof turns out
   recursive.** `givesCommaListFrom` and `followsCommaListFrom` are proved by
   `byWalking`, whose elaborated proof calls the theorem itself. The source shows no
   recursion, so the theorem is checked alone, and `induct::no_equations` then records
   "no `t.induct`" because the body calls itself. The row is in the digest, keyed by
   the theorem. *Proof-private, and better removed:* a theorem never has equations or an
   `induct` (`generate_equations` says "a theorem's arms have no equations"), so the
   row only shapes the note on a `t.induct` someone writes. Don't record it for a
   theorem, or record it from the statement alone. A small fix (Sonnet); with it, the
   102 measured here would all match **[estimated: it is the only difference found]**.
2. **A local `def` or `theorem` in a proof.** It is a declaration of the namespace,
   with a name in scope (`t.go`), so it is in the interface, and the interface pass
   can't know it without elaborating the proof. Not seen in the 102 `tools/fmt`
   namespaces. Two ways out: (a) a **syntactic rule**: a theorem whose proof block
   contains a local `def` or `theorem` is not deferred (its proof is elaborated in the
   interface pass), which costs only those proofs and is decidable from the parse; or
   (b) make such declarations unnameable outside the proof, which would let them be
   proof-private like `%match` helpers, but changes what users can write (Matt's call,
   and it would break the "name it, refer to it as `owner.name`" advice, which is for
   definitions' local `def`s, not theorems'). Recommend (a).
3. **Equations made on demand, `unfolding` naming a helper, other tables.** Not seen.
   Equations made on demand would show as a full check with no digest (`namespace_parts`
   refuses a nested unit), which the cache already can't hold; an `unfolding` list can
   only name a proof's by-product through case 2. Every other table only one pass
   filled would be listed by the pilot: none was, in these runs.
4. **Theorems the interface pass elaborates anyway** (22% here). Recursion is known from
   the source graph, and a recursive theorem's statement doesn't depend on its proof
   either, so stage 3 could defer those too, leaving termination to the full check. The
   pilot didn't try it (the group path is separate); worth a second run before stage 3's
   gain is estimated, since those proofs otherwise stay on the interface chain.

So for stage 3 the interface can be made from statements alone with one small fix (1)
and one syntactic rule (2a), on what was measured. The whole-project runs may find more.

### 11.4 Round 2: recursive, mutual and `decreasing` theorems too (SW-4752, 24 Nov 2026)

Opus lane, on cause 4. `STITCHWORT_INTERFACE_PILOT_ALL=1`, beside
`STITCHWORT_INTERFACE_PILOT`, makes the interface pass leave out the proofs of every group
whose members are all theorems: a recursive theorem, a mutual group of theorems, and a
`decreasing` theorem (routed through the ordinary group path, so its measure isn't
elaborated and no `f.%step` or `f.%go` is made), each admitted with stand-in bodies as in
11.1. A group mixing definitions and theorems still has its proofs elaborated (counted as
`with-defs`): its definitions' bodies are interface. Each line now also gives
`deferred-by:` and `kept-by:` counts by kind of group (`lone`, `recursive`, `mutual`,
`decreasing`), and a "no `t.induct`" `equation_skips` row for a theorem (cause 1, which
SW-4751 removes) is reported as its own cause, `theorem-induct-skip`, so what is left once
that fix lands shows. The CLI test `interface_pilot_all_leaves_out_recursive_theorems`
covers one of each kind.

**[measured]** The same four `tools/fmt` targets as 11.2 (`Fmt.ElementsProofs` and its
closure, 102 namespaces, 80 s with both passes), and four AoC days with `decreasing`
theorems, each with its closure (`Aoc.Year2024.Day09.Proofs`, `Aoc.Year2024.Day24.Proofs`,
`Aoc.Year2021.Day16.Proofs`, `Aoc.Year2020.Day03.Proofs`; 12 namespaces in all, `Aoc.Common`
and `Aoc.Common.Proofs` included). "With SW-4751" is the same build with a scratch patch
that skips the row for a theorem in `induct::no_equations`, standing in for that fix:

| Kind of group | proofs left out | namespaces with one | of them match | with SW-4751 |
|---|---|---|---|---|
| `tools/fmt`, lone | 3,301 | 97 | 88 | 97 |
| `tools/fmt`, recursive | 587 | 72 | 63 | 72 |
| `tools/fmt`, mutual | 321 | 28 | 25 | 28 |
| `tools/fmt`, kept anyway | 0 (908 in round 1) | | | |
| AoC days, recursive | 43 | 4 | 0 | 0 |
| AoC days, mutual | 11 | 1 | 0 | 0 |
| AoC days, `decreasing` | 8 | 4 | 0 | 0 |

`tools/fmt` has no `decreasing` theorem. Over the 102 `tools/fmt` namespaces 93 match and
the other 9 differ only by `theorem-induct-skip` (`Syntax.FollowsBase`, `Syntax.ParseWalk`,
`Syntax.ParseWalkCalc`, `Syntax.ParseWalkFrame`, `Syntax.ParseWalkStatements`,
`Syntax.ParseKept`, `Fmt.AppHangProofs`, `Fmt.JoinProofs`, `Fmt.StandsProofs`); with the
SW-4751 stand-in all 102 match. Round 1's two were the `byWalking` theorems; the other
seven are recursive theorems whose rows round 1 didn't see because it elaborated their
proofs. Of the 12 AoC namespaces, the 8 without a `decreasing` theorem match; each of the
4 `…Proofs` namespaces differs only by its `decreasing` theorems' `%step` and `%go`
(proof-helper:%step, proof-helper:%go), with or without SW-4751: no table, name or other
declaration differs, and the namespaces' recursive and mutual theorems (43 and 11) are
not among the differences.

**What each kind's interface needs from its proof:**

1. **A recursive theorem: nothing.** Its statement is its signature's; the kernel's
   termination check (structural recursion in `define_group`) is the full check's, and a
   proof that fails it fails like any other proof (10.5's failed-proof case). The only
   by-product is cause 1's row, which SW-4751 removes. Theorems never get equations or an
   `induct`, so nothing else is made from the proof's recursion.
2. **A mutual group of theorems: nothing, the group's shape included.** The members are
   declared from their signatures before any body; the full check's
   `define_reference_groups` splits the group by the references the proofs really make,
   but the digest writes plain sealed theorems sorted by path, not by group, so the split
   doesn't show. All 28 + 1 namespaces with one agree.
3. **A `decreasing` theorem: its `f.%step` and `f.%go`.** The full check's
   `decreasing_definition` declares them as sealed theorems in the namespace, so the
   digest writes them like any other declaration. Their statements come from the
   signature and the measure alone (`f.%step (x: A) (%rec: …[auto decreasing: m y < m x]
   → B) … : B`, `f.%go (k: Nat) (x: A) … (h: m x < k): B`, `decreasing.rs`'s header), not
   from the proof, so the interface pass could make them; but no source can name them
   (no written name has `%`), and the elaborator code that builds their names
   (`{f}.%step` in `equations.rs`, `induct.rs`, `tailrec.rs`, `decreasing_measure`) is
   for definitions' equations, `induct` and running, which a theorem doesn't have. So they
   are proof-private by the argument C.1 makes for `%match` helpers. *Recommend:* the
   digest leaves out a sealed `decreasing` theorem's `%step` and `%go` (and what is lifted
   under them) as proof-private, after a check of every by-name lookup of `%step`/`%go`
   that they can't be reached from another declaration; then the measure isn't in the
   interface either, and the interface pass needn't elaborate it. The other way, declaring
   them in the interface pass from the statement and measure, keeps the measure on the
   interface chain for no reader. A small change (Sonnet, `digest_prep`'s candidates),
   **[estimated]** to make the 4 AoC namespaces match.

So, on what was measured, a theorem's interface needs nothing from its proof of any
kind, once SW-4751 lands and a `decreasing` theorem's helpers are proof-private: the
interface pass need elaborate no theorem's proof (with 11.3's rule 2a still applying to a
proof with a local `def` or `theorem`). For `tools/fmt` that moves the 908 proofs (22% of
its written theorems in these 102 namespaces) off the interface chain.

**Whole projects (the orchestrator's):**

```
cargo build --release -p stitchwort-cli    # on lane/SW-4752
cp target/release/stitchwort /tmp/sw-pilot2
STITCHWORT_INTERFACE_PILOT_ALL=1 docs/proposals/parallel-checking/measure_interface_pilot.sh \
    /tmp/sw-pilot2 tools/fmt /tmp/pilot2-fmt
STITCHWORT_INTERFACE_PILOT_ALL=1 docs/proposals/parallel-checking/measure_interface_pilot.sh \
    /tmp/sw-pilot2 aoc /tmp/pilot2-aoc
```

About twice a cold check each, as before. The script's new lines give, per kind of group, the proofs left out, the
namespaces with one, and how many of those match; `theorem-induct-skip` and
`proof-helper:%step`/`%go` in the cause list are the two known causes above.
