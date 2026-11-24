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
