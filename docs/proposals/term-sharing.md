# Big terms: sharing, limits, and where memory runs away (SW-2660)

Status: design note, for Matt's decisions (three questions in [§7](#7-questions-for-matt)).
Written by Fable, 10 Nov 2026, against `main` at `4a617cdb8`. A paper lane: nothing was
built. Probes used the release CLI already built from `main` (binary of 10 Nov 09:47, which
includes SW-2600), with `check --no-cache` and `/usr/bin/time -l`.

Labels: **measured** (run for this note), **cited** (from the ticket or note named),
**estimated**, **inferred** (my reading of the code, not run).

## In short

- **The problem.** A check can use gigabytes before any limit stops it. The fuzzers found
  about ten such cases in three days, each at a different place in the code, and I found two
  more in five minutes of probing for this note (§2.3).
- **The cause is not one thing.** Only about a fifth of the incidents come from a shared value
  being written out as a tree. The rest are numbers unfolded to `Succ` chains, deep recursion
  that keeps something per level, and genuinely large unfolded goals. Sharing in terms would
  fix the first group only.
- **What every incident has in common:** memory grew where no counter was looking. Today's
  limits count steps, frames and the nodes of one read-back. Nothing counts memory.
- **Recommendation.** Keep terms as trees. Add one limit that sees everything: a memory budget
  for each check, measured at the allocator, as a backstop. Lower the read-back limit from
  10 million nodes to 1 million (D3464). Finish bounded read-back, which is already decided
  and removes the largest group at its root. Don't build shared (DAG) terms now: weeks of
  work in and around the kernel, for the smallest group.

## 1. The incidents

Grouped by what actually grew. All cited from the tickets unless marked.

| Group | Incident | What happened |
|---|---|---|
| **A. A shared value written out as a tree** | SW-2409 (done) | `rename` wrote `grow n (Node t t)` out with no limit: fuzz run killed at 16.6 GB |
| | SW-2512 (done) | 20 chained `let`s substituted into 2^20 nodes by the equation generator: out of memory |
| | `rewrite-value-too-large.sw` | stops at the 10M-node limit, after 1.32 GB (**measured**) |
| **B. A number unfolded to a `Succ` chain** | SW-2467 (in review) | `Fin` pattern `2^128`: 11+ GB in 15 s |
| | SW-2580 (done) | `Vec a 2^128` index: 10.5 GB |
| | SW-2123 (backlog) | the same family, minutes of time |
| **C. Deep recursion that keeps something per level** | SW-2639 (doing) | `decreasing` keeps 3 KB per level: 3.3 GB at the 2M-frame limit |
| | SW-2483 (backlog) | `settle 2^128`: 8 s to reach the depth limit |
| | by design | `length (replicate 1000000 1)` peaks at about 750 MB (`budget.rs:94`) |
| **D. A large unfolded goal or value, no sharing lost** | SW-2576, SW-2606 (done) | `cases` copied a 3.9M-node goal: 7 GB |
| | SW-2470, SW-2569, SW-2598, SW-2600 (done) | error notes read both sides back to the limit: 2 to 3.8 GB for 240 characters of text |
| | SW-1740 (record) | trip-journal under record eta: 33 declarations each reached 10M nodes unfolding `Float` arithmetic |
| | SW-994, SW-985, SW-1709 | `cases` and `match` on library arithmetic: 1.2 GB each |
| **E. Looked like a leak, was one case** | SW-2449 (backlog) | flat at 0.8 to 1.0 GB with spikes from single mutants; the spikes were SW-2576 |

Group A is 3 of about 15. Sharing throughout (option 1) addresses group A. It does nothing
for B and C, where the value itself is huge, and little for D, where the tree is honestly
that big.

## 2. How it works today

### 2.1 Terms, values and the bridge between them

- **Terms are trees.** `Term` is an enum whose children are `Rc<Term>`
  (`crates/core/src/term.rs:161`). Nothing interns or hash-conses them. Two terms can share
  a child in memory, but every pass treats a term as a tree.
- **Values are shared.** `Value` (`crates/core/src/value.rs:22`) holds its parts through
  `Rc`: constructor fields, spines, closures. A folded call keeps its unfolding in a memo
  cell that every copy shares (`Value::Call`, `Unfolding`, `value.rs:262`). `grow 30 (Leaf x)`
  is 31 cells as a value.
- **Read-back is the bridge, and it copies.** `quote_as` (`value.rs:2986`) walks a value and
  builds a fresh term. It doesn't remember shared parts it has seen, so those 31 cells become
  2^31 nodes. It counts nodes as it goes and stops at the size limit (`value.rs:3005` to
  `3022`).
- **Solutions go through the bridge twice.** The unifier solves `?m xs = v` by writing `v`
  as a term (`rename`, `crates/elab/src/unify.rs:2376`, limited since SW-2409), wrapping it
  in lambdas and evaluating it again (`solve`, `unify.rs:2294`). Zonking reads solutions
  back (`zonk_in`, `unify.rs:2870`).
- **The kernel walks trees and rebuilds them.** `infer` and `check`
  (`crates/core/src/check.rs:233`, `:425`) return the term they checked, built node by node.
- **Hashing walks the tree.** One BLAKE3 stream is fed each node, then its parts, left to
  right (`crates/core/src/hash.rs:530`).
- **Two parts already keep sharing.** The check cache writes a shared sub-term once and reads
  it back shared (`crates/elab/src/cache/codec.rs:4`). Conversion remembers pairs of *calls*
  it has compared (`value.rs:4336`).

So the design is already "small terms as written, big values shared". The leaks are where
something turns a big value into a term.

### 2.2 The limits

All set in one place, `Limits::for_stack` (`crates/core/src/budget.rs:117`). The browser uses
the same numbers, with a smaller stack (`crates/web/src/lib.rs:43`).

| Limit | Value | Counted where | The user sees (`E-RESOURCE`) | Same on native and wasm? |
|---|---|---|---|---|
| Steps | 10^10 per operation | `Budget::step`, at each evaluation, conversion and read-back step (`budget.rs:632`) | "it took more evaluation steps than allowed" | yes |
| Frames | 2,000,000 | the evaluator's pending work (`value.rs:1438`) | "it recursed more deeply than allowed" | yes |
| Size | 10,000,000 nodes | one read-back (`quote_as`) or one `rename`; not a total for the check | "a value was too large to show" | yes |
| Stack | bytes, 3/4 of the thread's | `Budget::nesting`, each level of a recursive pass (`budget.rs:671`) | "nested too deeply for the *pass*" | **no**: differs by build |
| Native frames | 16,000,000 | native runs only | "recursed more deeply" | native only |
| Deadline, cancel | set by the host | every 2^14 steps | search only; never shown or cached | n/a |

Beside these there are about a dozen local caps, each added for one incident, with eight
different values: 4,096 (`KNOWN_CAP`), 8,000 and 40,000 (messages), 65,536 (`READ_CAP`),
100,000 (`cases`' atoms, instance scans, statements), 200,000 (notes, search's proofs),
1,000,000 (`cases`' split), and 64 (`Fin` patterns, unmerged).

**What nothing counts:** memory. Also the nodes built by anything other than `quote_as` and
`rename`: substitution, match compilation, equation generation, the deriving code.

**What the limits cost when reached** (**measured**, release, an empty file is 80 MB):

| Case | Time | Peak memory |
|---|---|---|
| `rewrite-value-too-large.sw` (size limit) | 1.3 s | 1.32 GB |
| `rewrite-solution-too-large.sw` (size limit) | 1.9 s | 2.23 GB |
| `innerN 2^128` (frame limit; cited, SW-2639) | 4.8 s | 3.31 GB |

That's 125 to 215 bytes per node of read-back. The step limit is no bound on memory or
patience: at about 11 million steps a second (**measured** on the first row), 10^10 steps is
about 15 minutes.

### 2.3 Two new findings from probing

With `grow` as in `rewrite-value-too-large.sw` (all **measured**):

1. **A wrong `rfl` on shared values costs 1.31 GB.**
   `theorem wrong (x: Nat): grow 30 (Leaf x) = grow 29 (Leaf x) := rfl` gives the right
   `E-REFL` after 4.3 s and 1.31 GB. The note it prints is
   `Node (Node (Node (Node … …) …` cut short. So a note's read-back still runs to the 10M
   limit (**inferred** from 41 million steps and the memory), after four tickets capping
   notes.
2. **A true `rfl` between two shared values takes exponential time.**
   `grow n (Leaf x) = grow (n-1) (Node (Leaf x) (Leaf x))` by `rfl` holds, and memory stays
   at 82 MB, but conversion compares the two sides as trees: 394,296 steps at n = 16,
   6,292,744 at 20, 25,167,216 at 22, which is 6 × 2^n. At n = 30 that's 6.4 × 10^9 steps:
   under the step limit, so it would pass after about ten minutes (**estimated**; it was
   still running at the 60 s stop). Conversion's memo covers pairs of calls, not pairs of
   constructor cells.

Both are worth tickets. The second shows that sharing is lost in time as well as in memory.

### 2.4 How close real code comes to the limits

**Measured**, with `STITCHWORT_TIMINGS=decls`, uncached: all of std (4,573 declarations),
seven AoC proof namespaces chosen for size or history (2020 days 17 and 18; 2021 days 13 and
16; 2024 days 12 and 15; 2025 day 2) and `Rogue.Proofs`: 1,490 project declarations, counting
what those import.

| | Largest seen | Limit | Headroom |
|---|---|---|---|
| Steps in one declaration | 9,767,739 (`Rogue.Proofs.resolveOutOfWalls`); std's most is 9,033,732 | 10^10 | 1,000× |
| Nodes in the term a declaration ends up as | 105,898 (the same one); std's most is 93,242 | 10M per read-back | about 100× |
| Peak memory of the whole run | 323 MB (2021 day 16, with 4,481 declarations loaded); all of std is 278 MB | none | |

Not measured, because no counter exists: the largest single read-back and the deepest
frames in a real check. From the memory figures, no read-back in the sample can have been
much over half a million nodes (**estimated**: about 50 to 100 MB above what the loaded
declarations hold, at 125 bytes or more per node). A whole-AoC run wasn't done (test budget).
Bounded read-back's stage 0c planned exactly this counter and hasn't been built.

One real project has reached the size limit: trip-journal, on the record-eta branch, in 33
declarations (cited, SW-1740). All 33 were failures. A lower limit would have given the same
answer sooner.

## 3. Option 1: sharing throughout

**End state.** No pass ever turns a shared value into a tree. Three ways to get there:

- **(a) Terms as DAGs, with memos.** Read-back remembers shared cells (by address and binder
  depth) and returns the same `Rc<Term>` for them. Then every pass over terms needs its own
  memo to stay linear: evaluation, the kernel's `infer` and `check` (which rebuild the term
  today), substitution and shifting, zonking, hashing, printing, termination and positivity
  checks, lowering for the runtimes. One pass without a memo and the saving is gone, in time
  if not in memory (§2.3, finding 2).
- **(b) Hash-consing.** As (a), plus a table so equal terms are one object. Memos get stable
  keys and equality is one comparison. This is what Lean and Rocq do. Each `Term` node gains
  a header (a hash, and the range of free variables, which de Bruijn indices need before
  evaluation can be memoised).
- **(c) Explicit sharing with `let`.** Read-back emits `let s := shared part` instead of
  copying. The kernel has transparent `let` already, so it, the hash, the cache and
  extraction need no change. But every search then sees `let`s where it expected
  constructors, and anything that substitutes them back is exponential again. That's what
  SW-2512 was.

**The hash.** Yes, there's a design where the hash stays a function of the tree and is
computed over the DAG: hash each node as `H(tag, own fields, the hashes of its children)`,
and remember the hash of each shared node while one declaration is being hashed. Equal trees
give equal hashes however they're shared, and the cost is the size of the DAG. Details that
work out: a location wrapper hashes as what it wraps; a reference to the declaration itself
is a marker, so the memo must not outlive one declaration's hashing; the memo must hold the
nodes it remembers, so an address can't be reused under it. It isn't today's hash (one
stream over the whole walk), so every hash changes once. It costs about one BLAKE3 block per
node, where today's stream packs several nodes into a block (**estimated**: hashing gets a
few times slower; it's a small part of a check).

**The cache** already keeps sharing. **Printing** already cuts off at 20,000 nodes
(`pretty.rs:445`). **Extraction** would need memos like every other pass.

- **Soundness risk: the highest of the options.** For (a) and (b) the kernel gains memos in
  `infer`, `check` and evaluation, keyed by address. A wrong hit there accepts a wrong term.
  The kernel is small today because it is a plain recursive walk over a tree. (c) has no
  kernel risk.
- **For users:** group A becomes fast instead of an error. Nothing else changes.
- **Work (estimated):** (a) or (b): `Term` is matched or built at about 480 places in 56
  files across `core`, `elab`, `rt` and `js` (**measured** by grep for two of its variants,
  so a floor). Three to five weeks of Opus lanes, with reviews of every kernel change. (c):
  one to two weeks, mostly in the searches. The Merkle hash alone: two days.
- **Rules out later:** nothing. But it commits the kernel to caches for good.

**Verdict.** It fixes the smallest group. And the direction already chosen makes that group
smaller still: under bounded read-back (D2541 to D2545) the elaborator works on goals as
written, and "computing decides", so big things live as values, where sharing is free.
Stitchwort has no `simp` (D2541) and so no large machine-made proof terms, which is what
DAG terms are for in Lean. If that changes, this option comes back.

## 4. Option 2: limits as policy

**End state.** Each check has one resource model, set in one table, where each limit says
what it counts, what it costs at most, and what the user is told.

| Limit | End state | Why |
|---|---|---|
| Steps | 10^10, unchanged | 1,000× over the largest real declaration. Bounds time only. A lower limit for checking alone needs data on `rfl` examples first. |
| Frames | 2,000,000, unchanged | Programs need deep recursion. Its cost per frame is SW-2639's question (D3474). |
| Read-back size | **1,000,000 nodes** (D3464) | 125 to 215 MB at the limit instead of 1.3 to 2.2 GB (**estimated** by scaling §2.2). About 10× the largest term in the sample. The fuzzers already run at 1M (SW-2582); `cases` already splits at 1M (SW-2606). |
| **Memory** | **new: 1 GiB that the check has added since it started** (512 MiB in the browser) | The only limit that sees every allocation, whichever code made it. |
| Stack | unchanged | |
| Local caps | named in the same table, in three sizes (display, search, decide) | Eight values today. |

**The memory budget, concretely.** The fuzzers already have it (SW-2582,
`crates/driver/tests/support/heap_cap.rs`): an allocator wrapper counts each thread's live
bytes, and the budget's existing poll (every 2^14 steps) stops a check over the cap. The
proposal is to put the same thing in the product: in the CLI, the language server and the
browser build, outside `stitchwort-core`. The check stops with
`E-RESOURCE: ran out of resources: checking needed more than 1 GiB of memory`, naming the
definition being unfolded, as the frame error does. Cost: an add and a subtract on each
allocation (**estimated** 1 to 3% of checking time, cited from SW-2639's review).

A second, hard cap (say twice the budget) covers a loop that allocates without taking a
step: the allocator refuses, and the process ends with "out of memory checking `t`" instead
of taking the machine down. In the browser the page restarts its worker.

**The objection, and the answer.** SW-2639's review rejects a memory cap: bytes differ
between native (8-byte pointers) and the browser (4-byte), so a check near the cap could
pass in one and fail in the other. That's true, and it's why this is a backstop and not the
limit users normally meet. Three points:

1. **It's already so.** At the margin today, whether a check finishes depends on the
   machine: the fuzz run with SW-2467's case in it passed on the laptop, peaking at
   11.45 GB, and the same case was killed at 11.6 GB on the 15 GB server (cited). The
   browser has a hard wall at 4 GB or less, with a crash and no message (cited, SW-2639's
   review). A budget replaces a crash that depends on the machine with an error that
   depends on the build.
2. **There's precedent in the design.** The stack limit is in bytes and differs by build
   (`budget.rs:314` to `325`). Its rule carries over unchanged: running out is "no answer",
   never "no"; an attempt passes it on instead of choosing another path, so it can't change
   *which* term is elaborated. And only namespaces without errors are cached (D284), so it
   never reaches a cache.
3. **It's far from real use.** 1 GiB of growth in one check is three times the peak of a
   whole run over 4,481 declarations (§2.4). The browser's 512 MiB is the same amount of
   work, since its values are about half the size (**estimated**).

The deterministic limits stay the ones a user meets first. D3474 (the `decreasing` encoding)
is right whatever is decided here: it removes a cost, where a budget only stops one.

- **Soundness risk: none.** Nothing in the kernel's rules changes. A check stops or it
  doesn't.
- **For users:** runaway checks end in seconds with an error, on the laptop and in the
  playground. A valid check that needs more than the budget is refused; none is known.
- **Work (estimated):** the size limit: an hour, plus one whole-corpus run to confirm
  (std, AoC, the roguelike, examples; a verifier job) and snapshot churn. The memory budget:
  one Opus lane for the mechanism (it touches `budget.rs`), one Sonnet lane for the three
  hosts, examples and docs. The counter for read-backs and frames (stage 0c): one Sonnet
  lane.
- **Rules out later:** nothing. If DAG terms arrive, the limits stay as they are.

## 5. Option 3: targeted fixes, as today

**Is it converging? No.**

- About ten new runaways in three days of fuzzing (8 to 10 Nov), each at a different site:
  `rename`, the equation generator, `Fin` patterns, index unification, `cases`' atom search,
  `cases`' split, four rounds of error notes, the `decreasing` chain.
- The elaborator has about 400 calls that read a value back with no cap of their own (about
  190 of them fully unfolded), and 17 with one (**measured** by grep, tests included;
  SW-1747 classified 288 sites on 6 Nov). Each is bounded only by the 10M limit, which is
  1.3 to 2.2 GB.
- Two more turned up in five minutes of hand probing (§2.3).
- The fixes have costs of their own. SW-2467's cap of 64 `Fin` patterns refuses a 256-arm
  table that checks today. SW-2512's cap drops some equations. Each adds a constant.

**But targeted fixes are still the right tool for one kind of finding:** a small, valid
program that's slow or large because of an algorithm. Numbers must stay numbers (group B).
A budget turns a `Fin 1000` table's crash into an error; only the fix makes it check.

So keep fixing, but change what counts as a finding. With a budget, a fuzz case that ends in
`E-RESOURCE` inside the budget is a pass. A real program that hits the budget is a ticket.

- **Soundness risk:** low each time, but fixes land in the unifier and tactics, and
  sometimes in the kernel's index unification (SW-2580), under time pressure from a fuzz
  queue.
- **Rules out:** nothing. It just doesn't end.

## 6. Recommendation

**Limits as policy, with a memory budget as the one limit that can't be walked around; the
work already decided to shrink read-back; and no DAG terms.** In order:

1. **Measure** (one Sonnet lane): per declaration, the largest read-back and the deepest
   frames, over the whole corpus. This is bounded read-back's stage 0c, and it confirms the
   next step's number.
2. **Lower the size limit to 1M nodes** (D3464), and say what it is in the message.
3. **Add the memory budget** (question 2), and make the fuzzers' oracle "ends inside the
   budget".
4. **Carry on with bounded read-back** (decided, D2541 to D2545). It removes group D at the
   root: searches stop unfolding goals at all.
5. **Fix group B and C by algorithm** as real programs need them: SW-2467's numeric `Fin`
   patterns, D3474's `decreasing` encoding.
6. **Two cheap pieces of sharing, in the elaborator only:**
   - conversion remembers pairs of shared constructor cells it found equal, as it does
     calls (§2.3, finding 2). This is kernel code, so an Opus lane with a review;
   - walks that only *look* at a value (does it mention this unknown, is it in scope) visit
     a shared cell once. Bounded read-back's stage 4a reader (SW-1832) is the place.
7. **Not now:** DAG terms, hash-consing, the Merkle hash. Close SW-2418's audit as
   superseded: the budget covers what an audit would miss.

**Why not the better-sounding option.** Sharing throughout is the textbook answer and I
looked for a reason to recommend it. The incidents don't support it: 3 of 15, and those 3
end in a clean error today. It would put caches in the kernel, which is the one place
Stitchwort has kept simple.

## 7. Questions for Matt

Numbers other than D3464 are for the orchestrator to assign.

**D3464: lower the read-back size limit from 10 million nodes to 1 million?** Reaching it
would cost about 0.2 GB and 0.2 s instead of 2 GB and 2 s (estimated). The largest term in
std and the sample is 106,000 nodes (measured); the confirming run over the whole corpus
comes first, and if it finds a real read-back over 250,000 nodes the number is looked at
again. The message becomes "a value was too large to write out (over 1,000,000 parts)",
since "to show" is wrong for a `rewrite`. **[rec: yes]**

**Question 2: a memory budget for each check, as a backstop?** 1 GiB of growth (512 MiB in
the browser), `E-RESOURCE`, not the same number of values on every build, as the stack limit
isn't. This goes against the recommendation in SW-2639's review, for the reasons in §4; its
D3474 stands either way. With it, a fuzz case that stops inside the budget counts as a pass.
**[rec: yes]**

**Question 3: leave terms as trees for now?** No DAG terms, hash-consing or new hash until a
real program needs them, or until Stitchwort grows automation that writes large proof terms.
SW-2418's audit closes; the two small pieces of sharing in §6 item 6 go ahead as ordinary
lanes. **[rec: yes]**

## 8. Findings to file

- A wrong `rfl` between shared values reads a note back to the 10M limit: 4.3 s, 1.31 GB
  (§2.3, finding 1). Repro in §2.3.
- A true `rfl` between two differently built shared values is exponential in time: 6 × 2^n
  steps (§2.3, finding 2).
- No counter for the largest read-back or deepest frames per declaration (stage 0c).
- `E-RESOURCE`'s "a value was too large to show" is misleading when nothing is being shown.
- SW-556 (the old goal read-back cap) is still in the backlog though superseded (already
  noted in the proposals index).
