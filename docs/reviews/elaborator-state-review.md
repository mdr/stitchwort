<!-- External review of docs/reviews/elaborator-state.html, received 3 Nov 2026 (SW-1167). Verbatim. -->

# Stitchwort elaborator state: design review

## Overall assessment

**I support the architectural direction and would proceed with step 6, subject to tightening the undo-log semantics and resolving the ownership problem around nested library loads.**

The lifetime-based decomposition is a substantial improvement over the previous design. It addresses a genuine correctness problem, not merely code organisation.

In particular, I think three decisions are sound:

1. **Classifying state by lifetime.** Separating `Attempt`, `Decl`, `Unit`, `Tables`, `Session`, and `Caches` makes previously implicit assumptions explicit.
2. **Using compile-time exhaustiveness.** Destructuring components without `..` means new state must be considered by each mechanism. This is a good defence against the omissions that caused the existing cache bugs.
3. **Choosing mutable hash maps with undo logs.** Given your stack-ordered rewind requirements and benchmark results, this is a reasonable alternative to persistent data structures.

The evidence is also encouraging. Steps 1–5 are merged, differential tests pass, and the cache format was preserved across the table refactor. The reported memory costs of copying state provide a compelling reason to tackle step 6. Stitchwort elaborator state\_ de…

However, I see two architectural issues that deserve attention before implementing it:

- **Undo logs need an explicit lifecycle model**, particularly when language-server checkpoints, cache transactions, and nested library loads coexist.
- **`OwnedBy`'s ownership floor is not necessarily an ownership invariant.** If declarations from different units can be interleaved, checking an ID against a lower bound is insufficient.

I also see opportunities to strengthen the differential tests and benchmark methodology.

---

## Q1. Is an environment-level undo log sound?

**Yes, under the stated stack discipline. But the checkpoint lifecycle needs to be specified more precisely.**

The basic approach is sound:

- Each mutation records the previous value of its key.
- A mark records the current log position.
- Rewinding reverses mutations from that position onwards.
- The same mark remains usable after rewinding, provided subsequent mutations are logged correctly.

Nested library loading doesn't inherently break this. Nor does cancellation.

### Concern 1: Marks and transactions have different lifecycles

The design has at least three distinct uses of marks: retained language-server checkpoints, temporary cache-entry checkpoints, and checkpoints associated with nested elaboration.

A language-server checkpoint can survive indefinitely and be rewound repeatedly. A cache checkpoint generally needs to survive only long enough to construct an entry.

I'd make these different concepts in the API, even if they share the underlying logging mechanism.

In particular, specify what happens when a checkpoint is committed, discarded, or invalidated by rewinding to an earlier checkpoint.

Otherwise, it's easy to retain an invalid checkpoint and accidentally reuse a log offset that now refers to a different execution history.

**Recommendation:** Track checkpoint validity explicitly. Rewinding to an earlier checkpoint must invalidate checkpoints on the discarded branch, while preserving the target checkpoint itself.

### Concern 2: Log lifetime and memory growth

The document correctly identifies a contradiction between the assertion that command-line checks do not log and the proposal to use logging for cache deltas. Stitchwort elaborator state\_ de…

I'd resolve this with a simple rule:

**Retain undo history only as far back as the oldest checkpoint that might still be used.**

When no rewindable checkpoints remain, undo history can be discarded.

This matches the principle used in rustc: its inference undo log is cleared when the outermost snapshot is committed, because no earlier rollback remains possible. I checked this against rustc's implementation. [Rust Documentation](https://doc.rust-lang.org/nightly/nightly-rustc/src/rustc_infer/infer/snapshot/undo_log.rs.html?utm_source=chatgpt.com)

However, rustc consumes its snapshots. Stitchwort's retained, reusable language-server marks require slightly different lifecycle management.

For a command-line check, the undo log should normally be discarded after each successfully completed cache transaction, assuming no enclosing checkpoint requires it.

Otherwise, a normal check can accumulate an undo history for all 289 units, despite never needing to rewind.

### Concern 3: First-change tracking

The proposed `Logged<K,V>` stores an undo log, a `touched` set, and a `logging` flag.

One subtlety: **clearing `touched` after rewinding is essential**, because the next execution may change the same keys again.

A useful regression test is:

```text
x = 0
a = mark()
x = 1
b = mark()
x = 2

rewind(b)  // x == 1
x = 3
rewind(b)  // x must again be 1

rewind(a)  // x == 0
```

Also, check how `touched` is reset. If every mark clears a large hash set, the mark operation may no longer be O(1). A generation-based approach could avoid that, though it introduces its own bookkeeping.

### Concern 4: Logging and replay are not quite the same operation

The design says the undo log can supply the cache delta.

It can certainly identify the affected keys, but **the undo log itself contains previous values, not necessarily the values to replay**.

For example, if a key changes from `A` to `B` and is subsequently deleted, the cache must reproduce its final absence, not either historical value.

I'd treat the log as a *write-set index*. Encoding then reads the current value, or records a deletion, for each affected key.

This also needs careful treatment of nested library loads: mutations by an inner unit must not accidentally become part of the outer unit's cache entry.

Finally, all mutations must go through the logging API. Returning unrestricted mutable references, or storing mutable objects behind `Rc`, can permit changes that the log never observes. Rustc's `SnapshotVec` documentation explicitly warns about this class of problem. [Docs.rs](https://docs.rs/ena/latest/src/ena/snapshot_vec.rs.html?utm_source=chatgpt.com)

**Q1 verdict:** The algorithm is appropriate. I'd approve it after specifying checkpoint ownership, invalidation, log pruning, and write-set encoding.

---

## Q2. Is `OwnedBy`'s ownership floor correct?

**This is my strongest objection to the existing design.**

The ownership floor is only a valid ownership check when every declaration owned by the current unit has an ID above the floor, and no other unit's declarations do.

Nested library loading appears capable of violating the second condition.

Consider:

```text
Namespace A begins at DataId 100

  Library B loads
    B declares DataId 100

  A resumes
    A writes a row for DataId 100
```

The assertion accepts the write because `100 >= floor`.

But the row belongs to a declaration owned by B, not A.

There is a further issue in the code excerpt.

`OwnedBy::encode_since` partitions rows using `id < m.cut`, then checks:

```rust
if old.len() != m.rows {
    return Err(...);
}
```

**That check would not detect the example above.**

The row has an ID greater than or equal to the cut, so it's classified as new. The count of old rows is unchanged.

The document suggests that the encoder would reject this write, but the shown code doesn't establish that. There may be another validation elsewhere; none is included in the excerpt. Stitchwort elaborator state\_ de…

There's another limitation: comparing the number of old rows cannot detect changes to their values if their count stays the same. The ownership assertions may make such changes impossible through the intended API, but the count check isn't an independent safeguard.

### Should the floor move after nested library loads?

Only if you can guarantee that all library loading finishes before the namespace allocates any of its own declarations.

Otherwise, moving the floor creates the opposite problem: the namespace could be prohibited from updating its own earlier declarations.

### My recommendation

I'd distinguish *declaration ownership* from *declaration allocation order*.

An explicit unit identifier associated with declarations would give you a stronger invariant:

```text
owner(declaration) == current_unit
```

Ownership could be established when declarations are allocated, with `OwnedBy` checking that ownership on writes.

This is stronger than a numerical floor and continues to work if declarations from different units are interleaved.

An alternative is to guarantee contiguous allocation by loading all dependencies before elaborating the namespace. That would be simpler, but it needs to be a genuine architectural guarantee.

Also, I agree that tables such as `instances`, where later units can change earlier rows, need a different classification. Their mutability is fundamentally different from `OwnedBy`.

**Q2 verdict:** Don't rely on the floor unless contiguous declaration ownership is guaranteed. As written, the invariant is weaker than its name suggests.

---

## Q3. Should the frozen library base come before step 6?

**No. I would implement step 6 first.**

The proposed undo logs address the immediate memory problem without fundamentally changing how tables are accessed.

A frozen library base introduces additional complexity: overlay lookups, shadowing, and the possibility of changing the behaviour of existing table operations.

The benchmark on page 17 supports your proposed ordering:

| Representation | 30,000 rows, 200 marks |
|---|---:|
| Copied `HashMap` | 341 MB |
| Persistent `imbl` map | 68 MB |
| Undo-logged `HashMap` | 7 MB |

These are standalone benchmark results, not measurements of the actual elaborator. Nevertheless, the difference is substantial. Stitchwort elaborator state\_ de…

A frozen base could still be valuable, particularly for sharing the standard library between sessions. The reported cost of repeatedly loading that library suggests a potentially larger optimisation opportunity.

But I'd treat that as a separate project.

One point to investigate: **Can the frozen library really be immutable?**

Some tables, particularly instance validity, permit changes to old rows. A frozen base would therefore need carefully defined overlay-shadowing semantics.

**Q3 verdict:** Step 6 first. Measure its effects, then evaluate frozen-base sharing independently.

---

## Q4. Is the differential oracle independent enough?

**Reasonably, yes. But I'd supplement it with targeted tests.**

The important distinction is between two classes of error.

**Incorrect encoding or replay**

Suppose a table correctly dumps its entire contents but incorrectly encodes only some of its changes.

A fresh session and a replayed session will have different contents, and the differential test should detect that.

Here, the independence of `Codec` and `Dump` is valuable.

**Incorrect classification or omission**

Suppose a field is incorrectly classified as derived state, or a new field is deliberately ignored by both mechanisms.

The compiler's exhaustive destructuring forces someone to make that decision, but cannot establish that the decision is correct.

Both the dump and replay can then omit something important.

The new architecture greatly reduces the chance of an *accidental* omission. It doesn't eliminate incorrect classifications.

### Recommended additional tests

I'd introduce a small state-machine test harness that compares `Logged` against a reference implementation using complete `HashMap` clones.

Generate sequences of operations involving inserts, overwrites, deletions, nested marks, repeated rewinds, commits, and invalid checkpoints.

This tests the undo-log implementation independently of the elaborator.

Separately, extend the existing differential tests with scenarios that exercise:

- Nested library loading with cache hits and misses.
- Cancellation at several points during elaboration.
- Repeated editing of an early namespace.
- Replaying a cache entry and then elaborating a dependent namespace.
- Mutations to previously existing table rows.

The fourth scenario is particularly valuable: it tests whether the state is actually usable, not merely whether its dump matches.

I'd also keep the cache-disabling test from step 4. It's a useful independent check of the `Derived` classification.

**Q4 verdict:** The oracle is adequate as one line of defence. Property-based tests for `Logged`, plus semantic differential tests, would provide substantially stronger confidence.

---

## Q5. What should you measure?

I agree with measuring resident memory and table sizes, but I'd prioritise **realistic incremental-editing workloads** over isolated mark benchmarks.

The user-facing benefit is improved language-server behaviour, not simply faster mark creation.

I'd measure four things.

### 1. Memory across editing sessions

Measure memory after initial indexing, after a full project check, and after 100–500 edit/recheck cycles.

Include edits near the beginning and end of the project.

Record both process RSS and the actual bytes retained by undo logs. RSS alone may obscure improvements because the allocator can retain freed memory.

The most interesting measurement is whether memory stabilises after repeated rewinds.

### 2. Incremental-check latency

Measure median and p95 latency for editing an early, middle, and late namespace.

An edit near the beginning should exercise a much larger rollback and recheck.

This matters because the standalone benchmark shows undo-log rewinds become slower as the number of changes increases, even though mark creation becomes cheaper.

### 3. Check-cache overhead

The new design introduces logging during ordinary cached command-line checks.

I'd explicitly measure cold checks, fully cached checks, mixed hit/miss checks, and cache-entry creation.

The anticipated 0.1–0.3-second saving from eliminating scope copies could be offset by additional bookkeeping on every map mutation.

You need a before/after measurement to establish the net result.

### 4. Undo-log statistics

Instrument log entries, distinct keys touched, peak log size, bytes retained, and entries undone per rewind.

These will help explain performance changes and identify pathological workloads.

**Q5 verdict:** Measure sustained memory behaviour and end-to-end incremental latency first. Microbenchmarks should help explain those results rather than substitute for them.

---

## Q6. Is persistence worth another look?

**Not as the general representation. Possibly for selected tables.**

The benchmarks provide a reasonable argument against replacing the elaborator's mutable state wholesale with persistent collections.

In particular, the difference between `Vec` indexing and persistent-vector indexing is significant for frequently accessed definitions and metavariables.

However, I wouldn't conclude that persistent maps are unsuitable everywhere.

Consider the distinction between the kernel's evaluator-facing definition store and the elaborator's name scope.

The former may have extremely hot indexed lookups. The latter might have a different read/write profile, where an additional few nanoseconds per lookup is acceptable in exchange for simpler checkpoint semantics.

The document's benchmark indicates that `imbl` is competitive for some operations, despite being slower on lookups. Its persistent collections also support copy-on-write updates, rather than copying every node on every mutation. [Docs.rs](https://docs.rs/imbl/latest/imbl/vector/index.html?utm_source=chatgpt.com)

I would retain persistence as a possible **per-table implementation choice**.

If the undo-log implementation proves complicated for a particular table, using an immutable representation for that table might be a reasonable engineering trade-off.

I wouldn't pursue that before seeing the results of step 6.

One limitation: the benchmark ran under substantial system load and shows considerable variability. Its broad memory comparison is persuasive, but I'd want more controlled measurements before making decisions based on relatively small lookup-time differences.

**Q6 verdict:** No architectural rethink necessary. Preserve the option to use persistence selectively.

---

## Additional concern: nested-unit cache semantics

There's one issue I'd investigate independently of `OwnedBy`.

The document says each cache entry captures what a unit contributed, but also allows library files to load while another unit is being elaborated.

Consider this sequence:

```text
Begin namespace A
  Mark A

  Elaborate part of A

  Load library B
    Mark B
    Modify global scope
    Finish B

  Elaborate remainder of A

  Encode A's delta since Mark A
```

A simple log-based delta includes changes made by B.

That may be correct if the cache deliberately represents the entire transitive effect of elaborating A.

But if B also has its own cache entry, you need a policy for whether those changes are duplicated, excluded, or represented as dependencies.

The excerpt doesn't establish which policy Stitchwort currently uses.

**I'd resolve this before using the undo log as the authoritative source of cache-entry deltas.**

Otherwise, you risk conflating two questions:

- What changed since this checkpoint?
- What changes belong to this compilation unit?

Those are not necessarily equivalent.

---

## Recommended decision

I wouldn't block step 6 on a frozen library base, a new state architecture, or a more sophisticated differential oracle.

I would, however, make three things prerequisites:

| Priority | Action | Reason |
|---|---|---|
| **Blocking** | Specify checkpoint creation, invalidation, commit, and pruning | Prevent incorrect restores and unbounded history |
| **Blocking** | Define how nested-unit writes are attributed to cache entries | Prevent incorrect replay deltas |
| **Blocking for relying on `OwnedBy`** | Resolve declaration ownership versus ID ordering | The current floor does not prove ownership |
| High | Add model-based tests for `Logged` | Catch rollback errors independently |
| High | Audit mutation APIs for unlogged changes | Ensure rollback completeness |
| High | Measure sustained LSP memory and check-cache overhead | Verify the optimisation delivers its intended benefit |

The remaining concern is the unfinished `Globals` split. Until that's complete, the lifetime refactor hasn't established its invariants across the entire elaborator. That's an acknowledged limitation rather than a reason to stop step 6.

### Final verdict

**Approve the overall architecture, conditionally approve step 6, and revisit `OwnedBy` before treating its ownership guarantee as established.**

I particularly like the decision to make state policies explicit without introducing a runtime table registry. For a compiler with a fixed set of tables, exhaustive Rust pattern matching is an effective approach.

The most important insight from this review is that **undo-log correctness and cache-delta correctness are separate problems**. An undo log can perfectly restore a previous state while still being insufficient to determine which changes belong in a particular cache entry.

Getting that distinction right would be my principal focus before merging step 6.