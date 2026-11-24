# Check-cache keys by interface digest (SW-4706)

Design for stage 3 of [sealed-theorems.md](sealed-theorems.md) (section 3.9), decided by Matt
as D3728 (23 Nov 2026): design on paper first, then build on Opus (SW-4707). Paper lane: code
read, nothing built or run. Each claim is marked **[verified]** (code, with file:line as of
`435258a1b`), **[measured]** (by someone else, cited), **[estimated]** or **[not verified]**.

## Summary

**The problem.** A cache entry's key covers the unit's text and the *keys* of everything it
depends on, so an edit anywhere re-checks everything above it. Since full proof irrelevance
(D3722) no declaration can see a theorem's proof, so most of that re-checking can't find
anything new.

**The change.** A namespace's key covers its own text and, for each namespace it depends on,
an *interface digest*: a hash of everything that namespace's cache entry holds *except* the
proofs of its theorems and source positions. The digest is made when the entry is written and
stored in it. If the edited namespace's digest comes out the same, every namespace above it
has the same key as before and is loaded from the cache.

**What it should do.** Editing the proof of `spellsNil` in `Fmt.SpellProofs` (32 namespaces
import it directly **[verified, grep of `tools/fmt/src`]**) re-checks 1 namespace, about 0.6 s
of checking **[measured: 513.7 ms elaboration + 94.4 ms kernel,
`parallel-checking/fmt-units-22nov-pm.csv`]**, plus a replay of the rest, 2 to 4 s **[measured
for a whole-project replay, parallel-checking.md summary]**; today it re-checks that namespace
and everything above it **[estimated: tens of seconds; SW-4707 measures before and after]**.

The design in five rules:

1. **Default-include.** The digest is a second stream written by the entry encoder: every
   write to the entry also goes to the digest, minus a short, named list of exclusions. A
   table added to entries later is in the digest without anyone remembering it.
2. **Three exclusions**: the body of a sealed theorem (exactly `hash::has_interface`), source
   spans, and the entry's own messages and navigation. Nothing else.
3. **A digest exists only for a namespace that was written to or replayed from an entry in
   this session**: fully checked, no errors, no goals. Any other dependency contributes its
   *text key*, as today. So the new scheme is never less careful than today's for anything
   unfinished.
4. **Positions**: an entry that holds a raw position in another unit's file also records that
   file's text hash and misses when it changes (the mechanism `include` files use today).
5. **Reliance is never cached**: which goals and axioms a result relies on stays a walk over
   the live proofs at report time, as SW-4701 left it.

Stages: **A** project namespaces (the measure above; **built**, SW-4707: see "As built
(stage A)" at the end); **B** standard library files; **C**
leave out helpers that only a proof can reach, so edits that add or remove a `match` inside a
proof also cut off (**built**, SW-4714: see "As built (stage C)" at the end); **D** (Matt's decision, section 7) a namespace with an open goal inside a
proof keeps its digest, so working on a `?` doesn't re-check what's above it.

## 1. The end state

### 1.1 Today

- A namespace's key: format, modes, name, the host's hash of its sources, and for each
  namespace in its transitive closure, that namespace's **key** **[verified,
  `crates/elab/src/cache/mod.rs:862-894`; the closure is transitive,
  `crates/driver/src/project.rs:1164-1176`]**. The source hash covers the namespace's files'
  names and text, the names of all the project's namespaces and `stitchwort.yaml`
  **[verified, `project.rs:727-760`]**.
- A library file's key: format, modes, path, text, and the keys of the files it needs
  **[verified, `mod.rs:515-546`]**. A namespace's entry lists the library files in its reach
  (its own needs and its dependencies') with the key each had, compared before replay
  **[verified, `mod.rs:1152-1165`, `758-772`]**.
- Every entry's stamp holds the library's index of names, which name resolution reads
  whatever is loaded **[verified, `mod.rs:817-846`]**.
- An entry's header lists each outside declaration it refers to with its **full** hash
  (`def_hash`), compared on replay **[verified, written `mod.rs:1303-1327`, compared
  `mod.rs:2797-2812`]**. So even with a better key, a proof edit below would miss here.
- An entry is written only for a namespace with no error, no goal diagnostic, no declaration
  left unfinished and no dependency that failed **[verified, `mod.rs:976-1012`]**.

### 1.2 The key

For a namespace `N` with closure `C`:

    K(N) = H("ns", FORMAT, modes, N, sources(N), [(D, G(D)) for D in C])

    G(D) = ("digest", digest stored in D's entry)   if D was replayed from, or written to,
                                                    an entry in this session
         = ("text", K(D))                           otherwise

`G(D)` is known when `N` is reached because namespaces are checked in dependency order. A
namespace that failed has no `G`, so nothing above it has a key, as now (today the same
effect comes from `failed_namespaces`, `mod.rs:988-998`).

The entry's dependency records change from `def_hash` to `interface_hash` for definitions
(`mod.rs:1313` and `2801`): a theorem below is then "what the entry was made with" as long as
its statement is.

### 1.3 The digest, exactly

`digest(D) = H(the digest stream of D's entry)`. The stream is the entry's content in the
encoder's order (`Elaborator::encode`, `mod.rs:1782-2250`) with these rules:

| Part of the entry (where written) | In the digest? | Why |
|---|---|---|
| Needs: library files, dot names, equations (`1864-1875`) | **yes** | they make the namespace's library *reach*, which decides which instances and `auto` candidates a dependant sees (`session.rs:79-82`; `mod.rs:1152-1160`). A proof edit that starts using a new library file changes the reach, so it must change the digest |
| Library files with keys (`1876-1880`) | no | each dependant records and compares the reach's files itself (1.5) |
| `include`d files' hashes (`1881-1885`) | no | their content is in the bodies that read them |
| Names: early, late, changed, members (`1886-1897`, `2041-2063`) | **yes**, without spans | name resolution |
| Warnings (`1898-1914`) | no | the namespace's own messages; see section 3 |
| Each definition: name, path, theorem, instance, fold, opaque, tailrec, `unfolding` list, type, group, run body (`1918-1955`) | **yes** | |
| Its body (`1937`) | **yes**, unless `has_interface(id)`: a final theorem with a proof (`crates/core/src/hash.rs:235-238`) | a computing definition's body computes; a sealed theorem's is never read (2.1) |
| Its span (`1935`) | no | 1.4 |
| Data types: all of each (`1956-2021`) except the span | **yes** | |
| Built-ins bound (`2025-2030`) | **yes** | (library files only; a namespace that binds one isn't cached) |
| Every side table (`Tables::encode_since`, `state/tables.rs:366`, called at `2067-2070`), and the extensions (`2252-2267`) | **yes**, without spans | the list is below |
| Navigation (`2072-2223`) | no | positions in the unit's own files, read by the editor from the unit's own entry |
| References to outside declarations | by path and `interface_hash` | as the entry's own dependency records, after 1.2 |
| References to its own declarations | by position in the entry | stable for a given content |

The side tables, all of them **[verified: the list is `Tables`, `state/tables.rs:44-135`]**:
tests, abilities (effects and their operations), lifted `match` helpers, equation skips,
equations made on demand, records, interfaces, data types' owners, the five "why it isn't
derived" notes (`==`, `show`, `compare`, `Finite`, decision), generated `All`s, match columns,
`@[reading]` theorems, total rows, `rules` sets, `@[walk]` tags, field defaults, parameter
defaults, update printing, JS representation, instances, local definitions' keys. All are in
the digest by rule 1. (`unfinished_defs` and `unfinished_datas` are never in an entry;
`namespace_defs` is rebuilt by replay.) I found no table for coercions or notations, and
entries hold no doc text; doc-link warnings are recomputed on every replay **[verified,
`mod.rs:930-935`]**.

Using the single predicate `has_interface` (made `pub`) for "is this body left out" keeps the
digest and the hashes from drifting apart: a body is left out of the digest exactly when
references to the declaration hash as its statement alone. So a `def` whose type is a
proposition, a theorem in a group with a computing definition, a `?` and a failed proof's
stand-in all keep their bodies or own hashes in the digest, as SW-4701's "As built" note says
they do in hashes.

**Where it is computed and stored.** In `encode`, as it writes the entry: the `Encoding`
gets a second writer, and each exclusion is one explicit "entry only" call. The 32-byte
result goes in the entry's sealed header beside the stamp (`Stamp`, `mod.rs:282-291`; `seal`,
`mod.rs:2270`). On replay and in `plan_namespace` it is read back, not recomputed
(recomputing needs a full decode). `check --recheck` recomputes it and compares (section 2.4).
Entries are byte-for-byte reproducible across processes and orders **[measured,
parallel-checking.md's 22 Nov addendum: 258 entries identical]**, so the digest is stable; if
it weren't, the cost would be extra misses, never a wrong hit.

### 1.4 Positions

A proof edit usually changes the proof's length, which moves every later declaration in the
file. If positions were in the digest, there would be no cut-off; so they are out. That is
only right if no entry above holds a position inside the edited file that it would hand back
stale. Entries hold positions in three places: definition and name spans (the unit's own
files), `Loc` nodes inside terms, and navigation targets and warning labels, which can point
into another unit's file. Navigation already stores a target in another unit's file *by the
name of its declaration* when the target is that name's declared position, and looks it up
at replay **[verified, `mod.rs:2088-2096`]**; anything else is stored raw.

Rule: the encoder already builds the table of files the entry's spans fall in
(`Out::file_index`, `mod.rs:1373`). For each file in that table that is not one of the unit's
own, the entry records the file's text hash, and replay and `plan_entry` compare it, exactly
as `includes_unchanged` does (`mod.rs:775-790`). Such an entry misses when that file changes
at all: today's behaviour, for that entry only.

How many entries this catches is **[not verified]**: it is the first thing SW-4707 measures
(count entries of `tools/fmt` with another unit's file in their file table, with and without
navigation). If it is more than a few, the kinds of raw target found are converted to
by-name, as declarations' are.

### 1.5 Library files (stage B)

The same shape: `K(f) = H(format, modes, path, text(f), [G(e) for e in edges(f)])`, and a
namespace's entry lists `(file, G(file))` for every file its reach can load, transitively
(the edges are static, from the index), instead of `(file, key)`.

The difference from namespaces: a namespace's library check runs *before anything is loaded*
(`library_unchanged`, `mod.rs:758`, called from `plan_entry` and at the start of replay), and
a file's `G` is only known from its entry (found under its key, which needs its edges' `G`s:
a walk up from the leaves reading entry headers) or by loading it. So stage B needs: a
`Store` call that reads an entry's header only; a memo of `G` per file per session; and, when
some file in the reach has no entry yet (the edited file itself), loading the namespace's
needs first and comparing afterwards. Loading the needs happens on both the replay and the
elaborate path (`mod.rs:1242-1252`), so doing it before the comparison changes no state that
wouldn't change anyway **[verified for replay; not verified that the two paths load the same
set in every case]**. `plan_namespace` simply declines when a `G` is unknown.

This is a separate step with its own tests; it doesn't change stage A's format again if
stage A's header already has the digest field for both kinds of unit.

### 1.6 Helpers only a proof can reach (stage C)

A `match` or local definition inside a proof is lifted to its own declaration
(docs/core.md, opaque definitions, rule 6: "a `match` or local definition lifted from a
body ... and the body unfolds them all"). Under rule 1 those are in the
digest, so an edit that adds, removes or changes a `match` inside a proof changes the digest
and nothing is cut off. Safe, but it is a common kind of edit. How common in `tools/fmt` is
**[not verified]**: SW-4707 counts lifted helpers owned by theorems.

The end state leaves them out: a declaration is *proof-private* if it is a hidden helper
(`%` in its name) and nothing reaches it except sealed proof bodies and other proof-private
declarations: no name in scope, no row of a table other than its own `lifted`,
`match_columns` and `helper_keys` rows, no type and no kept body. That is a reachability
pass over the entry before the digest is taken, and the digest must then refer to the
entry's own declarations by path, not by position. It gets its own review (it is the one
place where the digest stops being "the entry minus three things").

The design is "Stage C design (SW-4713)" at the end of this note; it narrows the candidates
to lifted `match` helpers and replaces this paragraph where they differ.

## 2. Trust

A replayed entry goes into the trusted base unchecked (check-cache-trust.md, D1660). Today's
argument: *same key ⇒ same text, same compiler, same inputs all the way down ⇒ elaboration
would produce this entry.* The new one:

> **Claim.** If `K(N)` is the same, elaborating `N` now produces the same declarations,
> tables and messages as the stored entry.

By induction over the namespace order. `K(N)` fixes `N`'s text and, for each `D` below,
`G(D)`. If `G(D)` is a text key, `D`'s whole content is fixed (the old argument). If it is a
digest, everything in `D`'s entry is fixed except (a) sealed theorems' bodies, (b) positions,
(c) `D`'s messages and navigation. The claim then needs exactly:

- **P1 (entries are complete).** Everything a later unit can read of `D` is in `D`'s entry.
  This is today's cache contract (`mod.rs:5-15`), already checked by the differential tests:
  if it failed, today's cache would be wrong too.
- **P2 (sealing).** Elaborating `N` never reads the body of a declaration for which
  `has_interface` holds.
- **P3 (positions).** `N`'s result depends on positions in `D`'s files only through values
  stored by name or covered by rule 4.
- **P4 (absolute ids).** `N`'s result doesn't depend on declaration numbers, which shift
  when a proof below gains or loses a helper. Already relied on: a plain `check` leaves
  namespaces out (`project.rs:398-432`), so entries are replayed today into sessions with
  different numbering.

### 2.1 P2, checked against the code

The kernel half is docs/core.md, opaque definitions rule 6: "no other declaration ever sees a
theorem's proof: what any declaration checks against is its statement alone", with rule F;
no opt-out was built **[verified in the spec; kernel code not re-audited here: that was
SW-4700's and its Fable review's job]**.

The elaborator half: I read all 40 `.body()` reads in `crates/elab/src` outside the cache,
and the 4 in `crates/driver/src` outside `live/trial.rs` **[verified by grep and reading each
site; `live/trial.rs` (4 reads, the editor's trial edits) not read]**:

| Sites | What is read | Verdict |
|---|---|---|
| `interfaces.rs:1029,1300`, `module.rs:3213`, `auto.rs:1547`, `reading.rs:1886`, `opaque.rs:467`, `rewrite/repeatedly.rs:1745` | only whether there is a body | covered: a declaration without one hashes differently |
| `unify.rs:3180,3468`, `carry.rs:264`, `matching.rs:2672`, `nav.rs:1525`, `walk/mod.rs:708,975`, `rewrite/repeatedly.rs:1580,1620`, `equations.rs:2370,4443`, `equations/induct.rs:207,235,456`, `decreasing.rs:1236,1968`, `decreasing/plain.rs:799,855`, `opaque.rs:249,529`, `assume.rs:157` | bodies of computing definitions: projections, case trees, relations, helpers, defaults, the owner of a `?` | in the digest (bodies kept) |
| `equation_notes.rs:207` | the proof of every theorem **named like a generated equation**, across the whole session, to list equations in an error's note | proof-dependent, but only ever part of an **error**, and a namespace with an error is never cached |
| `timings.rs:327` | sizes, for `--timings` | not in any entry |
| `driver/axioms.rs:233,278`, `audit.rs:467`, `declhash.rs:153` | proofs, for `axioms`, `audit` and declaration listings | report-time walks over the live session (2.3) |

Not covered by this table, and for SW-4707's reviewer: reads of the `body` *field* inside
`crates/core` by functions the elaborator calls (erasure, `value::hidden`, termination), and
`live/trial.rs`. **[not verified]**

For the side tables, P2 is the question the brief asked of each ("statement or proof?"), and
rule 1 changes it: a table's rows are in the digest whatever they were derived from, so a
row that did depend on a proof would cost a missed cut-off, not a stale result. What I
checked is that the tables keyed by theorem hold nothing derived from a proof: `walk_tags`
is the tag and where it was written; `readings` is built when the `@[reading]` theorem is
declared and `reading.rs`'s one body read is a presence test; `rule_sets` hold the rules as
references **[verified from the table definitions and the grep above; the builders of
`ReadingInfo` and `RuleSet` not read line by line]**.

### 2.2 What breaks it

- **A table missing from entries** breaks today's cache equally; the digest adds no new way
  to miss one. This is the point of rule 1.
- **Session state a later unit reads that isn't in any entry.** `Session`
  (`state/session.rs:26-144`) has three I could find: the project's namespace list (in every
  source hash already), `project_names` (what `import N (..)` brings from each namespace, from
  a syntax pre-pass, `session.rs:32-34`), and `library_reach` (rebuilt from each entry's
  needs, which is why needs are in the digest). `project_names` comes from syntax, so today's
  text keys cover it and a digest wouldn't: **the key must add a hash of `project_names[D]`
  for each `D` in the closure.** It is cheap, and it doesn't change when a proof does.
  `derive_waiting` is documented as not cached, with an accepted stale note
  (`session.rs:128-135`); unchanged.
- **A proof-dependent message.** Section 3.
- **A digest function that changes meaning between builds.** A carried-over entry
  (check-cache-across-updates.md) brings a digest another build computed. Rule: any change to
  what the digest covers bumps `FORMAT`, which is in every key.

### 2.3 Reliance: goals, stand-ins, axioms

A theorem whose proof contains a `?` is still final with a body, so `has_interface` holds and
its interface hash is its statement's **[verified, `hash.rs:235-238`: the test is on the
theorem's own `assumption()`, not on what its proof mentions]**. So a digest must never be the
thing that says "finished".

- *An upstream proof gains a `?`.* `D`'s text changed, so `D` is checked; it reports a goal,
  so it is not written (`mod.rs:976-984`) and has no digest this session; by rule 3
  `G(D) = ("text", K(D))`, which differs from the digest it had; every `N` above misses and
  is checked afresh. While the `?` stays, each `N` is keyed to `D`'s text, exactly as today.
- *The report.* "Relies on an open goal" is `Elaborator::goals_relied_on`, a walk over the
  live session's checked terms (`assume.rs:179-196`; `driver/src/reliance.rs:1-9`), run when
  the summary, a test or `run` asks. A replayed `N` holds its real proofs, which refer to
  `D`'s theorems, whose current bodies are in the session; so the walk is right whichever of
  them were replayed. Nothing about reliance is stored in an entry **[verified: `encode`
  writes none; `unfinished_*` are documented "never in an entry", `tables.rs:118-126`]**.
- *A plain `check` that leaves namespaces out* loads everything as soon as a loaded
  namespace has an error or a goal (`project.rs:290-296`), so the walk sees all of it.
- *A failed proof* is replaced by a stand-in with its own hash and the namespace has an
  error: no digest, and nothing above is stored (`mod.rs:988-998`).
- *Axioms.* `stitchwort axioms` and `audit` walk bodies in the live session
  (`driver/src/axioms.rs:225-233`). A proof edit that starts using an axiom changes no
  digest, and the walk still finds it, because the edited namespace was checked and holds the
  new proof.
- *Tests.* The test cache's key already adds the goals a test relies on (SW-4701).

Stage D (section 7) would relax rule 3 for goals; the points above are why it is a decision
and not a default.

### 2.4 What a wrong key costs, and the nets

A digest that misses an input gives a stale verdict: a namespace reported as checking when
it wouldn't, and its terms admitted unchecked. The nets:

- Overmind's rolling `check --no-cache` of whole AoC and the roguelike, as now.
- The differential tests' count of replays the kernel refused, as now.
- **New, recommended:** `check --recheck` (it exists: every entry's terms go back through
  the kernel, `mod.rs:295-307`) also recomputes each replayed entry's digest and fails
  loudly on a mismatch. That catches an altered header, a replay that doesn't rebuild a
  part the digest covers, and a digest function that differs from the one that wrote the
  entry. It **cannot** catch a digest that leaves out something a dependant reads: the
  recomputation leaves it out too (SW-4707's Fable review, finding 2). Only the
  differential tests and the rolling `--no-cache` check catch that. Hence also one
  differential test that, for a project, edits each proof in turn and compares a cached
  check with `--no-cache` (below). A sampled re-check in normal
  runs isn't worth it: `--no-cache` in the rolling check covers the same ground.

## 3. What the user sees

A namespace loaded from the cache prints its stored warnings (`mod.rs:1898-1914`); errors
and goals are never stored. Can a proof edit in `D` change a warning in `N`?

- Through `N`'s elaboration: no, by the claim (P1-P4).
- Through text quoted from `D`'s proof: no warning does that that I found; the one message
  that reads proofs is an error's note (`equation_notes.rs`, 2.1) **[verified for body
  reads; I did not read every warning's text]**.
- Through positions: a warning label pointing into `D`'s file would go stale; rule 4 makes
  such an entry miss.
- "Unused lemma" style warnings about `D`'s declarations are `D`'s own, and `D` was checked.
- Doc-link warnings are recomputed on every replay already.
- "Relies on an open goal": section 2.3; never stored.

One visible change: the cache's debug and stats lines. A namespace above an edited proof now
says "replayed" instead of "elaborated, written" (`live.rs:720-740`).

## 4. The editor

Today **[verified, `crates/driver/src/live.rs:1-18`, `1051-1182`]**: the server checks one
namespace per step on a rewind stack. An edit rewinds to the mark before the first changed
namespace; everything after it is thrown away; then the edited namespaces are checked, then
their dependants, and the untouched rest is replayed from the cache. Dependants miss today
because their keys change.

With digest keys the same code gives the namespace-level cut-off with no editor change: a
dependant's key is unchanged, so its step is a replay. Two limits:

- **Only while the edited namespace checks cleanly.** With an error or a `?` in it (most of
  the time, mid-edit) rule 3 gives it a text key and everything above is re-checked on each
  edit, as today. Dependants of a namespace with an error are also not written
  (`mod.rs:988-998`), and the stores keep one or two entries per unit
  (`crates/driver/src/check_cache.rs:128`, `519`), so the dependants' healthy entries survive
  an error below but not a `?` below. Stage D is what fixes the `?` case.
- **Within a namespace, nothing changes.** Declarations after an edited proof in the same
  namespace are checked again: the rewind stack's unit is the namespace. Skipping them needs
  marks or units per declaration; it is the same structure as checking proof bodies after
  their statements (parallel-checking.md, option B) and should be designed with it. A
  separate stage; this note doesn't provide it.

Navigation makes rule 4 matter more in the editor (entries with `+nav` hold many more
positions); the count in 1.4 is taken in both modes.

## 5. Parallel checking

Option A of parallel-checking.md hands a namespace's result from one worker to another as a
cache entry. With text keys a worker can compute every key before any work starts; with
digest keys a namespace's key is known only once everything below it has finished, which is
the order a scheduler runs them in anyway, and the digest in the entry's header is the small
thing a worker needs from a finished dependency before it can look for its own entry. The
gain is on re-runs: after a proof edit, only one worker has anything to check. What parallel
checking still needs is unchanged: a session per worker, the scheduler, and (for proof bodies
in parallel, option B) statements admitted before proofs within a namespace. Stage C's
reachability pass and option B share the idea of "the part of a namespace that is its
interface", and reading only that part of an entry (skipping proof bodies when a worker
loads a dependency) would use the same marking **[estimated; not designed here]**.

## 6. Build plan (SW-4707, Opus)

Stage A, in order. Files: `crates/elab/src/cache/mod.rs` (most), `cache/codec.rs`,
`cache/dump.rs`, `crates/core/src/hash.rs` (`has_interface` public),
`crates/elab/src/state/session.rs` (a `namespace_digests` table beside `namespace_keys`),
`crates/driver/src/project.rs` (nothing expected beyond tests), `crates/driver/tests/`
check-cache tests, `docs/proposals/check-cache.md` (as-built note) and docs/core.md's hashes
paragraph ("and the check-cache keys, which cover text" becomes false).

0. **Before measure and counts** (20 min): the protocol below on `main`; count entries with
   another unit's file in their file table (with and without navigation); count lifted
   helpers owned by theorems in `tools/fmt`; list namespaces that are never cached
   (`STITCHWORT_CACHE_DEBUG`, "can't be cached"). If the first count is large, stop and
   report before building.
1. **The digest stream.** `Encoding` gets a second writer; `span` writes to the entry only;
   the three exclusions are explicit calls. Outside references in the digest are path and
   `interface_hash`. The digest goes in the sealed header. `FORMAT` 43 → 44.
2. **Dependency records by `interface_hash`** (`Out::def`, `decode`).
3. **The key**: `G(D)` as in 1.2, plus the hash of `project_names[D]` (2.2).
   `plan_namespace` records a dependency's `G` only when its entry was found, and declines
   when one is unknown.
4. **Rule 4**: other units' files in the file table, recorded with their text hash and
   compared in `plan_entry` and at the start of replay.
5. **`--recheck` recomputes and compares the digest.**
6. **Tests** (named, in the check-cache test file; each a small two- or three-namespace
   project checked twice, asserting on `Stats`):
   - an edited proof below: the dependant is a hit; same with a length-changing edit;
   - each of these edits below makes the dependant miss: a theorem's statement; a computing
     definition's body; a `def` of proposition type; an added or removed name; an instance;
     an `@[reading]` theorem and a `@[walk]` tag added or removed; a `rules` set; an ability;
     a record field default; a proof that starts using a new library file (reach);
   - a proof below gains a `?`: the dependant is checked, and `check`'s summary and
     `stitchwort goal` name the reliance; the `?` is filled again: reliance gone;
   - a proof below starts using an axiom: `stitchwort axioms` on the dependant's theorem
     shows it, with the dependant replayed;
   - a dependant whose warning points into the edited file misses (rule 4);
   - an entry whose stored digest is altered is refused by `--recheck`; an entry whose
     dependency's statement changed is refused on the trusted path (the existing
     "isn't what the entry was made with" refusal, now by interface hash);
   - one differential test: for a small project, for each theorem, replace its proof with
     an equal-statement variant, check with the cache, and compare diagnostics and the
     canonical dump with `--no-cache`.
7. **After measure.** Protocol: `tools/fmt`, release build, warm cache; change line 32 of
   `tools/fmt/src/Fmt/SpellProofs.sw` from `(byComputing, byComputing, byComputing)` to
   `((byComputing, byComputing, byComputing))` (same proof, one position later for the rest
   of the file); run `check` with `STITCHWORT_CACHE_DEBUG`; record namespaces elaborated,
   namespaces replayed, and wall seconds; before and after. This is a whole-project check,
   so the verifier or Overmind runs it, not the lane (the lane's tests are the small
   projects in step 6).

Stage B (library files, 1.5) and stage C (1.6) are separate tickets after A is measured.

**Estimates** (agent time). The nearest past task is SW-4701 (interface hashes, Opus): 32 min
against an estimate of 60 **[verified, the board]**. Stage A touches more (the encoder, the
key, a new entry field, about fourteen tests): **90 min**. Stage B: 60 min. Stage C: 60 min
plus a review. Stage D: 45 min after its decision. **[estimated]**

## 7. Decisions for Matt

1. **While a `?` is open inside a proof, should the namespaces above stay cached?** (Stage
   D.) *The problem:* with rule 3, opening a `?` in a low proof re-checks everything above it
   on each edit until the `?` is filled, and then once more; in the editor that is the
   common state. *The change:* a namespace whose only gaps are `?`s inside theorem proofs
   keeps a digest (the goals themselves are proof-private in stage C's sense), so what's
   above is replayed, and "relies on an open goal" comes from the walk alone. *What it should
   do:* working on a proof never re-checks another namespace **[estimated]**. *The cost:* a
   cached "this namespace checked" would then sit above an unfinished proof; every place
   that reports "finished" (check's summary, tests, `run`, `audit`, a plain `check` that
   leaves namespaces out) must get it from the walk, and one that reads the cache instead
   would be a silent wrong answer. **[rec: yes as the end state, built last, after stages A
   and C, with a Fable review of every "finished" report first]**

2. **Stage order after A.** B (library proof edits stop re-checking projects: helps every std
   lemma lane) or C (edits that touch a `match` inside a proof also cut off) first? This is
   the orchestrator's call unless Matt has a view; I'd take the counts from step 0: if many
   theorems own lifted helpers, C first, since without it stage A's cut-off misses the
   common edit. **[rec: decide from step 0's counts]**

Everything else here (the header field, the sidecar or header read for stage B, test names)
is implementation.

## 8. Open risks

- The **position rule** may catch most entries under navigation, leaving the editor with
  little cut-off until raw targets are converted to by-name **[not verified; step 0]**.
- **Lifted helpers in proofs** may make stage A's cut-off rarer than the headline suggests
  until stage C **[not verified; step 0]**.
- **P2 inside `crates/core`** and `live/trial.rs` were not read (2.1).
- **The builders of `ReadingInfo` and `RuleSet`** were checked by their body reads only.
  Under rule 1 a mistake there costs cut-off, not correctness.
- **A namespace that can never be cached** (an exported definition, `mod.rs:1805`) keeps a
  text key, so everything above it behaves as today, and a plain `check` can't leave out
  what's above it at plan time unless its "no entry" is distinguished from "not yet
  checked" **[not verified whether any project has one below other namespaces; step 0]**.
- **Stage B's load-then-compare** order needs the replay and elaborate paths to load the
  same library files (1.5) **[not verified]**.

## As built (stage A)

SW-4707 (Opus, 23 Nov 2026). Built as section 6 says, with these choices and findings.

**Step 0, before** (read from `tools/fmt/.stitchwort/cache/check` in the main checkout,
the 138 namespace entries of build `2e82891820f8…`, FORMAT 43, written 21 Nov without
navigation; script `files_table.py`, kept with the lane's notes):

- *Entries holding a position in another unit's file:* 24 of 138, and every one of them in
  `std:core` only, whose text the stamp's library index already covers. **None holds a
  position in another project file.** With navigation: there are no `+nav` entries in that
  cache, so not measured; in the tests, navigation's targets in another namespace's file
  (declarations, a record's fields) are kept by name and replay matches a fresh check
  (`a_moved_record_below_replays_what_navigates_to_it`). So the first count is small and
  rule 4 was built as written.
- *Lifted helpers owned by theorems:* 4,996 `%match` helpers (and about 50 of other kinds)
  whose owner's short name is one of the 5,563 theorems in `tools/fmt/src`; about 1,930
  theorems own at least one, a third of them **[estimated: matched by short name, from the
  entries' string tables]**. An edit inside such a proof that doesn't touch its `match`
  keeps the helper and the digest; one that adds, removes or changes the `match` doesn't
  (stage C).
- *Namespaces never cached:* not counted: it needs a whole-project check with
  `STITCHWORT_CACHE_DEBUG`, which the measure script below runs and keeps.

**Measure** (step 7): `measure.sh BINARY CHECKOUT` (in docs/reviews/SW-4707-notes.md)
warms a fresh cache directory on `tools/fmt`, makes the line-32
edit, checks again with `--timings` and puts the file back; it prints namespaces
elaborated and from the cache, and wall time, for main's binary and the lane's. Run by the
verifier, not the lane. **[measured by the orchestrator, 23 Nov 2026]**: after the edit,
main's binary re-checked about 54 namespaces in 31.0 s; this one re-checked
`Fmt.SpellProofs` alone, 5.3 s. Cold 115 s (main) and 117 s (this); warm about 2.9 s
both.

**Choices beyond the text** (none changes what an entry is trusted for):

- *One encoder, two passes*, rather than a second writer beside the first: `encode_pass`
  runs once for the entry and once in digest mode, in which `Out`'s span writes do nothing
  and each other exclusion is an `if !digest` (the library-file and `include` records, the
  warnings, a sealed body, the navigation section). Same default-include property; it
  costs a second encoding without navigation **[not measured]**.
- *The digest pass's node table is by content* (`TermWriter::by_content`): equal terms are
  one node whatever memory they share, so the digest can't depend on sharing, and
  `--recheck` can compute it again from decoded terms. A body left out is marked by a
  flag, so a sealed theorem and a stand-in can't write the same stream. Own declarations
  write their `interface_hash`.
- *Rule 4 for a project file* records the hash of every namespace's sources rather than
  that one file's text, which the elaborator doesn't have (the host gives hashes per
  namespace): such an entry misses when any project source changes, which is coarser than
  needed. A library file's position records that file's text hash. `W-MODULE-NAME` is a
  construct that needs it (its warning labels a type definition in the namespace it
  comes from; found by the Fable review): tested end to end
  (`a_warning_pointing_into_the_edited_file_checks_what_holds_it_again`) and at the unit
  level (`cache::tests::a_position_in_another_namespaces_file_…`).
- *A plan declines* when a dependency has no digest (`namespace_cache_key(.., planning)`):
  such a dependency is loaded anyway, so nothing that would have been left out is loaded.
- *`check --recheck` and a mismatch*: the replay is complete by then (its tables are in),
  so it isn't undone; the namespace gets `E-CACHE-DIGEST`, is counted in
  `Stats::digest_mismatches` and gets no digest, so the check fails. The entry isn't kept
  as re-checked, and this build's own is replaced by one that doesn't open, so the next
  check elaborates the namespace again. A test pins two digests of a fixed project, failing
  with "bump `FORMAT`" when the digest's meaning changes.
- *Library files' entries* also carry a digest in their header (so stage B needn't change
  the format) and record dependencies by interface hash; their keys are unchanged.
- *A digest is forgotten* when a namespace is checked without the cache path at all
  (`module.rs`), so its dependants fall back to its key.

**Found while building:** a proof that starts using a declaration that comes *later* in its
namespace changes the order the namespace's declarations are made in, and so its digest
(own declarations are referred to by position): measured on a two-namespace project, where
moving the used declaration first kept the digest. Costs cut-off, not soundness; stage C's
"by path, not position" would fix it.


## Stage C design (SW-4713)

Paper lane on Fable, 24 Nov 2026, for D3729; the build is SW-4714 (Opus). It replaces
section 1.6's sketch and folds in SW-4710. Code was read at `fda6878dd`; the experiments
are two-namespace projects checked with main's release binary. Marks: **[measured]** (a
probe I ran), **[verified]** (code, file:line), **[estimated]**, **[not verified]**.

**The problem.** Stage A keeps the cut-off for a proof edit only while the namespace's
other declarations stay exactly as they were, in the same order. Two common proof edits
break that. Adding or removing a `match` on something computed adds or removes a hidden
helper declaration **[measured: `theorem t … := match after + 0 with …` puts
`A.t.%match1` in `A`'s entry, `A`'s digest changes and `B` is elaborated]**; and a proof
that starts using a later declaration changes the order the namespace is checked in
**[measured: `other := z n` with `z` declared later changes `A`'s digest]**. About 1,930 of
`tools/fmt`'s 5,563 theorems own such a helper **[estimated, SW-4707 step 0]**.

**The change.** The digest stops mentioning (1) the helpers of `match`es that only sealed
proofs reach, and (2) where a declaration sits among the others: it names the namespace's
own declarations by path, and lists plain theorems in path order rather than checking
order.

**What it should do.** Editing a proof in any way that keeps every statement, including
adding and removing `match`es and using a later theorem, re-checks that namespace alone
**[estimated; the measure in C.5 shows it on `tools/fmt`]**.

### C.1 What is left out, exactly

**Candidates.** An own definition of the unit is a *candidate* when all of these hold:

- it has a row in the unit's `lifted` table: it is the helper of a lifted `match` (or of a
  record update's `match`), named `owner.%matchN` **[verified: every draft that isn't a
  local definition is pushed there, `lift.rs:885-898`; names from `lift.rs:678-699`]**;
- it is not marked `instance`, is not a theorem, and has no scope name.

Nothing else can be left out: not a local definition or local theorem (`t.go` is bound in
scope once its owner is final and can be named from another namespace, `lib.rs:3277-3296`),
not `f.%body`, `f.%step`, `f.unfold`, derived instances or their `%` helpers, equations,
defaults' helpers. Those are found by *constructed names* (`{path}.%step` at
`tailrec.rs:199-202` and `equations.rs:2211-2220`; `has_member(d, "%compare")` in the
derives), so reachability through terms doesn't describe who reads them. For `%match`
there is no constructed-name lookup: every code mention of the name tests a definition
already in hand from a term, or cuts the owner's name out of a message **[verified: grep
of `%match` in `crates/elab/src`, `crates/driver/src`, `crates/core/src`, 11 code sites:
`opaque.rs:490`, `tailrec.rs:270`, `equation_notes.rs:172,216`, `lift.rs:696,1807,1829`,
`auto.rs:1324`, `equations.rs:4376`, `termination.rs:369`, `pretty.rs:2884`]**. SW-4707
counted 4,996 `%match` helpers against about 50 hidden helpers of other kinds owned by
theorems, so this is the whole gain.

**Proof-private.** A candidate is *proof-private* unless it is reachable from a root:

- *Roots*: every reference to an own definition that the digest stream writes anywhere
  other than (a) inside a candidate's own record (its type, body, `unfolding` list, run
  body, group) and (b) inside a table row *owned by* a candidate. So roots include every
  type, every kept body, every name, every row of every table, the extensions, and anything
  added to entries later.
- *Not roots, because the digest doesn't write them*: a sealed theorem's body (stage A),
  and, new here, a sealed theorem's group list (C.2).
- *Edges*: the references in a candidate's own record and owned rows.
- *Owned rows*: the candidate's row in `lifted`, `match_columns` and `update_shown`
  (the three written for the helper by `lift.rs:855-915`). A row in any other table that
  mentions a candidate, as key or value, is a root.

Proof-private = the candidates not reached from the roots through edges (mark from the
roots; cycles among candidates with no root reaching them are private, as mutually
recursive helpers of one proof should be).

How the cases the brief asks about fall out:

| Case | Result | Why |
|---|---|---|
| a `match` in a theorem's proof | private | reached only from the sealed body |
| a `match` in a `match` in a proof | both private | the outer helper's body is an edge, with no root above it |
| a recursive theorem whose `match` is lifted (the helper joins the theorem's group) | private | the theorem's group list isn't written (C.2) **[measured that such a theorem checks and makes `A.rec.%match1`, `%match2`; not verified that they join the group]** |
| a `match` in a theorem's *statement* | kept | the type is a root. These are numbered before the proof's (`signature_matches`, `lift.rs:785`), so a proof edit doesn't rename them |
| a `match` in a computing `def`'s body, or in a `def` of proposition type | kept | a kept body is a root |
| a `match` inside a local `def` in a proof (`t.go.%match1`) | kept | `t.go` is named and its body kept. Inside a local *theorem*: private |
| a local `def` or `theorem` added to a proof | kept, digest changes | it gets a name another namespace can write (`A.t.go`); not a candidate |
| a helper in a group with a computing definition | kept | that definition's group list is a root |
| a helper named by an instance, an equation, a `rules` set, a reading, a default | kept | a row of another table is a root |
| a theorem with an `unfolding` list | its helpers private unless the theorem's stored list names them | the list is written for every definition, so if it names a helper that helper is a root **[not verified which; `opaque.rs:200-222` puts the earlier helpers in each *helper's* list]**. Costs cut-off only |
| the same helper shared by a proof and a computing `def` | can't arise by construction (a helper is named under one owner); if it did, the `def`'s body is a root | |

**How it is computed.** By the encoder, not by a separate walk over terms, so that rule 1
(default-include) still holds: a part added to entries later is a root unless someone
marks it as a candidate's own. `Out` gets a *context* (root, or a candidate) set by the
definition loop while it writes a candidate's record and by the three owned tables while
they write a candidate's row; `Out::def` in digest mode records `(context, target)` for
each own definition written. One *recording* digest pass collects the pairs; the marking
is a few lines; the *final* digest pass skips private candidates' records and owned rows.
If the final pass meets a reference to a private candidate, that is a bug in the marking:
it fails the encoding ("can't be cached"), never writes something. The entry itself is
unchanged: private helpers are in it and are replayed as now.

### C.2 The digest stream becomes position-free (SW-4710)

Leaving a record out shifts everything after it, so stage C needs this in any case; the
same change gives SW-4710. In digest mode only (the entry keeps its encoding):

1. **Own declarations by path.** `Out::def` and `Out::data` write an own declaration as
   its path (with its ordinal among own declarations of that path, in checking order, in
   the rare case two share one), not `id - base`. Outside declarations stay path and
   `interface_hash`.
2. **Group lists by path**, sorted. Today they are raw positions (`mod.rs:2325-2331`), so
   they never go through `Out::def`. **A sealed theorem (`has_interface`) writes no group
   list.** Its group says which declarations its *proof* is checked together with; each
   other member that is in the digest writes its own list, which names the theorem.
3. **A data type's `defs_before`** (`mod.rs:2402-2406`) counts every definition before it,
   private helpers and theorems included. The digest writes instead the number of
   *ordered* definitions (below) before it. `datas_before` is unchanged.
4. **Order.** The definitions section is written as: first the *ordered* part, in
   checking order; then the *plain theorems*, sorted by path. A plain theorem is a sealed
   theorem (`has_interface`) that is not marked `instance` and is the key of no table row
   (no `@[reading]`, `@[walk]`, `rules`, default, …: found in the recording pass, like the
   roots). Everything else that is kept is ordered: computing definitions, kept helpers,
   theorems with rows, data types. Tables keyed by a declaration (`OwnedBy`, sorted by id
   today, `table.rs:277-281`) sort by the same order. Tables that are sequences (`tests`,
   `abilities`, `lifted`, `equation_skips`, `equations_done`) keep their order, minus
   private rows. Names are already sorted by key (`mod.rs:1300-1313`).

What this buys: a proof that starts using a later *theorem* keeps the digest (the probe
above). A proof that starts using a later *computing definition* keeps it only if that
doesn't move the definition past another ordered declaration; otherwise the digest changes
and the namespaces above are re-checked, as today. Sorting everything by path would cover
that too; it is decision 1 below, and I recommend against it for now.

### C.3 Trust

Two different things can go wrong with a cache hit, and stage C touches only the second.

**(a) The replayed terms are still valid kernel terms: unchanged, and not resting on the
digest.** Every outside declaration a replayed entry's terms mention is in its dependency
records by path and `interface_hash`, compared on replay (`Out::def`, `mod.rs:1532-1556`;
the refusal "isn't what the entry was made with"). For a helper, which is not a theorem,
`interface_hash` is its full hash, body included (`hash.rs:235-258`). So if the marking
were wrong and a dependant's stored term did mention a helper the digest left out, a
changed or vanished helper is refused at replay and the namespace is elaborated: a late
miss, not a wrong admission. What the kernel guarantees underneath is rule 6 and rule F
(docs/core.md): no declaration's check unfolds or reads a theorem's proof, and a reference
to a theorem hashes as its statement, so nothing a dependant checked can depend on what
only a sealed proof mentions. **Limit:** a plain `check` that leaves a namespace out
unloaded (`plan_entry`, `mod.rs:793-807`) compares no dependency records; there the key is
the only guard, as in stage A.

**(b) The stored entry is what elaborating the source now would give.** This is the
claim of section 2, and stage C needs two more properties for it:

- **P5 (private helpers are invisible).** Elaborating `N` never reads a proof-private
  helper `h` of `D`: not its existence, name, type, flags or rows.
- **P6 (plain theorems' order is invisible).** `N`'s result doesn't depend on where a
  plain theorem of `D` sits in `D`'s checking order.

*P5, by the ways `N` could come to hold `h`:*

1. *Through a term.* `N` reads `D`'s types, kept bodies and table rows, all roots, and
   never a sealed body (P2). A private `h` is in none of them by definition.
2. *By name.* A `%match` helper has no scope entry (only local definitions are bound,
   `lib.rs:3277-3296`); source can't write one (`%` is its own token, `lexer.rs:976`)
   **[measured: `A.closed.%match1` in `B` is `E-PARSE`, "expected a field name after
   `.`"]**; and no code builds a `%match` name to look up (C.1).
3. *By re-lifting the same name in `N`* (the brief's question). A helper's path is
   `unit.path(name)` (`kernel.rs:195`) under its owner's key, so `N`'s helpers are named
   under `N`'s own declarations and can't collide with `A.t.%match1`. Within `D`, a proof
   edit renumbers that proof's helpers (`%match1` may now be a different `match`); all of
   them are private, and one that isn't (reached from a root) is in the digest under its
   name, so renumbering it changes the digest.
4. *By a table.* Its three owned tables are read by id (`match_columns`, `update_shown`),
   or walked only to explain a message that already names a `%match` helper (`lifted`:
   `lift.rs:1778-1830`, `decreasing/plain.rs:847`). `helper_keys` holds local
   definitions' keys, not these.
5. *By a scan of all definitions.* This is the new exposure: stage A never removed a
   whole declaration from the digest, so a scan was always covered. The scans in
   `crates/elab/src` outside the cache and tests, each read **[verified by reading the
   site; not a proof that the list is complete: it is a grep for `env.defs()`,
   `namespace_defs` and `tables.lifted`]**:

   | Site | Selects by | Can it select or be changed by a private helper? |
   |---|---|---|
   | `auto.rs:1344-1360`, `1464-1500`, `1533-1550` (decision procedures, hints) | the `instance` mark; order by path | no: a candidate isn't an instance |
   | `reading.rs:1882-1890` | the `instance` mark | no |
   | `opaque.rs:460`, `check.rs:1029` | "is any definition opaque?", a fast path before a walk over the terms of a diagnostic | a private helper under an `unfolding` list is opaque, so the gate can open; what follows reads only definitions in the diagnostic's terms and skips `%` names. Same result |
   | `opaque.rs:685-700` | an owner whose `unfolding` list holds a given local definition; skips `%` owners | no |
   | `tailrec.rs:199-202`, `equations.rs:2211-2220` | an exact `{path}.%step` | no |
   | `congruence.rs:693` | names ending `Cong` | no |
   | `interfaces.rs:1296`, `equation_notes.rs:70,202` | notes on an error | an error is never cached |
   | `assume.rs:86-172,419` | assumption labels | a helper isn't an assumption; goals aren't cached |
   | `module.rs:963-1113`, `decreasing.rs:1119,1409`, `lib.rs:1463`, `library.rs:988,1595` | the unit's own range, or a count taken as a mark | own unit only |
   | `library.rs:1024` (`library_decision_procedures`) | every definition's result type | `#[doc(hidden)]`, for a test of D58; not reached while elaborating **[not verified beyond its doc]** |
   | `timings.rs`, `search.rs:1393` (driver's `search`), `driver/*` (`audit`, `axioms`, `doc`, `run`, `declhash`, `live/trial.rs`) | everything | report-time walks over the live session, in no entry (section 2.3) |

   `namespace_defs` ranges grow and shrink with helpers; their only readers are the
   `auto.rs` sites above (membership tests and the instance scans).

*P6.* A plain theorem has no instance mark and no table row, so of the scans above only
an exact-name lookup can find it, and none of the lists they build has it in. The two
places I found where a dependant's result follows id order are both over tables or marks
that plain theorems are excluded from: `reading.rs:1882` (instances, in id order, giving
the order of `N`'s warnings) and `reading.rs:1919` (the readings table) **[verified]**.
That is why C.2 keeps anything with a row or a mark in the ordered part. P4 (absolute
ids) is relied on as before.

*The sealed theorem's group* (C.2 rule 2) is the one new exclusion besides private
helpers. Readers of a definition's group outside the cache: `tailrec.rs:208`, for the
`@[tailrec]` definition being checked, in the elaborator **[verified, grep of
`.group()`]**; in `crates/core`, the hashes (a computing member's `def_hash` covers its
whole group, proofs included, `hash.rs:212-225`, and that hash is in the digest),
termination, erasure and the backends **[not verified: for the Fable review]**. A
theorem can't be recursed on from outside (`E-NO-INDUCT`, SW-4707's review).

*What the kernel guarantees and what the elaborator must.* The kernel: rule F and rule 6
(no check reads a proof), dependency records by interface hash (a), and that a trusted
replay re-admits exactly the entry's declarations. The elaborator: P1 to P6. P5's items 2
to 5 and P6 are facts about elaborator code that a later change can break without any
test in the changed area failing: a new scan that picks definitions by type, or a new
lookup that builds `%match` names. Two things keep that honest: the differential tests
of C.5 (each compares with `--no-cache`), and one sentence at `Tables::lifted` and at
`Def`'s environment accessor saying that a scan must not let a `%match` helper change a
result another namespace caches.

*What a mistake costs.* A helper wrongly left out that a dependant's *terms* use: a
late miss (a). One that a dependant's *elaboration* consulted without keeping: a stale
entry whose terms are still valid, so a message, a warning or a choice `auto` made may
differ from a fresh check until `--no-cache`; and under a plain `check`'s plan, a
namespace reported as checking that a fresh check might not. A helper wrongly kept:
lost cut-off only. `--recheck` can't see either (both sides compute the same marking);
the nets are the differential tests and the rolling `--no-cache` check.

### C.4 The editor and parallel checking

Unchanged. The editor gets the wider cut-off through the same keys, under the same two
limits as section 4 (only while the edited namespace checks cleanly; nothing within a
namespace). For parallel checking, the marking is the first concrete form of "the part of
a namespace that is its interface" (section 5), but nothing reads entries by it yet.

### C.5 Build plan (SW-4714, Opus)

Files: `crates/elab/src/cache/mod.rs` (nearly all), `crates/elab/src/state/table.rs` and
`tables.rs` (owned rows' context; keyed tables' order in digest mode),
`crates/driver/tests/projects/check_cache/digest.rs`, this note ("As built (stage C)"),
`docs/core.md` rule 6's sentence on the digest, `docs/proposals/check-cache.md`. No kernel
change; no change to what an entry holds or how it is replayed.

1. **By path** (C.2 rules 1 to 3): `Out::def`/`data` in digest mode; group lists through
   them, none for a sealed theorem; `defs_before` as the ordered count. `FORMAT` 44 → 45
   (the digest's meaning changes; finding 3 of SW-4707's review), and the pinned digests
   in `the_digest_of_a_fixed_project_is_pinned` are re-pinned.
2. **The recording pass and the marking** (C.1): `Out`'s context; the candidate test;
   mark from the roots. Skip the recording pass when the unit has no candidate and no
   plain theorem out of order (an optimisation; say what it costs, see the measure).
3. **The final pass**: skip private records and owned rows; write the ordered part, then
   plain theorems by path; keyed tables in that order. A reference to a private helper
   here fails the encoding.
4. **`--recheck`** needs nothing new if it calls the same `interface_digest` on the
   replayed state; check that the replayed `lifted` rows give the same candidates.
5. **`STITCHWORT_CACHE_DEBUG`**: the "written" line also says how many helpers were left
   out and how many theorems were plain, for the measure.
6. **Tests**, in `check_cache/digest.rs`, each through `after_edit` (cold, warm, edit,
   compared with `--no-cache`); the scrutinee must be something computed, or the `match`
   isn't lifted (SW-4707's review, finding 5): assert the helper is in the entry.
   - a `match` added to a proof below; removed; its arms changed: `B` replayed;
   - a second `match` added before the first in one proof (renumbering): replayed;
   - a recursive theorem's lifted `match` added: replayed;
   - a `match` added to a theorem's *statement*; to a computing `def`'s body; to a `def`
     of proposition type; to a local `def` inside a proof: `B` elaborated;
   - a local `def` added to a proof (a new name): elaborated;
   - a helper added to a proof *before* a data type's declaration: replayed
     (`defs_before`);
   - a proof starts using a later theorem: replayed (SW-4710; today's
     `BASE` comment about `oneProof` coming first goes);
   - a proof starts using a later computing definition that moves past another: only that
     the result equals `--no-cache`;
   - a `@[reading]` theorem's proof starts using a later theorem: equals `--no-cache`
     (it is ordered, not plain);
   - `B` has a `match` in a proof of its own while `A`'s proof gains one: `B` replayed,
     and `C` above both too;
   - `--recheck` after each of the first three: no digest mismatch;
   - extend `every_proof_edit_below_gives_what_a_check_without_the_cache_gives` with, for
     each theorem, a variant that wraps the proof in `(match 0 + 0 with | _ => …)`.
7. **Measure**, run by the verifier or Overmind (a whole-project check): `measure.sh`
   from docs/reviews/SW-4707-notes.md with one more run. After `edited`, restore the
   file, then replace line 32's proof by one with a lifted `match`:

       sed -i '32s/:= (byComputing, byComputing, byComputing)$/:= (match 0 + 0 with | _ => (byComputing, byComputing, byComputing))/' "$file"
       run matched
       strings -a "$cache"/check/*ns.Fmt.SpellProofs-* | grep -c 'spellsNil.%match1'

   **[measured on a probe: this one-line form checks and makes `A.triple.%match1`; not run
   on `tools/fmt`]**. Expected: main's binary `matched: elaborated` about 54 (as
   SW-4707's "before"), the lane's `elaborated 1`, and the last line at least 1 (the
   helper was really made). Also record `cold` for both binaries: the extra digest pass
   shows there (stage A's second pass: 115 s to 117 s cold **[measured, SW-4707]**; one
   more pass should cost about the same again **[estimated]**).

**Estimate.** SW-4707 (stage A: the encoder's second pass, the key, rule 4, 18 tests) took
Opus 43 min against 90 estimated, and its Fable review 11 min **[verified, the board]**.
Stage C is one file's worth of encoder work and about 14 tests: **expected 45 min**, review
15 min.

### C.6 Decisions for Matt

1. **How far should the digest ignore checking order?** *The problem:* a proof that starts
   using a later declaration reorders its namespace, and today everything above is
   re-checked. *Options:* (a) plain theorems listed by path, everything else in checking
   order (C.2, this design): covers a proof that starts using a later theorem; rests on
   P6, which I could check site by site. (b) everything sorted by path: also covers a
   proof that starts using a later definition, but then no cached result above may depend
   on the order of *any* two declarations below, and I found two places where warnings
   come out in that order (`reading.rs:1882`, `1919`); each would be sorted by path first,
   and the next one added would be a silent stale warning order. *What it should do:*
   (a) keeps the cut-off for the reorder I could measure; how often (b)'s extra case
   happens is **[not verified]**. **[rec: (a) now; (b) as its own ticket if the debug
   counts show the extra case is common]**

Nothing else here is Matt's: no proved tool accepts less, no theorem changes, nothing
user-visible but the cache's debug lines.

### C.7 Risks

- **P5 item 5 is an audit of today's code**, and the list of scans came from a grep. The
  Fable review of SW-4714 should redo it against the built diff, with `crates/core`'s
  readers of a definition's group.
- **A recursive theorem's helper joining its group** was assumed from the lifting code
  (`lift.rs:926-935`), not observed. If helpers are admitted apart, rule 2 of C.2 is
  harmless and unneeded.
- **A theorem's stored `unfolding` list** may name its own helpers (C.1's table); then
  theorems with a list keep today's behaviour. Count them in the measure's debug line
  before doing anything about it.
- **The extra pass** is paid on every namespace written **[estimated 1 to 2% of a cold
  check]**.
- **Stage D** (a `?` in a proof keeps the digest) would make an assumption a third kind
  of thing left out; it should reuse this marking, not add a second one.

## As built (stage C)

SW-4714 (Opus, 24 Nov 2026), from "Stage C design (SW-4713)" with C.6's option (a)
(the orchestrator's call): plain theorems by path, everything else in checking order.
`FORMAT` 44 → 45; the pinned digests re-pinned. No change to what an entry holds or how
it is replayed. The reviewer's checklist is docs/reviews/SW-4714-notes.md.

**What the code says about the design's unread points:**

- *`crates/core`'s readers of a definition's group* (C.3, C.7): `check.rs:2783` sets it;
  `check.rs:2798` derives `recursive` from it, which only unfolding reads, and a
  theorem never unfolds (rule F); `check.rs:3381` (a transparency set) adds the opaque,
  non-theorem group-mates of a definition another unit names in `unfolding`, and that
  definition is kept, so its group list is in the digest and makes those members roots;
  `hash.rs:212` (group hashes) is in the digest through the computing member's hash. Outside
  the core, `js/src/lib.rs:2677,3051` and `rt/src/specialise.rs:366` are back ends: run
  time, in no entry. Termination reads data groups only. **[verified by reading each site]**
- *A recursive theorem's helper joins its group* (C.7): `lift.rs` joins a helper to its
  owner's group when its body mentions a definition still pending (`join && pending`), as
  a call of the owner is. **[verified in the code; the test
  `a_match_added_to_a_recursive_theorem_below_replays_what_uses_it` replays `B`, which
  needs the group rule]**
- *A theorem's `unfolding` list naming its own helpers* (C.1's table): it does.
  `Elaborator::in_body_of` (`opaque.rs`) appends the helpers admitted on their own to the
  owner's stored list when the owner has an `unfolding` clause. The list is written for
  every definition, so those helpers are roots and kept: such a theorem keeps today's
  behaviour, as the design says. **[verified in the code; not counted in `tools/fmt`]**

**How it is built.**

- *Two digest passes after the entry's.* `interface_digest` takes a `DigestPrep` (the
  candidates: own rows of `lifted`, not a theorem, not an instance, `%` in the name; each
  own declaration's ordinal among those of its path), runs a *recording* pass, makes the
  `DigestPlan` (`digest_plan`: mark from the roots, then the plain theorems), and runs the
  *final* pass. The recording pass is skipped when the unit has no candidate and no sealed
  theorem (nothing to find). It writes nothing: it walks each term for its `Def` nodes
  (`codec::defs_in`), and with no candidate it skips terms, since only rows' keys matter
  then. On a synthetic namespace (300 definitions, 600 theorems, about 90 ms to
  elaborate) it takes about 3 ms, against about 8 ms for the entry's encoding and 10 ms
  for the final digest pass **[measured, temporary instrumentation, release build]**.
- *Candidates* are the rows of `lifted` whose helper's last name segment starts
  `%match` (so `decreasing`'s `%plain` twins, also in `lifted`, are not; Fable review
  finding 1); `Tables::lifted` says so.
- *Contexts* (`Context` in `cache/mod.rs`): `Root`, `Key` (a row's key in a table keyed by
  declaration) and `Own(c)` (candidate `c`'s record, or its row of `lifted`,
  `match_columns`, `update_shown`: `encode_owned_since` in `state/table.rs`). `Out::def`
  records each own reference with the context. The term writer skips nodes it has written,
  so in the recording pass it starts afresh whenever the context crosses into or out of a
  candidate's; otherwise a reference first written inside a candidate would go unrecorded
  from a root.
- *The final pass* writes own declarations as `(0, path, ordinal)` (outside ones as
  before), group lists sorted by path (none for a sealed theorem), definitions in the
  plan's order (ordered ones in checking order, then plain theorems by path), a data type's
  `defs_before` as the ordered count, and leaves out private helpers' records and owned
  rows. A reference to a private helper there fails the encoding ("can't be cached").
- *Keyed tables' order.* Rows keyed by definition are still written in id order: no plain
  theorem keys a row (that is what makes it plain) and private rows are left out, so id
  order is the digest's order without a sort.
- *Plain* is: sealed (`has_interface`), not an instance, written as no row's key. A theorem
  named only in a row's value (a `rules` set's rule) can be plain; the row names it by path.
- *Debug*: `STITCHWORT_CACHE_DEBUG`'s "written" line adds "N proof-private helpers left
  out, M plain theorems".
- *`--recheck`* calls the same `interface_digest` on the replayed state; the replayed
  `lifted` rows give the same candidates. The tests re-check after each stage C edit: no
  mismatch.

**Tests** (`crates/driver/tests/projects/check_cache/digest.rs`, each compared with a check
without the cache): a `match` added to a proof, removed, its arms changed, a second added
before the first, one in a recursive theorem, one before a data type: `B` replayed, the
helper in the entry, `--recheck` clean; a `match` in a statement, a computing body, a
`def` of proposition type or a local `def` in a proof, and a local `def` added: `B`
elaborated; a proof starts using a later theorem: replayed (SW-4710; `BASE` no longer
needs `oneProof` first); a later computing definition, and an `@[reading]` theorem using a
later theorem: equal to `--no-cache`; private helpers in two namespaces: `B` and `C`
replayed; the differential test with each proof wrapped in a lifted `match`.

**Measure** (C.5 step 7): `measure-c.sh`, in docs/reviews/SW-4714-notes.md, for the
verifier or Overmind. **[not run by the lane]**

