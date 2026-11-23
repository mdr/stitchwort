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
proof also cut off; **D** (Matt's decision, section 7) a namespace with an open goal inside a
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
body ... for a theorem's, only the theorem's proof unfolds it"). Under rule 1 those are in the
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
  loudly on a mismatch. And one differential test that, for a project, edits each proof in
  turn and compares a cached check with `--no-cache` (below). A sampled re-check in normal
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
verifier, not the lane. **[not measured yet]**

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
  needed, and no entry was found to need it. A library file's position records that file's
  text hash. Tested at the unit level (`cache::tests::a_position_in_another_namespaces_file_…`)
  since no construct was found that writes one.
- *A plan declines* when a dependency has no digest (`namespace_cache_key(.., planning)`):
  such a dependency is loaded anyway, so nothing that would have been left out is loaded.
- *`check --recheck` and a mismatch*: the replay is complete by then (its tables are in),
  so it isn't undone; the namespace gets `E-CACHE-DIGEST`, is counted in
  `Stats::digest_mismatches` and gets no digest, so the check fails.
- *Library files' entries* also carry a digest in their header (so stage B needn't change
  the format) and record dependencies by interface hash; their keys are unchanged.
- *A digest is forgotten* when a namespace is checked without the cache path at all
  (`module.rs`), so its dependants fall back to its key.

**Found while building:** a proof that starts using a declaration that comes *later* in its
namespace changes the order the namespace's declarations are made in, and so its digest
(own declarations are referred to by position): measured on a two-namespace project, where
moving the used declaration first kept the digest. Costs cut-off, not soundness; stage C's
"by path, not position" would fix it.

