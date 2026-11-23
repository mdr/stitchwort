# SW-4707 review notes: check-cache keys by interface digest, stage A

For the Fable review of SW-4707 (docs/proposals/interface-digest-cache.md, stage A;
D3728). What was built, the trust argument as the code has it, the exclusions, and what
the lane could not verify. The design note's "As built (stage A)" section has the step 0
counts and the choices beyond the text.

## What to check first

1. **The key** (`crates/elab/src/cache/mod.rs`, `namespace_cache_key`). For each `D` in
   the closure: `("digest", d)` if `session.namespace_keys[D].digest` is set, else
   `("text", key)`; then `D`'s `project_names` set. Planning declines when a digest is
   missing. Check that a digest is set only in three places and cleared everywhere else:
   - set: after a replay with no error (`elaborate_namespace_cached`, `Ok((warnings,
     digest))`), after an entry is written (`encode_namespace` → `Ok((entry, digest))`),
     and by `plan_namespace` when `plan_entry` accepts the entry (from its header);
   - cleared: at the start of `elaborate_namespace_cached` (`known(None)`), and by
     `forget_namespace_digest` when `module.rs` checks a project namespace without the
     cache path. It lives in the same `Logged` map as the key, so a rewind takes it back
     with the key.
   Not written (errors, goals, an unfinished declaration, a failed dependency,
   uncacheable, cancelled) means no digest, hence the text key (rule 3).
2. **The exclusions** (`encode_pass`, `digest: bool`): exactly
   - spans: `Out::span` and `Out::span_after` write nothing (this also covers `Loc` nodes,
     probe spans, names' spans, table rows' spans and the file table, which stays empty);
   - the warnings section (the pass is called with `&[]`);
   - a body for which `has_interface` holds (now `pub` in `crates/core/src/hash.rs`), with a
     flag written either way so the stream stays unambiguous;
   - the navigation section;
   - the `pre` section's library files with keys and `include` records (design table rows
     2 and 3).
   Own declarations' recorded hashes are `interface_hash` in the digest (`def_hash` in the
   entry). Everything else is written by the same code as the entry.
3. **Dependency records by interface hash** (`Out::def` and `decode`), for library and
   namespace entries both. The stored own-declaration hashes that replay puts in the hash
   cache are still full hashes.
4. **Rule 4** (`foreign_file_hash`, `foreign_files_unchanged`, called by `plan_entry` and
   `replay_namespace` before anything changes): for each file in the entry's file table
   that isn't the unit's own, a library file's text hash, or for a project file the hash of
   every namespace's sources. Coarse but sound for project files; check the library-file
   case is right to rely on the index's text (the same text library keys use).
5. **`--recheck`** (`replay_namespace`): takes the snapshot after `load_needs` as
   `capture_after_needs` does, computes the digest through `namespace_parts` from the
   replayed state, and on a mismatch adds `E-CACHE-DIGEST` (not undone: the tables are in).
   The existing recheck tests (`check_cache::a_kernel_side_change_*`,
   `..._refuses_on_recheck_*`) now also run this computation and found no mismatch.

## The trust argument as built

Claim: if `K(N)` matches, elaborating `N` now gives the stored entry. `K(N)` fixes `N`'s
text and, per dependency, either its text key (the old argument) or its digest plus its
`project_names`. A digest fixes every part of `D`'s entry except sealed proofs, positions,
`D`'s warnings and navigation, and `D`'s library-file and `include` records. The proof
needs P1 to P4 of the design (section 2):

- P2 (no declaration reads a sealed proof) is the design's audit plus the kernel's rule 6;
  the lane added nothing to it. Not re-read: `crates/core` body reads by functions the
  elaborator calls, and `live/trial.rs` (design 2.1).
- P3 (positions) relies on all positions going through `span`/`span_after`. The lane
  checked the encoder and `cache/rows.rs`: their raw integer writes are counts, indices
  and flags, not positions. **Not checked:** positions rendered into *text*, which the
  digest keeps and which rule 4 can't see: a warning message, note or string literal in
  `N` that quotes a line and column in `D`'s file would go stale. None was found, but no
  search of every message was made.
- The library-file records left out: each dependant records and compares its own reach;
  `D`'s needs (which make the reach) are in the digest.
- `project_names` is in the key. `project_syntax_errors` isn't: a `D` with a syntax error
  is never written, so it has no digest.

## Exclusions the reviewer might want to question

- `pre.includes` left out of the digest: an `include`d file's text is in the terms that
  read it, so a changed file changes the digest when it changes a term. A changed included
  file that changes nothing in `D`'s result leaves `N` replayed, which is right.
- Library entries get a digest too (stage B's field), unused for now.

## What the lane couldn't verify

- The measure itself (a whole-project check): the script is below, for the verifier.
- Namespaces of `tools/fmt` that are never cached (step 0's third count): the script keeps
  the `can't be cached` lines.
- Entries with navigation in another project file: none found in tests; no `+nav` entries
  in the `tools/fmt` cache to count. The rule-4 miss for a project file is tested at unit
  level only.
- Carried-over entries (`--carry-over`): their digests were computed by another build. A
  build whose digest differs in meaning without a `FORMAT` bump would make the namespaces
  above trust the wrong thing; the design's rule is "a change to what the digest covers
  bumps `FORMAT`". Nothing enforces it.
- Cost of the second encoding pass: not measured.

## Tests

`crates/driver/tests/projects/check_cache/digest.rs` (18), and
`cache::tests::a_position_in_another_namespaces_file_stops_fitting_when_a_source_changes`.
Two existing tests changed, both because a comment in a namespace below now replays the
one above: `an_edit_re_elaborates_the_namespace_and_what_uses_it` (adds a body edit that
still re-checks) and `a_replayed_namespaces_instances_and_extensions_are_usable` (its edit
is now a new definition, so what it tests, elaborating after a replay, still happens).

## The measure script

Run with main's binary and the lane's, each copied out first:

    measure.sh /path/to/stitchwort /path/to/checkout

It prints `cold`, `warm` and `edited` lines: namespaces elaborated, namespaces from the
cache (left out or replayed), and wall time. Expected after SW-4707: `edited: elaborated
1`; before it, `Fmt.SpellProofs` and every namespace above it.

```bash
#!/usr/bin/env bash
# SW-4707's measure (docs/proposals/interface-digest-cache.md §6 step 7):
# a proof-only edit to tools/fmt/src/Fmt/SpellProofs.sw line 32, which moves
# every later position in the file, then a plain `check` through a warm
# cache. Run it once with main's binary and once with the lane's.
#
# Usage: measure.sh STITCHWORT_BINARY CHECKOUT [CACHE_DIR]
#   STITCHWORT_BINARY  a release `stitchwort` (copy it first if you rebuild)
#   CHECKOUT           the checkout whose tools/fmt and std to use (its
#                      tools/fmt/src/Fmt/SpellProofs.sw is edited and put back)
#   CACHE_DIR          default: a new temporary directory, so the run never
#                      touches tools/fmt/.stitchwort
#
# Prints, for the warm run and for the run after the edit: how many of the
# project's namespaces were elaborated and how many came from the cache
# (`--timings` rows marked "(cached)": left out by a plain check or
# replayed), and the wall time. Before SW-4707 the edited run elaborates
# Fmt.SpellProofs and everything that depends on it; after it, Fmt.SpellProofs
# alone (expected: 1 elaborated). With STITCHWORT_CACHE_DEBUG the lane's
# binary also says "can't be cached" for every namespace that never gets an
# entry: those lines are kept in $out/edited.debug.
set -euo pipefail
bin=$1
checkout=$2
cache=${3:-$(mktemp -d)}
proj=$checkout/tools/fmt
file=$proj/src/Fmt/SpellProofs.sw
out=$(mktemp -d)
export STITCHWORT_STD_DIR=$checkout/crates/elab/src/std

line=$(sed -n 32p "$file")
expected='theorem spellsNil: SpellsAll [] [] := (byComputing, byComputing, byComputing)'
if [ "$line" != "$expected" ]; then
  echo "line 32 of $file isn't the expected proof: $line" >&2
  exit 1
fi
cp "$file" "$out/SpellProofs.sw.orig"
trap 'cp "$out/SpellProofs.sw.orig" "$file"' EXIT

count() {
  # The --timings table's namespace rows: Fmt.* and Syntax.* units.
  local t=$1
  local cached elaborated wall
  cached=$(grep -cE '^(Fmt|Syntax)(\.[A-Za-z0-9]+)* \(cached\) ' "$t" || true)
  elaborated=$(grep -E '^(Fmt|Syntax)(\.[A-Za-z0-9]+)* +[0-9]' "$t" | grep -vc '(cached)' || true)
  wall=$(grep -oE '^wall [0-9.]+ ms' "$t" || echo 'wall ?')
  echo "elaborated $elaborated, from the cache $cached, $wall"
}

run() {
  local name=$1
  (cd "$proj" && STITCHWORT_CACHE_DEBUG=1 "$bin" check --timings --cache-dir "$cache") \
    > "$out/$name.out" 2> "$out/$name.debug" || true
  # --timings writes its table to standard error with the debug lines.
  cat "$out/$name.out" "$out/$name.debug" > "$out/$name.all"
  echo "$name: $(count "$out/$name.all")"
}

run cold
run warm
sed -i '32s/:= (byComputing, byComputing, byComputing)$/:= ((byComputing, byComputing, byComputing))/' "$file"
run edited
echo "never cached: $(grep -c "can't be cached" "$out/edited.debug" || true) lines (see $out/edited.debug)"
echo "outputs in $out; cache in $cache"
```

## Step 0 script (`files_table.py`)

For FORMAT 43 entries; for 44, skip 32 more header bytes after the exact flag (`FORMAT44=1`).

```python
"""Step 0 count: for each namespace entry of one build in a check-cache
directory, list the files its spans fall in that aren't the namespace's own.
Usage: python3 -I files_table.py CACHE_CHECK_DIR BUILD_PREFIX"""
import os, sys

def uint(b, i):
    n = s = 0
    while True:
        x = b[i]; i += 1
        n |= (x & 0x7f) << s; s += 7
        if x < 0x80:
            return n, i

def blob(b, i):
    n, i = uint(b, i)
    return b[i:i + n], i + n

d, build = sys.argv[1], sys.argv[2]
total = foreign_entries = 0
kinds = {}
for name in sorted(os.listdir(d)):
    if not name.startswith(build + "-ns."):
        continue
    ns = name[len(build) + 4:].rsplit("-", 1)[0]
    b = open(os.path.join(d, name), "rb").read()[:-32]
    i = 8 + 4 + 32 + 16
    _, i = blob(b, i); _, i = blob(b, i)
    i += 33 + (32 if os.environ.get("FORMAT44") else 0)
    n, i = uint(b, i)
    for _ in range(n):
        i += 1; _, i = blob(b, i); i += 32
    body, i = blob(b, i)
    j = 0
    n, j = uint(body, j)
    for _ in range(n):
        _, j = blob(body, j)
    n, j = uint(body, j)
    files = []
    for _ in range(n):
        f, j = blob(body, j); files.append(f.decode())
    own_prefix = "project:src/" + ns.split("+")[0].replace(".", "/")
    foreign = [f for f in files if not f.startswith(own_prefix + ".sw") and not f.startswith(own_prefix + "/")]
    total += 1
    if foreign:
        foreign_entries += 1
        print(ns, foreign)
        for f in foreign:
            k = f.split(":")[0]
            kinds[k] = kinds.get(k, 0) + 1
print(f"{foreign_entries} of {total} entries have another unit's file in their file table; by kind {kinds}")
```
