# SW-4714 review notes: interface-digest cache, stage C

For the Fable review of SW-4714 (docs/proposals/interface-digest-cache.md, "Stage C
design (SW-4713)" and "As built (stage C)"; D3729). Option (a) of C.6 was built: plain
theorems by path, everything else in checking order.

## What to check first

1. **The marking is complete** (`digest_plan`, `Context`, `Out::def`'s recording,
   `Encoding::enter` in `crates/elab/src/cache/mod.rs`). A candidate is private only if
   no reference to it is recorded in `Root` or `Key` context and no candidate reached
   from one has an edge to it. Check that every place an entry writes an own definition
   goes through `Out::def` (`Encoding::def`, `Encoding::term`'s `Term::Def` nodes,
   `Encoding::global`, group lists now in digest mode), and that the context is `Own(c)`
   only while candidate `c`'s own record or owned row is written:
   - the definition loop sets `Own(id)` for a candidate's record and `Root` after it;
   - `GrowVec::encode_owned_since` (`lifted`) and `OwnedBy::encode_owned_since`
     (`match_columns`, `update_shown`), through `encode_rows(.., owned = true)`, set it
     for a candidate's row; every other table's key is `Key`, its value `Root`.
   The net under the marking: in the final pass `Out::def` fails the encoding on any
   reference to a private helper, so a missed root costs "can't be cached", not a digest
   that omits something written.
2. **The term writer's node reuse** in the recording pass: it skips a node already
   written, so `Encoding::enter` replaces the writer when the context crosses into or out
   of `Own(_)`. Between `Root` and `Key` it doesn't (a key is written by `Out::def`
   directly, and both are roots).
3. **Plain theorems** (`digest_plan`): `has_interface`, not `instance`, not recorded as a
   key. Check P6 against the scans below: a plain theorem is in no list a dependant
   builds by id order.
4. **Position-free stream** (final pass only; the entry's own encoding is unchanged):
   own definitions and data types as `(0, path, ordinal)` (outside ones stay odd
   numbers into `deps`); group lists sorted by `(path, ordinal)`, none for a sealed
   theorem (its `sealed` flag is written first); definitions in `plan.order`; data
   types' `defs_before` as `plan.ordered_before`. Data types' group lists and
   `datas_before` stay positions (no proof edit moves a data type).
5. **Keyed tables' order**: `encode_rows` still sorts by id. Claim: in the final pass
   the rows left are keyed by ordered definitions (a plain theorem keys none, private
   helpers' owned rows are filtered), and ordered definitions are in id order, so this
   is the digest's order.
6. **`--recheck`** uses the same `interface_digest` from the replayed state; the
   candidates come from the replayed `lifted` rows, the ordinals from the replayed
   declarations, which replay admits in the entry's (checking) order.

## Exclusions, all of them

Stage A's (sealed bodies, spans, warnings, navigation, library-file and `include`
records) plus, new:

- a proof-private helper's record (name, path, flags, `unfolding` list, type, body,
  group, run body, hash), and its rows of `lifted`, `match_columns` and `update_shown`;
- a sealed theorem's group list;
- own declarations' positions among the unit's (replaced by path and ordinal), the
  plain theorems' place in checking order, and the private helpers and plain theorems in
  data types' `defs_before`.

## The unread code the design flagged

- `crates/core` readers of a definition's group: `check.rs:2783` (set), `2798`
  (`recursive`, read only for unfolding; theorems never unfold), `3381` (transparency
  closure over a *named* definition's opaque non-theorem group-mates: that definition is
  kept and its group list makes them roots), `hash.rs:212` (in the digest via the
  computing member's hash). Back ends: `js/src/lib.rs:2677,3051`,
  `rt/src/specialise.rs:366`, run time only. Read, not run.
- A recursive theorem's helper joins the group when its body mentions the pending owner
  (`lift.rs`, `join && pending`). The recursive-theorem test replays `B`.
- A theorem's stored `unfolding` list does name its own helpers: `in_body_of`
  (`opaque.rs`) appends the helpers admitted on their own. Those helpers are then roots
  and kept: today's behaviour for such theorems, as the design says. Not counted in
  `tools/fmt`; no test.

## The scans of C.3 P5 item 5

Not redone against this diff: the diff adds no scan, and the list is the design's
(`auto.rs`, `reading.rs`, `opaque.rs`, `check.rs:1029`, `tailrec.rs`,
`equations.rs`, `congruence.rs`, `interfaces.rs`, `equation_notes.rs`, `assume.rs`,
`module.rs`, `decreasing.rs`, `lib.rs:1463`, `library.rs`, report-time walks in the
driver). **For the Fable review**, as C.7 asks. Comments now sit at `Tables::lifted` and
`Env::defs` saying a scan must not let such a helper (or a plain theorem's place) change a
result another namespace caches.

## What the lane couldn't verify

- The measure (a whole-project check): the script is below, for the verifier or Overmind.
- The extra pass's cost: one more encoding, without sealed bodies or navigation, per
  namespace written that has a candidate or a sealed theorem (almost all of
  `tools/fmt`'s). The measure's `cold` line shows it.
- How many `tools/fmt` theorems have an `unfolding` list (so keep their helpers).
- Option (b)'s case (a proof that starts using a later computing definition that moves
  past another): still a re-check above, tested only as equal to `--no-cache`.
- `crates/core`'s readers were read, not tested beyond the recursive-theorem case.

## Tests

`crates/driver/tests/projects/check_cache/digest.rs`: 13 new (`a_match_*`,
`a_proof_below_that_starts_using_a_later_*`, `a_reading_whose_proof_*`,
`private_helpers_in_two_namespaces_*`), the differential test extended with three
`match`-wrapped proofs, `BASE` reordered (`oneProof` after `oneIsOne`), the pins
re-pinned. `after_edit_holding` asserts the helper is in an entry (a `match` on a
variable isn't lifted) and runs `--recheck` after the edit.

## The measure script

`measure-c.sh BINARY CHECKOUT`, with main's binary and the lane's, each copied out first.
It prints `cold`, `warm`, `edited` (SW-4707's line-32 bracket edit) and `matched`
(line 32's proof wrapped in `(match 0 + 0 with | _ => …)`, which makes
`Fmt.SpellProofs.spellsNil.%match1`): namespaces elaborated, from the cache, wall time.
Then how many `Fmt.SpellProofs` entries hold the helper (at least 1: the `match` was
lifted) and, for the lane's binary, the debug "written" line with the counts left out.
Expected: `matched: elaborated` about 54 with main's binary (SW-4707's "before"),
`elaborated 1` with the lane's; `edited` 1 with both; `cold` a little slower with the
lane's (the recording pass).

```bash
#!/usr/bin/env bash
# SW-4714's measure (docs/proposals/interface-digest-cache.md C.5 step 7),
# extending SW-4707's (§6 step 7):
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
# Stage C: the same proof with a lifted `match` around it, which adds the
# helper Fmt.SpellProofs.spellsNil.%match1 (proof-private). Before SW-4714
# this re-checks what `edited` did before SW-4707; after it, 1.
cp "$out/SpellProofs.sw.orig" "$file"
sed -i '32s/:= (byComputing, byComputing, byComputing)$/:= (match 0 + 0 with | _ => (byComputing, byComputing, byComputing))/' "$file"
run matched
echo "helper made: $(cat "$cache"/check/*ns.Fmt.SpellProofs* | grep -a -c 'spellsNil.%match1' || true) entries hold spellsNil.%match1"
echo "left out (lane's binary only): $(grep -E '^check cache: Fmt.SpellProofs: written' "$out/matched.debug" || true)"
echo "never cached: $(grep -c "can't be cached" "$out/edited.debug" || true) lines (see $out/edited.debug)"
echo "outputs in $out; cache in $cache"
```
