#!/usr/bin/env bash
# The stage 3 pilot (SW-4730; "Stage 3 pilot" in
# docs/proposals/parallel-checking.md): does a namespace's interface digest
# come out the same when its theorems' proofs are left out? For the
# orchestrator or Overmind, not a lane: it checks a whole project with
# every namespace elaborated twice (an interface pass, rewound, then the
# full check), so it takes about twice a cold check (tools/fmt: about 3
# minutes on a quiet machine).
#
#   measure_interface_pilot.sh BINARY PROJECT OUT_DIR
#
# BINARY is a build of the branch with the pilot (`STITCHWORT_INTERFACE_PILOT`;
# a copy of the checkout's target/release/stitchwort also needs --std-dir).
# PROJECT is the project folder (tools/fmt, aoc). The cache goes in
# OUT_DIR/cache, fresh each run, and the pilot's lines in OUT_DIR/pilot.txt.
# Prints: matches out of total; the namespaces that differ, grouped by
# their set of causes; and how many namespaces each single cause touches.
# A cause is one of: proof-local-def (a `def`/`theorem` written in a proof),
# proof-helper:%KIND (a generated helper only the full check makes),
# def-hash (a declaration both have, with another interface hash),
# table:NAME (rows of an elaborator table only one pass has), names,
# data types, errors-in-interface-pass (something needs a proof's
# contents: a proof-local def named outside it), no-digest-* (a pass whose
# entry can't be written), stream:PARTS (none of those: only the digest's
# bytes differ), no-report (the namespace wasn't elaborated through the
# cache: a namespace with a syntax error, say).
set -euo pipefail
bin=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
project=$(cd "$2" && pwd)
mkdir -p "$3"
out=$(cd "$3" && pwd)
rm -rf "$out/cache"
echo "== pilot over $project"
start=$(date +%s)
(cd "$project" && STITCHWORT_INTERFACE_PILOT=1 nice -n 10 "$bin" check \
    --cache-dir "$out/cache" > "$out/stdout.txt" 2> "$out/stderr.txt") || true
echo "   took $(( $(date +%s) - start )) s; $(tail -1 "$out/stderr.txt")"
grep -E "^(interface-pilot: |  )" "$out/stderr.txt" > "$out/pilot.txt" || true
heads="$out/pilot.heads"
grep "^interface-pilot: " "$out/pilot.txt" > "$heads" || true
total=$(wc -l < "$heads" | tr -d ' ')
matches=$(grep -c ": match (" "$heads" || true)
echo "   match: $matches of $total namespaces"
awk '
    /^interface-pilot: / {
        if (match($0, /deferred [0-9]+, kept [0-9]+/)) {
            split(substr($0, RSTART, RLENGTH), a, /[ ,]+/); D += a[2]; K += a[4]
        }
    }
    END { printf "   theorems: %d proofs left out, %d elaborated anyway (recursive, mutual or decreasing)\n", D, K }
' "$heads"
echo "   differing, by set of causes:"
grep -v ": match (" "$heads" | sed -E 's/^interface-pilot: ([^:]+): [a-z ]+ \[causes: ([^]]*)\].*/\2\t\1/' \
    | sort | awk -F'\t' '
        $1 != last { if (last != "") printf "     %3d  %s: %s\n", n, last, names; last = $1; n = 0; names = "" }
        { n++; names = names (names == "" ? "" : " ") $2 }
        END { if (last != "") printf "     %3d  %s: %s\n", n, last, names }'
echo "   by single cause (namespaces):"
grep -v ": match (" "$heads" | sed -E 's/.*\[causes: ([^]]*)\].*/\1/' | tr ',' '\n' \
    | sed 's/^ *//' | sort | uniq -c | sort -rn | sed 's/^/   /'
echo "   details: $out/pilot.txt"
