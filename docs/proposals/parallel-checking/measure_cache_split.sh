#!/usr/bin/env bash
# How much of a cache entry is proofs (SW-4729, step 0 of stage 2 in
# docs/proposals/parallel-checking.md section 10). For the orchestrator or
# Overmind, not a lane: it runs a cold whole-project check of tools/fmt and
# of aoc (about 2 minutes each on a quiet machine, one after the other).
#
#   measure_cache_split.sh BINARY REPO_ROOT OUT_DIR
#
# BINARY must be the checkout's own target/release/stitchwort (a copy also
# needs --std-dir). For each project it prints the total over the namespaces
# written, and the ten largest namespaces by entry size. Columns are bytes
# of the entry's streams: the whole entry, the proofs of sealed theorems and
# their private helpers, source positions, navigation, warnings, and the
# interface (what the digest hashes). The percentage is proofs / entry.
# "Proofs" is entry minus interface, positions, navigation and warnings, so
# it is an estimate: the digest's terms are written by content (shared nodes
# once, absolute node numbers), the entry's by address.
set -euo pipefail
bin=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
root=$(cd "$2" && pwd)
mkdir -p "$3"
out=$(cd "$3" && pwd)
for project in tools/fmt aoc; do
    name=$(basename "$project")
    rm -rf "$out/cache-$name"
    echo "== cold check of $project"
    (cd "$root/$project" && STITCHWORT_CACHE_DEBUG=1 nice -n 10 "$bin" check \
        --cache-dir "$out/cache-$name" > /dev/null 2> "$out/$name.log") || true
    grep -E ": written, .*entry [0-9]+ bytes" "$out/$name.log" > "$out/$name.written" || true
    awk '
    {
        ns = $3; sub(/:$/, "", ns)
        n = split($0, a, "entry "); split(a[n], b, " ")
        entry = b[1]
        match($0, /proofs [0-9]+ bytes/); split(substr($0, RSTART, RLENGTH), p, " "); proofs = p[2]
        match($0, /positions [0-9]+/); split(substr($0, RSTART, RLENGTH), q, " "); pos = q[2]
        match($0, /navigation [0-9]+/); split(substr($0, RSTART, RLENGTH), r, " "); nav = r[2]
        match($0, /warnings [0-9]+/); split(substr($0, RSTART, RLENGTH), t, " "); warn = t[2]
        match($0, /interface [0-9]+ bytes/); split(substr($0, RSTART, RLENGTH), u, " "); iface = u[2]
        b_bytes = 0
        if (match($0, /part B [0-9]+ bytes/)) { split(substr($0, RSTART, RLENGTH), v, " "); b_bytes = v[3] }
        E += entry; P += proofs; O += pos; N += nav; W += warn; I += iface; B += b_bytes
        printf "%d %s %d %d %d %d %d\n", entry, ns, proofs, pos, nav, warn, iface > "/dev/stderr"
    }
    END {
        printf "TOTAL entry %d  proofs %d (%.1f%%)  positions %d (%.1f%%)  navigation %d (%.1f%%)  warnings %d  interface %d (%.1f%%)\n",
            E, P, 100*P/(E+(E==0)), O, 100*O/(E+(E==0)), N, 100*N/(E+(E==0)), W, I, 100*I/(E+(E==0))
        printf "TOTAL part B (what a load without proofs skips, SW-4735) %d (%.1f%%)\n", B, 100*B/(E+(E==0))
    }' "$out/$name.written" 2> "$out/$name.rows"
    echo "   top 10 namespaces by entry size: entry, name, proofs (share), positions, navigation, interface"
    sort -rn "$out/$name.rows" | head -10 | awk '{ printf "   %10d  %-32s proofs %9d (%4.1f%%)  positions %8d  nav %8d  interface %9d\n", $1, $2, $3, 100*$3/$1, $4, $5, $7 }'
    echo "   namespaces written: $(wc -l < "$out/$name.written")"
done
