# SW-1742: does mimalloc make the test binaries faster?

Yes: about 12% less CPU on the heavy from-source std checks, well outside
the run-to-run spread. Measured 7 Nov 2026 on an otherwise idle machine, with
the release test build of the driver `library` binary, run from `crates/driver`.
Both binaries were built before any timing. Runs alternate system, mimalloc,
system, mimalloc, ... and use `/usr/bin/time -l`.

## `hash_stability::prelude` (5 alternating runs each)

1-minute load before each run: 3.5, 3.4, 3.4, 3.4, 3.1, 2.9, 2.7, 2.5, 2.3, 2.1
(each run is single-threaded, so the load is other work, not the test).

| | user s (median, range) | wall s (median, range) | max RSS (MB) |
|---|---|---|---|
| system allocator | 12.57 (12.56-12.58) | 12.65 (12.65-12.66) | 262 (262-263) |
| mimalloc | 11.07 (11.06-11.09) | 11.15 (11.15-11.55) | 246 |

Gain: user -11.9%, wall -11.9%, RSS -6%. The ranges do not overlap (the
gap is 1.5 s against a spread of 0.03 s). The first mimalloc run, 11.55 s wall,
is the outlier and still beats every system run.

## `std_library::` (36 tests, multithreaded; 2 clean pairs)

The group fills the machine itself (load 25-75 while it runs), so each run
waited until the 1-minute load was under 4 before starting. Only two pairs are
clean; a third attempt was stopped for time, and a first pair taken at load
2.8 / 25 (640 s vs 505 s user) agrees but is not counted.

| | user s | wall s | max RSS (GB) |
|---|---|---|---|
| system, run 1 / 2 | 625 / 620 | 85.3 / 72.4 | 5.20 / 5.34 |
| mimalloc, run 1 / 2 | 517 / 510 | 75.6 / 59.7 | 5.20 / 5.20 |

User CPU -17.5%. Wall time -11% to -17%, noisier because the group is parallel.
Memory is unchanged.

## Recommendation

A sweep is worth doing: the gain is above 5% and far outside the spread, on
both the single-threaded and the multithreaded workload, and memory does not
grow. Done here: the driver `library` binary (the biggest, which holds
`hash_stability` and `std_library`). Candidates for a follow-up, each needing
a one-line `#[global_allocator]` and `mimalloc` as a dev-dependency (already
workspace-pinned): the binaries that elaborate the std from source, in `elab`,
`cli` (tests that run the compiler in-process), `lsp`, `native` and
`driver/tests/elaboration`, `proofs`. Leave out `driver/tests/resources.rs`
and `search_at_aoc.rs` (already set their allocator), and `rt`'s
`effect_alloc.rs` and `state_match.rs`, which count allocations with their
own. Measure one or two others first: the gain depends on how
allocation-heavy each binary is. SW-1729's earlier null result was taken at
load 25-35, where timings are noise.
