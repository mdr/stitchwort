# SW-3071: where the playground's 35 s re-check goes

Measured 13 Nov 2026 (Sonnet lane), whole AoC project through the LSP `Inline` server with a `LayeredStore`, release build, machine under load (so rough).

| | Native | Browser |
|---|---|---|
| First check | 87–88 s (291 ticks) | 112 s |
| Re-check after editing Year2025/Day02 | 5.1–5.2 s (290 ticks) | 35.6 s |

Native re-check: 287 namespaces replayed from the store, 3 re-elaborated. A `sample` over repeated re-checks:

- replaying definitions (`admit_trusted_def` evaluating each): ~32%
- `LiveProject::answers` (whole-project `nav::index_data_of`), run twice: ~21%
- re-elaborating the edited namespaces: ~12%
- `library_unchanged` re-hashing library files per replayed namespace: ~6%
- `Store::read` cloning (SW-3062): 1 ms, 28 MB — not a hotspot
- session rewind: 40–100 µs

So the browser is 1.3× native on a cold check but 7× on a re-check: something wasm- or worker-specific dominates the re-check, and it is not measured yet.

A memo of library-file keys (cutting the median replay tick 4.2 → 3.4 ms) was tried and dropped: no end-to-end change natively or in the browser.

Options, in order: (1) per-phase timings in the browser worker (replay, `answers`, tick count) read from `window.editor.stats`; (2) don't replay namespaces the edit can't affect (non-linear session); (3) an incremental nav index.

The profiling test used is kept at `docs/reviews/SW-3071-profile-test.rs` (an `#[ignore]`d LSP test; not built).
