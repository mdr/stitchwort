# SW-4714 Fable review: interface-digest cache, stage C

Review of `fedd8a3da` on `lane/SW-4714` (diff against the merge base with `main`), 24 Nov
2026, by the design's author (docs/proposals/interface-digest-cache.md, "Stage C design
(SW-4713)"). Marks: **[measured]** a probe I ran with the lane's release binary,
**[read]** code read at the site, **[not checked]**.

## Verdict

**Sound to merge.** I found no stale replay in 14 two-namespace probes, the scan audit
finds no reader of a left-out helper or of a plain theorem's place, the stream is
unambiguous, and the safety net does turn a marking bug into "can't be cached". Two low
findings (a candidate filter wider than the design's, a missing test), neither a trust
problem.

## How the probes work

Each case is a project `A`, `B` (`B` imports `A`), checked cold into a cache, then with
`A` edited (plain `check`, so `B` is left out on a hit), then `--recheck`, then the edited
project into a fresh cache, then `--no-cache`. A stale replay would be: `A`'s digest equal
before and after the edit (so `B` is a hit) while `B`'s digest from the fresh cache differs
from the one stored before the edit, or the output differs from `--no-cache`. `B` holds
its observables in `def`s (of proposition type where a proof is the observable), so they
are in `B`'s digest. Script and cases: the review scratch folder, `try.sh` and `cases/`
(not kept in the repo; each case is a few lines and is described below).

## 1. Stale-replay attempts **[measured]**

| Case | Edit to `A` | `A`'s digest | `B` | Fresh `B` = stored `B`, output = `--no-cache`, `--recheck` clean |
|---|---|---|---|---|
| base | a `match` on `one + 0` added to a proof | same, 1 left out | hit | yes |
| unf | the same, in a theorem with `unfolding f`; `B` has an `opaque def … unfolding f` and uses the theorem | **changes**, 0 left out | elaborated | yes |
| unf2 | that helper's arms change | **changes**, 0 left out | elaborated | yes |
| order | two plain theorems swap places in the source, one proof now uses the other and a later computing `def` through a lifted `match`; `B` has `byFacts [second, first]` in a `def` | same, 1 left out | hit | yes |
| rec | a recursive theorem's helpers (which call it, so they join its group) change shape and number; `B` has a `def` of proposition type calling it, a theorem, and a `def` matching on its proof | same, 2 then 3 left out | hit | yes |
| inst | a proof starts using a later instance through `"${Coin.Heads}"` in a lifted `match` | same | hit | yes |
| instfirst, instnamed | the same with the theorem written before two instances, by interpolation and by naming `Coin.instShow` in the scrutinee, so the second instance could move before the first | same | hit | yes |
| local | a local theorem in a proof (named from `B` as `A.t.lem`) gains a `match`, and so does the proof around it | same, 2 left out | hit | yes |
| localdef | a local `def` and local theorem inside a lifted arm, both used from `B`; the enclosing `match` changes | **changes** | elaborated | yes |
| samename | `B` has a theorem and `def`s with `A`'s names, each lifting its own `match` | same | hit | yes (`B.oneIsOne.%match1` private in `B`, the `def`s' kept) |
| stmt | a theorem with a `match` in its statement gains two in its proof; `B` uses the statement as written and unfolded | same, 2 left out | hit | yes: the statement's helper keeps `%match1` |
| datamove | a proof starts matching on a value of the later of two data types; `B` uses both types and derived `==` | same | hit | yes |
| reading | an `@[reading]` theorem's proof gains a `match` and starts using a later theorem; `B` has `if small n` and a `cases` proof through the reading | same, 1 left out | hit | yes |

Where the digest stayed equal across an edit that might reorder ordered declarations
(inst, instfirst, instnamed, datamove), the fresh-cache digest is equal too, and ordered
records are written in id order with no sort **[read: `digest_plan`'s loop]**, so the
order did not change: instances and data types are not moved by a proof that starts
using them.

Not constructible, as the design said: a helper shared by a proof and a computing
definition, an instance or a derive (a helper is named under one owner); a dependant
naming a helper (`%` doesn't lex in a name). A theorem that becomes an instance or gains
a row changes its record's `instance` flag or adds the row, both written.

## 2. The scan audit, against the built tree **[read]**

Grep of `env.defs()`, `namespace_defs`, `tables.lifted` / `.lifted.` in `crates/elab/src`
and `crates/driver/src` outside `cache/`, and of loops over definitions in
`crates/core/src`. Every site in the design's table (C.3 P5 item 5) is still there and
reads as described. Sites the table did not list:

| Site | What it does | Verdict |
|---|---|---|
| `goals.rs:1194,2114`, `module.rs:3336`, `matching.rs:2625,3176`, `module.rs:1024-1055` | a bounds check or a read of one id taken from a term | not a scan |
| `auto.rs:1597` | sizes a per-id cache | not a scan |
| `counterexample/mod.rs:398,422`, `timings.rs:134`, `library.rs:988,1595`, `lib.rs:1463,1618` | counts taken as marks | own unit |
| `module.rs:526` | the progress display | in no entry |
| `state/paths.rs:86` (`DeclPaths::sync`) | the path index; read by exact path (`unique_def`), by the cache's dependency records only | a private helper's path is asked for only by an entry whose terms mention it (C.3 (a)) |
| `search.rs:1395,1408` (`search_candidates`) | every declaration | callers are `driver/src/search.rs:625` and `search_at.rs:1441`: report-time |
| `queue.rs:2455`, `congruence.rs:693` | tests | none |
| `decreasing/plain.rs:876` (pushes to `lifted`) | see finding 1 | |
| `crates/core`: `native.rs:343,353` | sorts the native tables | no scan of definitions |

`congruence.rs:86` uses the definition count as a cache stamp, then looks lemmas up by
name beside the function. `opaque.rs:490` tests a `%match` head already in hand from a
term. So P5 and P6 hold as far as this grep reaches: no scan selects a non-instance,
non-theorem `%` helper by anything but an exact constructed name (`%step` only), and none
orders plain theorems by id into a result a namespace keeps. As in the design, this is
not a proof that the grep is complete.

## 3. The position-free stream **[read]**, written and replayed digests **[measured]**

- An own declaration is `0, path, ordinal`; an outside one is an odd number; before this
  change an own one was an even number. `0` can only start an own reference, the string is
  length-prefixed, so it is a prefix code. Definitions and data types are told apart by
  where the grammar expects each, as before.
- `(path, ordinal)` is injective over own definitions (`digest_prep` counts every own
  definition, left-out ones included, so leaving one out never renumbers a kept one's
  ordinal: a kept definition that shares a path with a private one keeps its number).
- The record list is counted, each record carries `theorem`, `instance` and the `sealed`
  flag, and a theorem is in the trailing path-sorted part exactly when it is sealed, not
  an instance and keys no row, all of which the stream shows. Two states with the same
  stream have the same ordered records in the same order and the same plain theorems.
- `ordered_before` has `n + 1` entries, indexed by `defs_before` in `0..=n` **[read]**.
- Keyed rows (`encode_rows`) stay sorted by id; a key is recorded in `Key` context, so a
  theorem that keys a row is ordered, and id order is checking order among ordered
  definitions. The tables with their own sorts (`new.sort_by_key`, `helpers.sort()`) and
  the sequences write the real order, so they can only show more, never hide it.
- The term writer is replaced when the context crosses into or out of a candidate's, in
  the recording pass only, whose bytes are thrown away. The replacement is
  `TermWriter::default()`, not by-content: it skips fewer nodes, so it records more, never
  less.
- Written and recomputed digests agree: `--recheck` reported no mismatch in all 14 probes,
  and the lane's `after_edit_holding` asserts `digest_mismatches == 0`.

## 4. The safety net **[read]**

`Out::def` in the final pass calls `fail` for any own reference to a private helper;
`encode_pass` returns `Err(problem)` at its end (`mod.rs:2955`), `interface_digest`
propagates it, and the namespace is "can't be cached": it keeps a text key and nothing
above trusts a digest. Under `--recheck` the same failure is a digest mismatch. Every own
definition the digest stream writes goes through `Out::def`: the one raw write
(`m.0 - before.defs`, the group list) is now `if !digest`, and the other raw index writes
are data types' (`datas_before`, data groups), which are never left out.

What the net covers: a root the recording pass missed (a skipped node, a context left as
`Own`). What it cannot cover, by construction: a reader that never goes through a term
(sections 1 and 2 are the evidence there), and a reference wrongly recorded as an edge
because a context was `Own` when it should have been a root. For the latter I read the
three places a context becomes `Own`: the definition loop (set per record, reset to
`Root` at the end of each), `GrowVec::encode_owned_since` and `encode_rows(.., owned)`
(set per row, `row_end` after each). An early `return Err` between them abandons the
pass. Not exercised by a test: it needs an injected marking bug.

## 5. `FORMAT` 45 and the pins

`FORMAT` is 44 → 45 and is in every key, so no entry holding a stage A digest is read by
this build, including with `--carry-over`. `the_digest_of_a_fixed_project_is_pinned`
passes with the re-pinned values; my `base` probe reproduces `PINNED_A`
(`52d79132…f098`) from the CLI.

## Findings

1. **Low. The candidate filter is wider than the design's.** `digest_prep` takes any own
   definition with a `lifted` row whose name contains `%` and that isn't a theorem or an
   instance. The design's C.1 says `owner.%matchN`, and its no-constructed-name argument
   was a grep of `%match` only. `lifted` also gets the twins of `decreasing/plain.rs:876`,
   named `H.%plain`. Today that changes nothing: a twin is called from `f.%plain`'s body,
   which is kept, so it is always reached; and no code builds a `%plain` name to look one
   up **[read: grep of `%plain` in elab, driver, core, js, rt]**. But a later helper kind
   pushed to `lifted` would become a candidate without anyone asking the C.1 question of
   it. Fix: require the name's last segment to start `%match`, or say at
   `Tables::lifted` that pushing a row makes the helper a candidate. No repro: no
   behaviour differs.
2. **Low. No test for a theorem with `unfolding`.** Measured (`unf`, `unf2`): its helper
   is kept (0 left out), the digest changes on a `match` edit and `B` is elaborated, equal
   to `--no-cache`. That is the design's "costs cut-off only" row, and it should be pinned
   by a test so a later change to `in_body_of` can't make such a helper private
   unnoticed. Repro: `opaque def f (n: Nat): Nat := n + 1`, `theorem fOne: f 0 = 1` with
   `unfolding f` and proof `byComputing`, edited to `match f 0 + 0 with | _ =>
   byComputing`.
3. **Note.** The notes' "no proof edit moves a data type" held in the one probe
   (`datamove`); the digest writes data types by id either way, so a move would cost
   cut-off, not correctness.

## Not checked

- Mutual groups of a theorem with a computing definition; `@[walk]` lemmas; record-update
  helpers (`update_shown` rows); `decreasing` theorems; derives beyond derived `==`.
- Entries with navigation, the editor's path, `--only`, `--carry-over`.
- `crates/core`'s readers of a definition's group and the back ends (the lane read them;
  I did not).
- Two own declarations sharing a path (the ordinal's case) in a probe.
- The safety net by fault injection; the `tools/fmt` measure and the extra pass's cost.
- Whether the grep in section 2 finds every scan.

## Tests run

`package(stitchwort-driver) & binary(projects) & test(/check_cache::digest::/)`: 32
passed, 24 s. The 14 probes above, each under 2 s.
