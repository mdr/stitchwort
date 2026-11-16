# SW-3603: std's warnings (16 Nov 2026)

How to see them: `stitchwort check --std Std --warnings` (or any `--std` target)
prints every warning the core and the named library files give, then a
`code`, `file`, `count` table on standard output. It skips the check cache,
since a file the cache answers for has no warnings to give. Plain `check`
still shows programs nothing from the library. The same counts are pinned in
`crates/driver/tests/library/warning_pins.tsv` (project, file, code, count;
`std` is the only project so far) and checked by
`warning_pins::the_library_warnings_stay_within_their_pins`: each count is a
ceiling, the table only goes down.

## Before (205 warnings)

Every warning is `W-PROOF-CHAIN`; no other code fires anywhere in std
(`W-ARROW-FORALL`, `W-THEOREM-FORALL`, `W-UNREACHABLE`, `W-REDUNDANT`,
`W-DOC-LINK` and the rest: 0). 109 of the chains are `trans a (trans b c)`
(three terms), the others are longer or written over several lines. All are
`Eq.trans`; none are `Iff.trans` or `<=` chains.

## By namespace

| Namespace | Before | Now |
|---|---|---|
| Array | 1 | 1 |
| Float | 14 | 14 |
| Function | 1 | 0 |
| Int | 17 | 17 |
| List | 38 | 36 |
| Map | 53 | 53 |
| Mod | 12 | 12 |
| Nat | 24 | 24 |
| NonEmptyList | 1 | 1 |
| Omega | 11 | 11 |
| Parse | 3 | 3 |
| Ring | 16 | 16 |
| Set | 3 | 3 |
| Text | 1 | 1 |
| Vec | 2 | 2 |
| core | 8 | 0 |

## By file, where any remain or were fixed

| File | Before | Now |
|---|---|---|
| Array/Array.sw | 1 | 1 |
| Float/Theory.sw | 14 | 14 |
| Function/Function.sw | 1 | 0 |
| Int/Int.sw | 15 | 15 |
| Int/Sums.sw | 2 | 2 |
| List/Distinct.sw | 2 | 0 |
| List/Grid.sw | 1 | 1 |
| List/Lemmas.sw | 11 | 11 |
| List/SortLemmas.sw | 21 | 21 |
| List/Split.sw | 2 | 2 |
| List/Toolkit.sw | 1 | 1 |
| Map/Map.sw | 11 | 11 |
| Map/Raw.sw | 1 | 1 |
| Map/Spec.sw | 41 | 41 |
| Mod/Mod.sw | 12 | 12 |
| Nat/Arith.sw | 14 | 14 |
| Nat/Bits.sw | 4 | 4 |
| Nat/Digits.sw | 6 | 6 |
| NonEmptyList/Lemmas.sw | 1 | 1 |
| Omega/Sound.sw | 11 | 11 |
| Parse/Chars.sw | 1 | 1 |
| Parse/ReadsChars.sw | 1 | 1 |
| Parse/RunsTokens.sw | 1 | 1 |
| Ring/Sound.sw | 16 | 16 |
| Set/Spec.sw | 3 | 3 |
| Text/Text.sw | 1 | 1 |
| Vec/Vec.sw | 2 | 2 |
| core | 8 | 0 |

## Shape of the hits

40 of the 205 sit on one line (`Eq.trans a (Eq.trans b c)` of short lemma
applications, such as `Bool.falseNotTrue (Eq.trans c.flipped (Eq.trans (same x) d))`).
A calc says the same with more words there. If Matt would rather not
have those flagged, the narrowing is "report a nest only when it spans lines"
(`crates/elab/src/proof_chain.rs`); not applied.
