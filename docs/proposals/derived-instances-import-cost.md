# What std's derived instances cost every importer (SW-3710)

**Status:** proposed, 17 November 2026. Measured at `da665940f` (after) and
`8b9c6ace9` (before: the merge parent of `2f4c14504`, SW-3369), both release
CLIs on Speedwell under load about 8, so seconds are best of three and
rough. Nothing was changed: every fix the profile points at either changes
what is derived or is a design, so this note stops for a decision.

## 1. The problem [measured]

D3609 (SW-3369) made std's own types derive `==`, `<`, printing and
`Finite`, like program types. Since then a cold load of a tiny program
that imports one std namespace (`crates/driver/tests/library/import_cost.rs`'s
programs, `stitchwort check --no-cache`, which checks the library files
from source; `STITCHWORT_TIMINGS=decls` sums the steps) costs:

| Program | Steps before | Steps after | Seconds before | Seconds after |
|---|---|---|---|---|
| `def n : Nat := 3` (no import) | | | 0.24 | 0.27 |
| Nat | 11.2M | 20.7M | 1.11 | 1.77 |
| Int | 17.3M | 27.1M | 1.62 | 2.40 |
| Text | 10.4M | 18.9M | 1.06 | 1.66 |
| Map | 31.7M | 45.0M | 2.76 | 3.90 |

(The CLI's sums run a little above the test's counts, 19.8M for Nat, since
the test's session differs slightly; the differences agree.) So about
+0.6 to +1.1 s, or +40 to +60%, on every cold start: a fresh session, an
empty cache, the playground, the first check after std changes. A warm
check cache replays these, so day-to-day checks don't pay.

## 2. Where it goes [measured]

**By instance.** A scratch probe around each `derive_data_*` call
(patch kept out of the tree) for the Nat program: `Ord` 6.17M steps
(0.38 to 0.43 s), `DecEq` 2.90M (0.18 to 0.20 s), `Show` 37K, `Finite` 39K.
Text and Map split the same way. So derived `<` is two thirds and `==` a
third; printing and `Finite` are free.

**By type.** Diffing the per-declaration tables before and after: for
Nat, 12 types account for 9.0M of the 9.5M extra steps, all of them the
reflected syntax of the `arithmetic` (omega) and `ring` decision
procedures, which every importer loads because std's proofs use those
tactics:

| Type | Extra steps |
|---|---|
| `Std.Omega.Fact` | 4.22M |
| `Std.Omega.Goal` | 1.23M |
| `Std.Omega.Cert` | 0.76M |
| `Std.Omega.ITerm` | 0.76M |
| `Std.Ring.ZExpr` | 0.55M |
| `Std.Omega.NTerm` | 0.50M |
| `Std.Omega.Step` | 0.36M |
| `Std.Ring.NExpr` | 0.34M |
| `Std.Omega.Row`, `Omega.Env`, `Ring.Env`, `Ring.Mono` | 0.39M |

Map adds `Std.Map.Tree` (2.0M) and `Std.Map.Tree.Shape` (50K): Map's
internal balanced tree, whose structural `==` isn't map equality anyway.

**By definition.** Within a type, the costly definitions are the proofs:
for `Omega.Fact`, `%equal` (the `Ord` law `compare r s = Equal → r = s`)
2.32M, `%sameSound`/`%sameComplete` 1.02M, `%trans` 0.58M, `%flip` 0.17M;
the test functions (`%same`, `%compare`, `%show`) are a few thousand each.

**By constructor.** A synthetic `type T = | C1 (a: Nat) (b: Nat) | …` with
4, 8, 16 and 32 constructors costs steps exactly linear in the count
(SW-3370's rebuild holds): per constructor about 52K for `%sameSound`,
49K for `%equal`, 26K for `%trans`, 9K for `%flip`. Fields of a type with
a derived instance cost about three times that (`Fact`'s `%equal`: 154K
per constructor, against `ITerm`'s 34K).

**In the elaborator.** samply on that synthetic type with 120
constructors: elaborating the generated source is about 80% of the time,
the kernel's check of the result 19%. Inside elaboration the time is
spread, not one hotspot: `infer_j` (the `J`s of the rebuild) 37%
inclusive, instance unification (`unifies_with_instances`) 27%, zonking
9%, and the allocator 27% of self time.

## 3. Options

**A. Derive std types' instances on first use (keeps D3609).** At a
std type's declaration, record its plan (cheap: whether it can be derived,
or why not, which `no_eq`/`no_ord`/`no_show` already keep); generate and
check the instances only when instance search first asks for `DecEq`,
`Ord`, `Show` or `Finite` of that type. Every importer pays only for the
std types it compares or prints. Expected: back to the before column,
Nat 20.7M → about 11.2M steps, 1.8 → 1.1 s [inferred: the tiny programs
use no std type's derived instance, and the before build is that
behaviour]. Program types stay eager: their namespace usually uses them,
and a check cache entry covers the rest. Design questions, which is why
this isn't built here:

- Derivation then runs in the middle of another definition's elaboration
  (`derive.rs`'s doc gives exactly this as the reason it is eager; it calls
  `clear_metas`). It needs the suspended-context path a library file
  already uses when it loads mid-declaration.
- The check cache keys and stores derived declarations with their library
  file; lazily derived ones need entries of their own, keyed by the type.
- `hash_stability::prelude` and the `derived-std-instances` snapshot record
  derived declarations; they'd record only those used.
- A derivation that fails late (a refusal) must give the same note as
  today.

Estimate: one Opus lane, about 2 h agent time, plus a short design pass
first.

**B. Don't derive for std's internal types (changes what's derived).** An
attribute (std-only, or a general `@[noDerive]`) on the twelve `Omega` and
`Ring` reflection types, and `Map.Tree`, `Map.Tree.Shape`. Measured with
the probe skipping `Omega.*` and `Ring.*`:

| Program | Steps after | Steps, B | Seconds after | Seconds, B |
|---|---|---|---|---|
| Nat | 20.7M | 11.6M | 1.77 | 1.23 |
| Int | 27.1M | 18.0M | 2.40 | 1.79 |
| Text | 18.9M | 10.8M | 1.66 | 1.36 |
| Map | 45.0M | 35.9M | 3.90 | 3.08 |

(Map.Tree would take Map's about 2M lower.) Small to build (Sonnet, under
an hour), but it is an exception to D3609, and a general `@[noDerive]`
would be new user-visible syntax; it also helps only these types, not the
next std type with many constructors.

**C. Make the generated proofs cheaper to elaborate (keeps everything).**
The profile has no single hotspot (§2), so the gain is unknown without a
further profile of `infer_j` and instance unification on generated
source. Generating core terms directly instead of source would skip the
80% spent elaborating (the kernel would still check them, so trust is
unchanged) but is a rewrite of about 6,000 lines of derivers. Worth a
profiling ticket; it helps every program's own types too.

**D. Ship std's check cache with the CLI and the playground bundle.**
Covers every cold-start cost, not only this one (check-cache.md lists
shipped entries as a possible follow-up for the playground). A separate
design.

## 4. Recommendation

A, for std types only: it keeps D3609 as decided (every type gets its
instances) and removes nearly all of the measured cost, which falls on
types no program compares. B is the stopgap if A waits. C as a profiling
ticket; D on its own merits.

**Decision for Matt** (number to be assigned): derive std types' `==`,
`<`, printing and `Finite` on first use instead of when std loads?
[rec: yes]
