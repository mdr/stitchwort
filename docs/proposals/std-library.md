# Splitting the prelude into a standard library (SW-148), draft 1

**Date:** 20 October 2026. **Ticket:** SW-148 (related: SW-145, SW-146; supersedes D48).
**Decisions already made by Matt:** D49, D50, D55, D56 (§2). **Open:** D57 (deferred), D58 to D62 (§10).
**Status:** draft for external review. Nothing is implemented.

Claims about the code are marked **[checked]** when I ran or read the thing named, and
**[unmeasured]** or **[estimate]** when they aren't. Line numbers are for `main` at `65e6e4e`.

## Contents

0. [The short version](#0-the-short-version)
1. [Background: the prelude today](#1-background-the-prelude-today)
2. [What Matt has decided](#2-what-matt-has-decided)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [The design](#4-the-design)
5. [What stays and what moves](#5-what-stays-and-what-moves)
6. [Effects on the rest of the system](#6-effects-on-the-rest-of-the-system)
7. [Staging](#7-staging)
8. [Risks](#8-risks)
9. [Questions for the reviewer](#9-questions-for-the-reviewer)
10. [Decisions](#10-decisions)
11. [Sources](#sources)

## 0. The short version

- **Today** every program checks the whole prelude, a single 3,226-line Stitchwort file
  (`crates/elab/src/prelude.sw`): 245 definitions, 369 theorems and 21 types **[checked]**.
  Checking an empty file takes about 0.21 s **[checked: `stitchwort check` on a one-line file,
  0.215 s wall]**, almost all of it the prelude. The prelude roughly doubled during October's
  AoC work, and it will keep growing as proofs need lemmas.
- **Proposal.** Only a small **core** stays always loaded: what built-in syntax, `deriving`,
  `calc`, `auto` and abilities need. Everything else becomes **library files** under `Std`,
  each checked only when a program uses something in it.
- **No user-visible change in meaning.** Full names don't change (`Std.Nat.modAddMod` stays
  `Std.Nat.modAddMod`), and imports keep their meaning: they only decide which names can be
  written without a prefix (D50).
- **One rule does change (D50, D55).** Today any namespace directly under `Std` can be used
  as a prefix in any file (namespaces.md §4.6, "Qualifiers are always available"). That
  special rule goes. A namespace whose name isn't a default name (`Eq`, `Effect`, `Builtin`)
  is reached by `Std.Eq.sym` or after `import Std (Eq)`.
- **Natives** (functions with a Rust fast path, such as `Text.split`) move with their
  namespace. Their fast path is attached when their file loads (D56).
- **Staging:** first the loading machinery, with one file moved as a test; then the import
  change; then the rest of the move, section by section, measuring as it goes.

## 1. Background: the prelude today

### 1.1 One file, loaded before everything

- `crates/elab/src/lib.rs:53`: `pub const PRELUDE: &str = include_str!("prelude.sw");`
  **[checked]**.
- `crates/driver/src/driver.rs:54-86`: every `Session` loads it as a file named `<prelude>`
  with `loading_prelude = true`, then calls `finish_prelude` **[checked]**.
- `finish_prelude` (`crates/elab/src/lib.rs:376`) checks that every built-in in the registry
  has been bound: `registry::check_complete` **[checked]**.
- The playground and the JavaScript backend get the prelude the same way, through the `elab`
  crate.
- The test cache's build fingerprint hashes `crates/elab/src`, so a prelude edit invalidates
  cached test results (`crates/driver/build.rs:16`) **[checked]**.

### 1.2 What's in it

The file has section comments **[checked]**:

| Lines | Section | What's there |
|---|---|---|
| 1–52 | Logic | `Void`, `Unit`, `Not`, `And`, `Or` and lemmas |
| 53–110 | Numbers, Booleans | `Nat`, `Bool`, `add`, `sub`, … |
| 111–197 | Lists | `List`, `Maybe`, `Pair`, basic functions |
| 198–326 | Decisions | `Decidable`, `Nat.decEq`, `toBool`, `elim`, … |
| 327–358 | Characters | `Char`, `Char.decEq` |
| 359–870 | Division | `div`, `mod` and many lemmas (`Nat.leTrans` is at 434) |
| 871–1394 | Comparisons | `Ordering`, `compare`, `max`/`min` lemmas |
| 1395–2077 | Sorting | 122 definitions and theorems, including sorting proofs |
| 2078–2617 | Numbers as text | `Text` (2001), `Int` (2139), digits, `toText`/`toNat` |
| 2618–2685 | Splitting and joining | `Text.split`, `Text.join` |
| 2686–2726 | Lines | `Text.lines` |
| 2727–~2900 | Effect machinery | `Effect.Comp`, `bind`, handlers' plumbing |
| 3192–3226 | IO | `ability IO`, `IO.simulate`, `IO.readAllLines` |

### 1.3 How the compiler depends on it

- **The registry.** `crates/core/src/registry.rs:70` lists about 150 *built-ins*: prelude
  declarations the compiler refers to by identity **[checked]**. They fall into two groups.
  - **Built-ins used by syntax and by the checker.** `+` is `Nat.add`. `<` and `<=` are
    `Nat.LessThan` and `Nat.LessEq`. `==` uses `Decidable.toBool`. `if` uses
    `Bool.ifThenElse` and `Decidable.elim`. `++` uses `List.append` and `Text.append`.
    Literals use `MkChar`, `MkText`, `Nil` and `Cons`. `()` is `Builtin.UnitType`. `calc`
    uses `Eq.sym`, `Eq.trans`, `Nat.leTrans` and `Nat.lessTrans`. Abilities use about 30
    `Effect.*` declarations. The elaborator names about 90 distinct `Builtin::` variants
    **[checked: grep of `crates/elab/src`]**.
  - **Natives.** These have a Rust implementation used when the arguments are known values
    (`crates/core/src/native.rs`, header comment) **[checked]**. Examples are `Text.split`,
    `Int.abs` and `Nat.toText`. A native must compute exactly what its Stitchwort definition
    computes, and tests compare the two.
- **By name.** `deriving` writes `Std.Eq.cong`, `Std.Nat.equal` and `Std.Nat.equalFalse` as
  names (`crates/elab/src/derive.rs:521,567,584`), and records write `Std.Eq.cong`
  (`records.rs:233`). The alias `not` is `Bool.not` (`scope.rs:35`) **[checked]**.
- **`auto`** searches every checked definition whose result is `Decidable …`. This includes
  every one in `Std`, whether or not it's imported (namespaces.md §7.1; multi-file.md §4.9.5,
  "`Std`: Yes") **[checked: the design text]**. About 20 such procedures are spread across
  the prelude, from `Nat.decEq` (line 244) to `Int.decLessThan` (2250) **[checked: grep]**.

### 1.4 The default set as built

namespaces.md §4.6 says the default set is "exactly what `Std` declares at its root". Its
table lists 13 types and abilities. The prelude also declares `And`, `Or` and `Int` at the
root (lines 25, 29, 2139), so those are default names too **[checked]**. The §4.6 table is
out of date and should gain them. The namespaces that are **not** default names are `Eq` (it
has no type of its own, since `=` is built in), `Effect` and `Builtin`.

### 1.5 Problems this causes

1. **Cost.** Every program pays for every lemma. That was D48: about 0.13 s rising to about
   0.21 s for an empty file, with the examples benchmark's step counts up about 50%.
2. **Tests leak.** Prelude tests run in every project's `stitchwort test` and change its totals
   (SW-146).
3. **Slow prelude iteration.** A prelude edit means rebuilding the CLI (SW-145).
4. **One undivided space.** There's no structure beyond section comments.

## 2. What Matt has decided

| ID | Decision |
|---|---|
| D49 | Split the prelude. As a first step, everything that built-in syntax doesn't need moves into `Std` library files, checked only when used. What happens to the remaining core (for example renaming it `std/Core.sw`, D57) is decided later. |
| D50 | Imports keep exactly today's meaning: they decide which names can be written unqualified, nothing else. Drop the special rule that makes every `Std` namespace usable as a prefix without an import. `Std.X.y` always works, and `import Std (X)` makes `X.y` work. |
| D55 | No additions to the default set. `Eq`, `Effect` and `Builtin` need `import Std (…)` or the `Std.` prefix. Matt's reasoning: needing an import isn't a real cost, since agents and error hints add them easily. |
| D56 | Natives move with their namespace. Their Rust implementation is attached when the file that defines them loads. |
| D48 | Superseded by D49. Caching checked modules can come later, per module. |

## 3. How other languages do it

| Language | Always loaded | Everything else | Proofs vs programs |
|---|---|---|---|
| **Idris 2** | `Prelude`, "loaded implicitly unless you use the `--no-prelude` option" [I1] | `base` etc., "imported as required" [I2] | The Prelude's header says "proofs of Nat/List properties that almost never get used in practice would probably be better in base libraries" [I2] |
| **Agda** | Nothing: every module is imported explicitly [A1] | `Data.Nat.Base`, `Data.Nat.Properties`, … | Separate modules: `Base` holds definitions and `Properties` holds lemmas. `Data.Nat` re-exports `Base` and only a few decision procedures from `Properties` [A2] |
| **Rocq (Coq)** | `Init`, "automatically loaded when starting" [C1] | `Require Import Arith` and so on [C1] | Arithmetic lemmas live in `Arith`, outside `Init` |
| **Lean 4** | `Init`, imported automatically [L1] | Explicit `import` of compiled `.olean` files [L1] | `Init` *does* contain many lemmas (`Init/Data/Nat/Lemmas.lean`) [L2]. Lean pays little for this, because imports load already-checked `.olean` files rather than re-checking source |
| **Rust** | The `std` prelude (short names) and the *extern prelude* (crate names such as `std` and `core`) [R1] | `std::collections::HashMap` works anywhere; `use std::collections::HashMap` gives the short name | (n/a) |
| **Elm** | Fixed default imports: `import List exposing (List, (::))`, `import Maybe exposing (Maybe(..))`, … [E1] | Explicit imports | (n/a) |

What this means for us:

- **Small core plus libraries loaded on demand** is what Idris, Rocq and Lean do. Idris's
  header comment states our D49 almost word for word.
- **Separating lemmas from definitions** follows Agda's `Base`/`Properties` split and Rocq's
  `Arith`. We get the same speed benefit without renaming, by splitting the *files* while
  keeping the *names* (§4.2). Agda users effectively do the same by hand: the style guide
  says to import both `Data.List.Base` and `Data.List.Properties` qualified as `List` [A2],
  so lemmas and functions read `List.…` whichever module they're in.
- **Lean is the counterexample.** It keeps lemmas in its always-loaded `Init` because it never
  re-checks them. Stitchwort re-checks every run (multi-file.md §8.3). So Lean's arrangement
  only becomes attractive here once we have a cache of checked modules, the deferred part of
  D48.
- **D50's import rule is Rust's.** `std::…` is always reachable by its full path, and `use`
  only shortens names. Our `Std` plays the part of Rust's extern prelude. Elm instead puts
  `List` and the rest in by default; we already do that for the default types, and D55 keeps
  the list as it is.

## 4. The design

### 4.1 Layout

```
crates/elab/src/std/
  core.sw            -- always loaded: today's prelude minus what moves (D49)
  Nat/Division.sw    -- namespace Std.Nat: div/mod lemmas
  Nat/Compare.sw     -- namespace Std.Nat: max/min, ordering lemmas
  List/Sort.sw       -- namespace Std.List: sorting and its proofs
  Text/Digits.sw     -- namespace Std.Text / Std.Nat: toText, toNat, digits
  …
```

- Everything is still embedded in the binary with `include_str!`, through one generated
  table of `(path, text)` pairs. The playground and JS backend get the same table.
- Because the folder sits under `crates/elab/src`, the test-cache fingerprint
  (`driver/build.rs`) covers it unchanged.
- Each library file starts with a namespace line such as `namespace Std.Nat`, as project
  files do (multi-file.md §4.2). Several files may add to one namespace, and core may already
  declare into it. User files still can't add to `Std` (namespaces.md §4.4); library files
  can.
- **Names don't change.** `Nat.modAddMod` is `Std.Nat.modAddMod` wherever its file is.

### 4.2 The unit of loading is a file, not a namespace

In project code the unit of checking is a namespace: all of a namespace's files are checked
together, and cycles *between* namespaces are refused (multi-file.md §4.6). The library needs a
finer unit:

- `Std.Nat` will be spread over core plus several library files. If using `Nat.toText` loaded
  every `Std.Nat` file, it would also check all the division lemmas, and most of the saving
  would be lost.
- So **library files are loaded one at a time**, each after the files it uses.
- **Library files must not form a cycle** between them. A library test checks this, and the
  library's authors fix it by moving declarations. Within one file, anything goes, as today.
- **Dependencies are found the way projects find them.** The pre-pass that finds a
  namespace's edges (`project.rs:132`, `namespace_edges`, built on `decl_refs`) works at the
  level of files for `Std`. The edges are exact, not merely safe, as multi-file.md §4.6
  requires.

### 4.3 The name index and what triggers a load

- **The index.** At start-up, every library file is *parsed*, not checked. This builds an
  index from full name to file (`Std.Nat.modAddMod` → `Nat/Division.sw`). Parsing ~2,500
  lines should be cheap compared with checking them **[unmeasured; measured in stage 1; if not
  cheap, the index is built at compile time by `build.rs`]**.
- **What triggers a load.** Before a user namespace (or single file) is checked, the pre-pass
  collects every reference that resolves into `Std`, by any route:
  - `List.sort`, where `List` is a default name;
  - `Std.List.sort`;
  - `import Std.List (sort)` followed by `sort`;
  - dot notation, `xs.sort`. Its namespace comes from the type of `xs`, which the pre-pass
    can't know, so dot notation looks the name up in the index and loads it during checking
    (§4.5).

  The files those references name, and their dependencies, are loaded in a **canonical
  order** first: dependency order, with ties broken by path. The order never depends on the
  order in which the program mentions things.
- **Errors.** "Unknown name" and its near-miss suggestions search the index as well as what's
  loaded. So `List.sortt` still suggests `List.sort` even when the sorting file isn't loaded.

### 4.4 Imports (D50, D55)

- **Removed:** the paragraph "Qualifiers are always available" in namespaces.md §4.6.
- **Kept:** `Std` is reserved and always means the library. Default names (§1.4, including
  `And`, `Or` and `Int`) remain default, so `List.map` and `Int.abs` keep working without an
  import.
- **New:** `import Std (Eq)` must work for a namespace that isn't a type. Today it's an error:
  `E-IMPORT-UNKNOWN: Std has no Eq` (and the same for `Effect`) **[checked]**. §4.5's rule "an
  item may be a sub-namespace that is a type" widens to any sub-namespace.
- **New hint.** `Eq.sym` with no import gives an error with the fix: "`Eq` is `Std.Eq`; add
  `import Std (Eq)`, or write `Std.Eq.sym`".
- **Who's affected:** 14 `.sw` files outside the prelude use `Eq.` (5 in `aoc/src`, 8 in
  `examples/accept`, 1 in `examples/extract`), and 2 use `Effect.` **[checked: grep]**. Rust
  tests that embed programs need the same edit. It's mechanical.
- **Unaffected: dot notation.** `p.sym` finds `Eq.sym` through the type of `p`
  (namespaces.md §4.8), not through a name in scope.

### 4.5 Dot notation and `auto`

- **Dot notation.** For `e.f` with `e : D …`, step 2 of namespaces.md §4.8 looks for `D.f`.
  It now looks in the index, not only among loaded declarations. A hit loads that file and its
  dependencies, then checking continues. This is the only load that happens *during*
  checking. It's deterministic: the same program loads the same files in the same order.
- **`auto` (D58, proposed).** **Every `Decidable` procedure in `Std` stays in core.** The
  alternative is that `auto` sees only what happens to be loaded. Then whether
  `if x == y` checks could depend on whether the file also mentions, say, `List.sort`, which
  would be bizarre. There are about 20 procedures (§1.3), plus the lemmas their definitions
  need. A library test enforces it: no library file may declare a definition whose result
  type's head is `Decidable`.
  - *Later, compatible:* proper instance declarations (multi-file.md §4.9.6) could lift this,
    with an index of instances by the type they decide.

### 4.6 Natives (D56)

- **The registry gains a column** saying whether each built-in is **core** (syntax, the
  checker, `deriving`, `calc` or abilities need it) or **library** (a native whose definition
  lives in a library file).
- **`finish_prelude` → `finish_core`.** It checks only the core built-ins, as
  `check_complete` does today.
- **When a library file loads,** its natives are bound exactly as today: the same
  shape checks (`register_native`) and the same content-hash checks for text natives and the JS
  generator (namespaces.md §7.3). Nothing about those checks is weakened; they run at a
  different moment.
- **A library test loads every library file** and runs `check_complete` over the whole
  registry. A native whose definition went missing is still caught, in CI rather than at
  start-up.

### 4.7 Tests in library files

- Library files keep their `test`s next to their definitions (house style).
- Those tests run under a library test target (a `dev/t std` area, plus the gate), **never**
  in a project's `stitchwort test`. That fixes SW-146.
- Core's tests run the same way.

### 4.8 Hashes and caching

- Full names are unchanged and bodies move verbatim, so content hashes shouldn't change.
  Hash stability isn't a goal anyway; hashes are a migration oracle. **Stage 3 compares every
  moved declaration's hash before and after.**
- The test cache keeps working. Its key includes the build fingerprint, which covers the
  library files.
- **Caching checked library files** (the rest of D48) becomes natural once files are units.
  It's out of scope here.

## 5. What stays and what moves

A first cut, from the sections in §1.2. Stage 1's dependency tool (§7) gives the real answer.

| Stays in core | Why |
|---|---|
| Logic (`Void`, `Unit`, `Not`, `And`, `Or`) | Default names; `!=` is `Not` |
| `Nat` with `add`, `sub`, `mul`, `div`, `mod`, `leq`, `LessThan`, `LessEq`, `equal…`, `decEq` | Operators, natives the kernel relies on, `deriving` |
| `Nat.leTrans`, `Nat.lessTrans` and the lemmas they need | `calc` |
| `Bool`, `ifThenElse`, `not`, `uniqueEq` | `if`, the `not` alias |
| `List`, `Nil`, `Cons`, `append`; `Maybe`, `Pair` with `fst`/`snd` | Literals, `++`, built-ins |
| `Decidable` and every `Decidable` procedure | `==`, `if h :`, `auto` (D58) |
| `Char`, `Text`, `MkText`, `Text.append` | Literals, `++`, string interpolation |
| `Int` and its constructors | Built-in |
| `Eq.sym`, `Eq.trans`, `Eq.cong` | `calc`, `deriving`, records |
| The effect machinery (lines 2727–~2900) | Abilities and handlers compile to it |
| `ability IO` and `IO.simulate` | Built-in; a default name |

| Moves (examples) | To |
|---|---|
| Division lemmas (`Nat.modAddMod`, `Nat.divMul…`, …) | `Nat/Division.sw` |
| `compare`, `max`, `min` and their lemmas | `Nat/Compare.sw` |
| Sorting and its proofs | `List/Sort.sw` |
| `List.transpose`, `padRight`, `splitBy`, `keepIf`, … | `List/…` |
| Digits, `Nat.toText`, `Text.toNat`, `Int.toText` (natives) | `Text/Digits.sw`, `Int/…` |
| `Text.split`, `join`, `lines`, `trim` (natives) | `Text/…` |
| The `Int` arithmetic natives and lemmas not needed by core | `Int/…` |

**Estimated size of core: about 700 of 3,226 lines** **[estimate: added up from the line
ranges above; not measured]**. Two things make it uncertain. Some core declarations' proofs
reach into later sections, and the `Decidable` procedures (D58) need some list and text
lemmas. Stage 1 measures it.

## 6. Effects on the rest of the system

- **CLI.** No new commands. `check`, `run`, `test` and `build` load what's used.
- **Playground.** It embeds the same table, and nothing else changes. Playground projects
  (SW-133) aren't affected.
- **JS backend.** Exports and boundary codecs use built-ins by identity, as today. Text
  natives are bound when their file loads (§4.6).
- **REPL and `eval`.** These check each new input like a file: an input that names
  `List.sort` loads the sorting file from then on.
- **Error messages.** These print full names as today. A name from an unloaded file shows
  normally once loaded; the index makes suggestions work before then.
- **SW-145** (faster prelude iteration). Out of scope, but splitting makes a later "load
  `std/` from disk in debug builds" switch easy.
- **namespaces.md.** §4.6 loses "Qualifiers are always available" and its table gains `And`,
  `Or` and `Int`. §4.5 widens import items to any sub-namespace. §7.1's "`auto` searches
  every checked definition" stays true, because they're all in core (D58).

## 7. Staging

1. **Mechanism, with one file moved.**
   - The `std/` table and the name index.
   - File-level dependencies for `Std`, with the no-cycle test.
   - Loading triggered by the pre-pass and by dot notation.
   - Natives bound on load (the registry column, `finish_core`), and the whole-library
     `check_complete` test.
   - The library test target (SW-146).
   - Move **Sorting** (lines 1395–2077: self-contained, no natives, not used by syntax), as
     the proof that the mechanism works.
   - **Measure:** an empty file, `aoc` check, examples benchmark, and parse time for the
     index.
   - A small tool lists, for each prelude declaration, the core declarations it needs. This
     settles §5's split.
2. **Imports (D50, D55).** Drop the prefix rule, allow `import Std (Eq)`, add the hint,
   update the 16 files and the Rust test programs (mechanical: DeepSeek, from an exact list),
   and update namespaces.md §4.5 and §4.6.
3. **Move the rest,** one section per commit, comparing hashes before and after (§4.8), and
   gating each one. Measure again at the end.
4. **Later, separately:** what's left in core (D57), caching checked files (rest of D48), and
   SW-145.

## 8. Risks

- **The core may not shrink as much as hoped,** if core declarations' proofs depend on many
  lemmas from later sections. *Mitigation:* the stage 1 tool measures this before stage 3. A
  lemma core needs can stay in core, and `Decidable` procedures with heavy proofs can have
  them restated more simply.
- **Hidden string lookups.** Any place the compiler names a prelude declaration by a string
  rather than through the registry breaks if that declaration moves. The ones found are
  `derive.rs` and `records.rs` (`Std.Eq.cong`, `Std.Nat.equal`, `Std.Nat.equalFalse`) and
  `scope.rs:35` (`not`), all of which stay in core **[checked: grep for quoted `"Std.` and
  `"Bool.` in `crates/elab/src`]**. *Mitigation:* stage 1 adds a test that loads core alone
  and runs every compiler path that names a declaration (`deriving`, records, `calc`,
  `auto`, abilities).
- **Load-dependent behaviour.** Apart from `auto` (handled by D58), could anything mean
  something different depending on which library files are loaded? Nothing found so far.
  Instance-like search is the usual culprit, and `auto` is our only one. **Reviewer: please
  look for others.**
- **Performance of loading on demand.** Typical AoC programs use `List`, `Text` and `Nat`
  heavily, so they may load most of the library and see little saving until checked files
  are cached. Small programs and the playground benefit most. **[unmeasured]**

## 9. Questions for the reviewer

1. Is the file-level loading unit (§4.2) sound, given that project namespaces are checked as
   a whole? Is there a simpler unit that keeps most of the saving?
2. D58, keeping every `Decidable` procedure in core, is the simplest fix for `auto`. Is
   there a better rule that keeps `auto`'s result independent of what's loaded?
3. Are there other places where loading on demand could change meaning, such as dot
   notation's unfolding loop or error recovery?
4. Is parsing the whole library at start-up for the index the right trade-off, against an
   index built at compile time?
5. Anything missing from the precedents in §3 that would change the design? In particular,
   how Lean, Agda and Idris handle the "you used a name from a module you didn't import"
   error.

## 10. Decisions

| ID | Question | Recommendation |
|---|---|---|
| D57 | Rename what's left of the prelude to `std/core.sw`, and drop the word "prelude"? | Deferred by Matt until after the first step |
| D58 | Keep every `Decidable` procedure in core, so `auto` never depends on what's loaded (§4.5)? | Yes |
| D59 | Load the library a file at a time, with no cycles between library files (§4.2)? | Yes |
| D60 | Build the name index by parsing at start-up, falling back to `build.rs` if slow (§4.3)? | Yes |
| D61 | Run library tests only under a library target, never in projects (§4.7, SW-146)? | Yes |
| D62 | Stage as in §7, moving Sorting first as the test case? | Yes |

## Sources

- [I1] Idris 2 documentation, "Type-Driven Development with Idris" porting notes: the prelude
  is "always implicitly loaded unless you use the --no-prelude command-line option".
  https://idris2.readthedocs.io/en/latest/typedd/typedd.html
- [I2] Idris 2 `Prelude` source, module header. https://www.idris-lang.org/Idris2/prelude/source/Prelude.html
- [A1] Agda standard library README. https://agda.github.io/agda-stdlib/master/README.html
- [A2] Agda standard library, `Data.Nat` (re-exports `Data.Nat.Base` and selected
  `Data.Nat.Properties`). https://www.cse.chalmers.se/~abela/notes/html/Data.Nat.html; style
  guide (`doc/style-guide.md`): `Base` is "for basic operations", `Properties` "for lemmas about
  them", and both are conventionally imported under the datatype's name (`Data.List.Properties`
  as `List`). https://github.com/agda/agda-stdlib/blob/master/doc/style-guide.md
- [C1] The Coq/Rocq Standard Library index ("Init: the core library, automatically loaded when
  starting Coq"). https://docs.rocq-prover.org/v8.20/stdlib/
- [L1] Theorem Proving in Lean 4, "Interacting with Lean" (Init imported automatically; imports
  resolve to `.olean` files). https://docs.lean-lang.org/theorem_proving_in_lean4/interacting_with_lean.html
- [L2] Lean 4 source tree, `src/Init/Data/Nat/` (contains `Lemmas.lean`, `Basic.lean`, …).
  https://github.com/leanprover/lean4/tree/master/src/Init/Data/Nat
- [R1] The Rust Reference, "Preludes" (extern prelude: `core` always, `std` unless `no_std`).
  https://doc.rust-lang.org/reference/names/preludes.html
- [E1] elm/core README, default imports. https://github.com/elm/core/blob/master/README.md
