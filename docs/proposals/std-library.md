# Splitting the prelude into a standard library (SW-148), draft 2

**Date:** 20 October 2026. **Ticket:** SW-148 (related: SW-145, SW-146; supersedes D48).
**Decisions already made by Matt:** D49, D50, D55, D56 (§2). **Open:** none; D57 was accepted after the review and done in stage 1.
**Status:** reviewed once externally ("proceed, but tighten the loader invariants before
implementing stage 1"; no soundness issue found). Nothing is implemented.

## Changes since draft 1

Draft 1 had one external review, with four major findings and three minor. Its verdicts were:
D57 defer; D58, D59 and D60 agree with changes; D61 and D62 agree. It had no objection to
D49, D50, D55 or D56. Every finding is addressed:

1. **A governing invariant** (§4.0, new). Lazy loading is an implementation detail. Apart
   from D50's intended import change, a program resolves and elaborates exactly as if all of
   `Std` were checked. Stage 1 gets an eager-versus-lazy comparison mode to enforce it
   (§7).
2. **File dependencies are more than namespace edges** (major; §4.2).
   - A reference inside one namespace can still be an edge between two files, so every
     reference resolves to its owning file.
   - Dot notation can add edges during checking. The loader tracks *not loaded / loading /
     loaded* and reports a cycle on any load request, static or dynamic.
3. **The index is part of name resolution** (major; §4.3).
   - Resolution always consults the complete index, never "what's loaded so far".
   - Suggestions never load anything.
4. **The index must be complete and unique** (major; §4.3).
   - It is built by a declaration-collection phase that includes generated names
     (constructors, record fields, ability operations, aliases).
   - It rejects any full name declared twice across core and library, even in files no
     program loads.
   - It keeps a namespace tree, so `import Std (Eq)` needs no load.
5. **D58 is the stage 1 rule, not the ideal** (major; §4.5). The later rule is a global,
   canonically ordered index of `Decidable` candidates that `auto` searches whatever is
   loaded. A chosen candidate's file is loaded before use.
6. **§3 corrected** (minor). Lean, Agda and Idris need an import before even a fully
   qualified name from another module works. Stitchwort deliberately differs: references,
   not imports, establish dependencies on `Std`. Rust's `std` is the closest precedent.
7. **The index is built once per process** and keeps the parsed syntax for loading (minor;
   §4.3, D60). Stage 1 measures its time and memory.
8. **"Default name" isn't a reason to be in core** (minor; §5). A default name can point
   into a library file. Keeping `And` and `Or` in core is just simpler for now.

The reviewer's answers to §9's questions are summarised in [§9](#9-review-answers).

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
9. [Review answers](#9-review-answers)
10. [Decisions](#10-decisions)
11. [Sources](#sources)

## 0. The short version

> **Since SW-213 (D260, D266):** what a program can *name* without an import is narrower
> than what it can *use*: a library namespace's functions and lemmas need
> `import Std (List)` and so on, and `Map`, `Set`, `Vec`, `Fin` need an import even for
> the type ([prelude-slim.md](prelude-slim.md)). Loading is unchanged: what's loaded never
> changes what a program means.

- **Today** every program checks the whole prelude, a single 3,226-line Stitchwort file
  (`crates/elab/src/prelude.sw`): 245 definitions, 369 theorems and 21 types **[checked]**.
  Checking an empty file takes about 0.21 s **[checked: `stitchwort check` on a one-line file,
  0.215 s wall]**, almost all of it the prelude. The prelude roughly doubled during October's
  AoC work, and it will keep growing as proofs need lemmas.
- **Proposal.** Only a small **core** stays always loaded: what built-in syntax, `deriving`,
  `calc`, `auto` and abilities need. Everything else becomes **library files** under `Std`,
  each checked only when a program uses something in it.
- **The rule everything else follows (§4.0).** Lazy loading is an implementation detail.
  Apart from D50's import change, a program must resolve and elaborate exactly as if the
  whole standard library had already been checked.
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

- **A small, automatically available core plus separately loaded modules** is common. Idris,
  Rocq and Lean all do it, and Idris's header comment states our D49 almost word for word.
- **But Stitchwort differs on how a module gets loaded.** In Lean, Agda and Idris, even a
  fully qualified name from another module works only after that module is imported. Lean's
  `import` adds a module's contents, while namespaces and `open` are a separate mechanism.
  Agda needs `import M` before `M.x` works, and `open` gives the short forms [A1]. Idris
  files list their imports. In Stitchwort, **references, not imports, establish a dependency
  on `Std`**: writing `Std.List.sort` is enough to load it. Rust's treatment of `std` is the
  closest precedent [R1]. Users coming from Lean or Agda should be told this explicitly.
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

### 4.0 The invariant

> **Lazy loading is an implementation detail.** Apart from the intended import change of
> D50, a program must resolve and elaborate exactly as if the entire standard library had
> already been checked.

- What's loaded may decide whether a declaration's *body* has been checked yet. It must never
  decide whether that declaration *takes part in resolution*.
  - Name lookup, ambiguity, import validation, dot notation and `auto` all see the whole
    library, through the index (§4.3).
- **Enforced by a test mode.** A test-only "eager `Std`" mode loads every library file first.
  Stage 1 runs `aoc`, the examples and the library's own tests in both modes and compares
  them. The two modes must agree on:
  - which programs are accepted and which rejected;
  - which declaration each name resolves to;
  - declaration hashes.

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
  If two files ever genuinely need mutual recursion, they become one file. Generalising the
  unit to a cycle of files can come later.
- **Ordinary references give exact file edges, by resolving each one to its owning file.**
  This is *not* `namespace_edges` (`project.rs:132`) with a different key. Within one
  namespace, a reference is internal to the namespace but can still connect two files:

  ```
  -- Nat/A.sw, namespace Std.Nat
  def a := … b …         -- unqualified, same namespace
  -- Nat/B.sw, namespace Std.Nat
  def b := …
  ```

  Here `A.sw → B.sw` is an edge. So the analysis resolves every reference, qualified or not,
  through the index to the file that owns it. It reuses `decl_refs` to collect references.
- **Type-directed references add edges during checking.** A library file can contain
  `xs.sort`, whose target the pre-pass can't know. The loader keeps a state for each file:
  *not loaded*, *loading* or *loaded*. A load request for a file that is *loading* is a
  cycle. It's reported as an internal library error naming both files, never a hang and
  never a silent skip. Static and dynamic requests use the same check.
  - The load-every-file test (§4.6) loads in an order that exercises these dynamic edges
    too.
  - A stricter rule would forbid dot calls across library files. The reviewer preferred the
    robust loader, and so do I.

### 4.3 The name index and what triggers a load

- **The index is part of name resolution, not just a loading shortcut.** Every lookup
  (short names, qualified names, `import` items, dot notation, default names and
  near-miss suggestions) consults the full index. It never consults "what's loaded" first and
  the index only on failure. For example, `import Std.A (foo)` with `import Std.B (foo)`
  followed by `foo` is ambiguous whether or not `A` happens to be loaded.
- **What the index holds.** It maps each full name to its owning file
  (`Std.Nat.modAddMod` → `Nat/Division.sw`), and it keeps a **namespace tree**. So
  `import Std (Eq)` can introduce the prefix `Eq` without loading every file that adds to
  `Std.Eq`.
- **It's built by a declaration-collection phase, not a scan of top-level names.** Every
  name a user can write must be in it, including generated ones: constructors (`Std.List.Cons`
  and their short forms), record fields (`Std.X.R.field`), ability operations (`IO.print`),
  and aliases (`not`). Stage 1 lists each declaration form and the names it generates, and a
  test checks the index against an eager load.
- **Global uniqueness.** Building the index rejects any full name declared twice, whether
  library vs library, core vs library, or a generated name vs either. This happens before any
  user code is checked, even if neither file would otherwise be loaded, so lazy loading can't
  hide a malformed library.
- **Once per process.** The index is immutable, process-level data shared by every
  `Session`. The parsed syntax of each file is kept and reused when that file loads, so
  parsing happens once.
- **Cost.** Parsing ~2,500 lines should be cheap compared with checking them **[unmeasured]**.
  Stage 1 measures the time once per process and the memory for keeping the parsed library.
  If either is significant, or the library grows by an order of magnitude, the index is built
  at compile time by `build.rs` instead (D60).
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
- **Errors.** "Unknown name" and its near-miss suggestions search the index, so `List.sortt`
  still suggests `List.sort` even when the sorting file isn't loaded. **Diagnostics never
  load anything:** asking for a suggestion has no side effects.
- **The resulting model for users:**

  | Written | Result |
  |---|---|
  | `Std.List.sort` | always allowed; loads the sorting file |
  | `List.sort` | allowed, because `List` is a default name; loads it |
  | `Eq.sym` (no import) | scope error, suggesting `import Std (Eq)` or `Std.Eq.sym` |
  | `Std.Eq.sym` | always allowed |

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
  - **This is the simple stage 1 rule, not the ideal.** Its cost is that core includes
    everything those procedures depend on, which may be much more than the ~20 procedures
    themselves. Stage 1 measures that closure, and D58 stands only if it's acceptable.
  - **The later rule** (no instance system needed): a global, canonically ordered index of
    the library's `Decidable` candidates, built with the name index. `auto` always searches
    it, whatever is loaded. When a candidate's file isn't loaded, it is loaded and checked
    before the candidate is tried. The index is only a hint, never trusted, because the
    declaration is still checked before use. Then `auto`'s result depends on the program and
    the library version only.

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
- **No bypassing the loader.** Compiler code may refer by identity only to *core* built-ins.
  A library built-in is reached only by name, so it goes through the loader, and a debug
  assertion catches any attempt to use one before it is bound.

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
| Logic (`Void`, `Unit`, `Not`, `And`, `Or`) | `!=` is `Not`, and the registry lists `And` and `Or` (`registry.rs:77-78`). Being a default name is *not* by itself a reason to stay in core, since a default name can point into a library file (§4.3). Keeping these in core is just simpler for now |
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
   - The resolver consults the index for every lookup (§4.3), and the index is unique and
     complete, including generated names.
   - The loader tracks file states and detects cycles on static and dynamic requests (§4.2).
   - **Gate additions:**
     - the eager-versus-lazy comparison over `aoc`, the examples and the library tests
       (§4.0);
     - a duplicate-name test for the index;
     - test cases for a cross-file cycle and for a dot-notation cycle;
     - a test that loads core alone.
   - Move **Sorting** (lines 1395–2077: self-contained, no natives, not used by syntax), as
     the proof that the mechanism works.
   - **Measure:**
     - an empty file, `aoc` check and the examples benchmark;
     - the index's cost once per process, in time and in memory for the kept syntax;
     - the size of D58's core closure.
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

## 9. Review answers

Draft 1 asked the reviewer five questions. A summary of the answers:

1. **Is file-level loading sound?** Yes, and it's the right granularity. A whole namespace
   is too coarse for `Std.Nat`. Single declarations would add much more complexity:
   mutual recursion, generated definitions, checking groups. A file is an explicit,
   human-maintained bundle. The required changes (owner-file edges and dynamic cycle
   detection) are now in §4.2.
2. **Is D58 the best `auto` rule?** It's the best *simple* stage 1 rule, accepted subject to
   measuring its core closure. The cleaner long-term rule is a global candidate index, now
   in §4.5.
3. **Other sources of load-dependent meaning?** Ordinary name resolution and ambiguity,
   generated names, dot lookup, `auto`, and compiler-generated references. Diagnostics must
   have no side effects, and imports resolve against the index. Natives aren't a semantic
   problem as long as they're checked against their loaded definitions. The best defence is
   the eager-versus-lazy comparison (§4.0).
4. **Parse at start-up, or an index built at compile time?** Parse at start-up and measure.
   Build it once per process and reuse the parsed syntax. Move to `build.rs` only on
   evidence (§4.3).
5. **Missing precedents?** Lean, Agda and Idris need an explicit import before a fully
   qualified name from another module is available. Stitchwort is deliberately different:
   references establish library dependencies. §3 and §4.3 now say so.

The reviewer also proposed the sentence that is now §4.0's invariant.

## 10. Decisions

| ID | Question | Review | Recommendation |
|---|---|---|---|
| D57 | Rename what's left of the prelude to `std/core.sw`, and drop the word "prelude"? | Agree to defer | **Accepted by Matt (20 Oct 2026)**: the core file is `std/core.sw` |
| D58 | For stage 1, keep every `Decidable` procedure in core, so `auto` never depends on what's loaded (§4.5)? | Agree with changes (measure; global candidate index later) | Yes, as revised |
| D59 | Load the library a file at a time, with owner-file edges, dynamic cycle detection, and no cycles between library files (§4.2)? | Agree with changes (now included) | Yes |
| D60 | Build the name index once per process by a declaration-collection phase that checks uniqueness, keeping the parsed syntax; `build.rs` only if measured slow (§4.3)? | Agree with changes (now included) | Yes |
| D61 | Run library tests only under a library target, never in projects (§4.7, SW-146)? | Agree | Yes |
| D62 | Stage as in §7, moving Sorting first, with the eager-versus-lazy, duplicate-name and cycle tests in the stage 1 gate? | Agree (with those tests) | Yes |

## As built (stage 1)

**Code.** `crates/elab/src/library.rs` (index, loader), `crates/elab/src/std/` (the files),
`crates/driver/tests/std_library.rs` (the gate's tests), `dev/t std`.

- **Layout (§4.1).** `crates/elab/src/std/core.sw` is the old `prelude.sw` (D57: renamed; the
  Rust const is still `PRELUDE` and `Session::with_prelude` keeps its name, because dozens of
  tests edit `PRELUDE`'s text). Library files are listed in `LIBRARY_FILES` (a test checks the
  list against the directory). One file so far, `std/List/Sort.sw`.
- **No namespace line in library files (deviation from §4.1).** A library file is written as the
  prelude is (`def List.sort`, `theorem Nat.addRotate`), and each declaration goes in the
  namespace its name says, so one file can add to `Bool`, `Nat`, `List` and `Ordering`. A single
  `namespace` line couldn't say that. The index derives each name's full key the way loading does.
- **Index (§4.3).** Built once per process (`LibraryIndex::standard`) from the parsed core and
  library files: every declared name, with generated ones (constructors, record fields, ability
  operations and their `%` helpers), mapped to its file; a duplicate full name, across core,
  library or generated, fails the build. The parsed syntax is kept and reused when a file loads
  (and the core's, for `Session::new`). A test compares the index with the names an eager load
  makes, both ways.
- **The index is the name table (§4.3).** Each library name is entered in the one name table as
  `Global::Pending(file, kind)`. So resolution, imports, `(..)`, the namespace tree, ambiguity,
  dot notation and suggestions already read the whole library and none of them loads. Loading a
  file replaces its entries in place. `Pending` reaching the checker is an internal error.
- **Loading (§4.2, §4.3).** Before a module is checked, `dependencies()` collects the files its
  references resolve to; files load in canonical order (Kahn's algorithm, ties by path), each
  after the files it needs. A file's own edges come from the same resolver, run once when the
  index is built. A nested load sets the module state aside and restores it.
- **Deviation: dot notation is over-approximated before checking, not loaded during it.**
  Loading in the middle of checking needs `&mut Elaborator` where the checker has `&Elaborator`,
  plus metavariable and module state that nested elaboration would clobber. Instead `x.f` loads
  every file with a function whose last name component is `f`, exactly as `module.rs` already
  treats `.f` among a module's own declarations (`speculative` dependencies). Resolution is
  unaffected (it uses the full index either way); the cost is that `xs.map` may load a file that
  `List.map` alone wouldn't. Cycles through dot notation are therefore found with the static
  edges. If a `Pending` name is reached at check time anyway, the error says so and names the
  file (and both files, if one is loading).
- **Cycles.** `load_order` reports a cycle, `E-INTERNAL` naming every file in it; a request for
  a file that is loading is reported the same way. Tests: a two-file cycle, a three-file one, a
  cycle through dot notation.
- **Natives and the registry (§4.6).** `Builtin::home()` (core or library; the library list is
  empty so far, since Sorting has no natives), `finish_core` checks only core built-ins,
  `check_registry_complete` checks all (a test loads every file first), and a debug assertion
  fires if compiler code uses a library built-in that isn't bound. Library natives bind as their
  file loads, because a library file is elaborated in prelude mode.
- **Tests (§4.7).** `test`s in the core and library files are skipped unless
  `Elaborator::library_tests` is set; they are marked `library` and `Session::run_tests` never
  runs them. `Session::with_library_tests().run_library_tests(..)` does (gate test
  `the_standard_library_passes_its_own_tests`; there are no library tests yet). The library
  test target is `dev/t std`, and all of it runs in the gate.
- **Eager mode and gate additions (§4.0, §7).** `Session::eager()` loads every file first.
  `std_library.rs` loads `examples/accept`, `extract`, `reject`, `soundness`, the example
  projects and `aoc/` in a lazy and an eager session and requires the same accept or reject,
  the same rendered errors, the same hash for every declaration. It also covers: the
  duplicate-name index test, the cycle tests, a core-alone test (every example that loads no
  library file behaves identically with no library installed, and a program using records,
  `==`, `calc`, `auto`, abilities and text works), D58 (`library_decision_procedures` is empty,
  with a negative control), the registry homes, and load order independent of mention order.
  `flake.nix` now includes `aoc/` in the build's sources for this.
- **`hash_stability`** now uses `Session::eager()` (library defs would otherwise count as the
  example's own); its `prelude` snapshot is sorted by name, since the library loads after the
  core. The 638 lines are the same set as before the move (`sort | diff`: identical), so every
  moved declaration (91) has its old hash.
- **Not done, as stated:** D50/D55 (stage 2).

**What moved.** The prelude's "Sorting" section ran from `-- Sorting` to just before `type
Text`: 102 declarations, in `Bool`, `Nat`, `List` and `Ordering`. 91 moved to
`std/List/Sort.sw` (548 lines). 11 stayed in core because other, unmoved prelude declarations
use them: `Bool.inspect`, `Bool.toNat`, `List.sumByFrom`, `List.sumByCons`, `List.filterKeep`,
`List.filterSkip`, `List.foldLeftAppend`, `List.appendNil`, `List.appendAssoc`,
`List.occurrences`, `List.Subsequence`. They can follow when their users move (stage 3).
None of the 102 is in the D58 core closure. `Text` (line 2001 on) isn't Sorting, and stays.

**Measurements** (release builds, this machine, one run each of five or three; the baseline is
`main` at `f21af95`):

| | before | after |
|---|---|---|
| `stitchwort check` of a one-line file, wall | 0.20-0.21 s | 0.17-0.18 s (user 0.19 -> 0.16) |
| same, peak RSS | 25.4 MB | 21.3 MB |
| `stitchwort check` of `aoc/`, wall | 0.55-0.56 s | 0.55-0.56 s (RSS 39.3 -> 40.3 MB) |
| bench `examples`: steps / visits / allocations | 1,211 M / 114.4 M / 1,412 M | 944.5 M (-22.0%) / 85.9 M (-24.9%) / 1,093.5 M (-22.6%) |
| bench `examples`: peak heap | 108.9 MB | 111.1 MB (+2.1%) |
| bench `check-nested-apps` peak heap | 918 kB | 1.0 MB (+11.3%, over the 10% threshold; baseline updated) |
| index build, once per process | n/a | about 5-7 ms for 674 names (included in the above) |

`aoc/` doesn't gain: its programs use the sorting lemmas, so the file loads. The index's
memory isn't isolated: the process is 4 MB smaller overall for an empty file, because the
library file isn't checked. The kept syntax of 3,231 lines is small next to that.
`examples` bench steps fall because the examples that don't use sorting no longer check it.

**The core closure D58 implies** (`cargo test -p stitchwort-elab --release closure_report --
--ignored --nocapture`, with `PRELUDE_REPORT=<path>` to run it on another text; it prints, for
each declaration, what it needs, and `*` marks the closure). On the prelude before the move:
roots are the registry's built-ins plus every function whose result is `Decidable` (25), and the
closure is **202 of 636 declarations, 584 of 2,132 code lines (27%)**. By blocks of 250 file lines (declarations in the closure of all): 0-250: 49 of 50; 250-500: 26 of 62;
500-750: 0 of 58 (division lemmas); 750-1000: 20 of 58; 1000-1250: 1 of 54; 1250-1500: 0 of 51;
1500-2000: 0 of 81 (sorting and its lemmas); 2000-2250: 49 of 59 (`Text`, characters);
2250-2500: 14 of 40; 2500-2750: 12 of 38; 2750-3000: 27 of 48 (effects); 3000+: 4 of 37. So D58 leaves
most of the division, comparison, sorting and number-printing lemmas movable. It is acceptable, and the stage 3
split can follow the `*` marks.

**Open for stage 2 and later.**
- `Session::with_prelude` and `PRELUDE` could be renamed to core names; left because of the
  test churn.
- Library names are entered per session (674 entries today). It's cheap, but it grows with the
  library; a shared immutable table would avoid it if the library grows tenfold.
- A library file can't yet say it adds to a namespace and not declare in it; none needs to.
- Dot notation's over-approximation could be tightened (only `Def`s whose namespace is a type)
  or replaced by loading during checking if a case turns up where it over-loads badly.
- The playground: `crates/web` builds and its tests pass; the wasm build is part of the gate. The
  index build uses no clock, since `Instant` panics on wasm32.

**Stage 3 (20 October 2026).** The library is registered as six files: `Int/Int.sw` (46
declarations), `List/Sort.sw` (107), `List/Toolkit.sw` (98), `Nat/Arith.sw` (121),
`Nat/Digits.sw` (47) and `Text/Text.sw` (20). No declaration moved back into core. The one
failure registration exposed was `Text/Text.sw`'s `IO.readAllLines` naming `.lines`, which the
dot-notation pre-pass counted as a dependency on the same file; `dependencies` now leaves out
the file being loaded, as the index's edges already did. `std/core.sw` is 1,085 lines. Release
timings (median of three): `stitchwort check` of `def z: Nat := 0`, 0.04 s (before, about
0.12 s); `aoc`, 4.01 s (before, about 3.8 s).

**Trimming the core further (22 October 2026, SW-241, prelude-slim.md stage 3).** Eighteen
more natives and some helpers and lemmas became library files: `Text/Basics.sw` (`Text.length`,
`trim`, `split`, `join`, `toNat`, `toInt`, …), `Int/Basics.sw` (`Int.tdiv`, `fdiv`, `modNat`,
`abs`, `Nat.toInt`, …), `Option/Option.sw`, `Ord/Ord.sw` (`Ord.max`, `min`, `byKey`) and
`Decidable/Decidable.sw`. `std/core.sw` is 1,806 lines. Details and what stayed are in
prelude-slim.md, "As built (stage 3)".

## As built: stage 2 (compiler part, 20 October 2026, SW-165)

**Code.** `crates/elab/src/scope.rs` (`Elaborator::library_namespace`, the note in `unknown`
and in `add_imports`), `crates/elab/src/project.rs` (the pre-pass).

- **Qualifiers (D50).** A library namespace is a qualifier without import only if it is a
  default name (a root declaration of `Std`, found as a short name) or the file's own. Inside
  library files every `Std.X` namespace still works (`loading_prelude`). Otherwise the file
  must import it (`import Std (Eq)`) or write `Std.Eq.sym`. No namespace was added to the
  default set (D55).
- **Imports.** An item of `import Std (...)` may be any namespace, even one with no
  declaration of its own: it is accepted when `Std.X` is a namespace, and then counts as a
  qualifier in that file. A user file that declares `Eq.foo` with no import now gets its own
  namespace `Eq`, as it would for any unknown name.
- **Import paths are read without imports** (unchanged), so `import Effect (Comp)` no longer
  works in a program: write `import Std.Effect (Comp)`. The error is `E-IMPORT-UNKNOWN` with
  the note "`Effect` is `Std.Effect`, which isn't a default name: write
  `import Std.Effect (Comp)`".
- **New hint.** `Eq.sym` with no import is `E-UNKNOWN-NAME` with the note "`Eq` is `Std.Eq`;
  add `import Std (Eq)`, or write `Std.Eq.sym`". Dot notation (`p.sym`) is unaffected.
- **Examples.** `examples/reject/eq-qualifier-without-import.sw`,
  `examples/accept/import-std-namespace.sw`, `examples/accept/std-qualified-eq.sw`.

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
