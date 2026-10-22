# A slim prelude: everything else behind imports (SW-213), draft 1

**Date:** 21 October 2026. **Ticket:** SW-213 (D258). **Builds on:** std-library.md
(SW-148, D49–D62), namespaces.md §4.5–§4.8, interfaces.md §9 (D170, D172).
**Status:** a design note for Matt's review. Nothing is implemented.
**Decisions asked for:** D260–D267 (§9). **Decided (21 Oct 2026):** D260 option B, D261 (no import for dot notation), D266 (the 22 names) (Matt). D262, D263, D264, D267 as recommended (Claude, implementation detail). Open: D265 (stage 1 adds no import form). **Stage 1 (§8.1) is implemented.**

Claims about the code are marked **[checked]** when I read or ran the thing named, and
**[estimate]** when they come from a heuristic script or arithmetic. Line numbers are for
`main` at `f08fec1`. `Maybe` is written `Option` where the proposal talks about the
future, because SW-210 renames it; nothing here depends on that rename.

## Contents

0. [The short version](#0-the-short-version)
1. [Two axes: what's checked, and what's in scope](#1-two-axes-whats-checked-and-whats-in-scope)
2. [What the compiler needs from the core](#2-what-the-compiler-needs-from-the-core)
3. [The proposed prelude](#3-the-proposed-prelude)
4. [Layout of everything else](#4-layout-of-everything-else)
5. [The semantic choices](#5-the-semantic-choices)
6. [How other languages do it](#6-how-other-languages-do-it)
7. [Measured cost](#7-measured-cost)
8. [Staging and risks](#8-staging-and-risks)
9. [Decisions](#9-decisions)
- [Appendix A: the measurement scripts](#appendix-a-the-measurement-scripts)
- [Appendix B: per-file imports for `aoc/`](#appendix-b-per-file-imports-for-aoc)
- [Sources](#sources)

## 0. The short version

- **The earlier split was about cost, not about scope.** SW-148/151/160/165 made library
  files load only when used, but promised that "a program behaves as if everything were
  loaded" (std-library.md §4.0). Because `List`, `Nat`, `Text`, `Map` and the rest are
  default names, and a default name works as a prefix, `List.map`, `Map.insert` and every
  `Nat` lemma still work with no import.
- **Proposal, in one sentence.** The prelude keeps the *types* that built-in syntax and
  ordinary signatures need (`Nat`, `List`, `Text`, `Option`, …), but a type's *namespace*
  (`List.map`, `Nat.addComm`) needs `import Std (List, Nat)`. Dot notation (`xs.map f`,
  `|> .map f`) keeps working without an import, because the value's type picks the
  namespace.
- **Library types leave the prelude.** `Map`, `Set`, `Vec` and `Fin` need an import even
  to name the type.
- **What a typical AoC program gains** is one line, `import Std (Int, IO, List)`, which
  says which parts of the library it uses by name. Estimated: 164 of 617 `.sw` files under
  `examples/` and `aoc/` would need a new or longer import line (§7.1).
- **The cost axis is a separate, smaller win.** An empty program costs about 0.08 s today,
  of which the core is at most about 0.07 s; the core can't shrink much while operators and
  `==` need the instances (and their laws) that live in it. The real saving is in library
  files, which are two-thirds proofs: splitting each into functions and proofs (Agda's
  `Base`/`Properties`) would let `xs.sort` load about 50 lines instead of about 1,000
  (§7.2).
- **Unchanged:** `auto` and instance search see the whole library whatever is imported
  (D172 stays); built-in syntax and `deriving` refer to the library by identity or full
  name, so they never need anything in scope.

## 1. Two axes: what's checked, and what's in scope

These are easy to mix up, and the earlier work only moved the first one.

| | (a) Checked for every program (**cost**) | (b) Usable without an import (**surface**) |
|---|---|---|
| Decided by | `crates/elab/src/library.rs` (the loader) | `crates/elab/src/scope.rs` (name resolution) |
| Today | `std/core.sw`: 2,021 lines, 375 declarations (185 `def`, 125 `theorem`, 38 `instance`, 21 `type`, 5 `interface`, 1 `ability`) **[checked: grep]** | 26 default names plus their constructors, and the prefix of each (§1.2) |
| Not checked unless used | 12 library files, 4,035 lines (`List/Sort.sw` 1,043; `List/Toolkit.sw` 708; `Map/Map.sw` 600; `Nat/Arith.sw` 493; …) **[checked: `wc -l`]** | |

### 1.1 Cost today

- Every program checks `core.sw`. By namespace its declarations are: `Int` 65, `Nat` 55,
  `Effect` 37, `Text` 35, `Ordering` 27, `Bool` 23, root 21, `List` 18, `Char` 18, `Maybe`
  16, `Show` 13, `Pair` 12, `Decidable` 11, `Ord` 6, `DecEq` 6, others 12 **[checked: grep
  of declaration lines]**.
- Not counting comments and blank lines, core is 790 lines of code and 525 of proofs. The
  library files are 505 lines of code, 2,259 of proofs and 50 of tests **[checked:
  `split.py`, Appendix A]**. `List/Sort.sw` is 49 lines of code and 726 of proofs.
- A library file loads when a program refers to anything in it. Dot notation is
  over-approximated: `xs.f` loads *every* library file with a function whose last name is
  `f` (std-library.md "As built", `library.rs:102`) **[checked]**.

### 1.2 Surface today

- **Default names are the root declarations of `Std`** (namespaces.md §4.6). The scope
  table records every `Std.X` with no further dot as a default name, plus the alias `not`
  (`scope.rs:279-287`, `ALIASES` at `scope.rs:35`) **[checked]**. That gives 21 in core
  (`Void`, `Unit`, `Not`, `And`, `Or`, `Nat`, `Bool`, `List`, `Maybe`, `Pair`,
  `Decidable`, `Char`, `Ordering`, `Text`, `Int`, `IO`, `DecEq`, `Ord`, `Show`, `Add`,
  `Mul`) and 4 in library files (`Fin`, `Map`, `Set`, `Vec`) **[checked: grep]**.
- **A default name is also a prefix.** `List.map` resolves through the short name `List`
  to `Std.List`, then looks up `map` (`resolve`, `scope.rs:439-470`). So the whole
  namespace of every default type is usable by prefix.
- **Only `Eq`, `Effect` and `Builtin` need an import** (D50, D55): `import Std (Eq)`, with
  the hint "`Eq` is `Std.Eq`; add `import Std (Eq)`, or write `Std.Eq.sym`"
  (`scope.rs:884-895`) **[checked]**.
- **Dot notation needs no import**: `xs.map` finds the namespace from the type
  (`dot.rs:205-217`) **[checked]**.

So almost nothing is behind an import today. That is the gap this note closes.

## 2. What the compiler needs from the core

The question is what must be **loaded** (checked before any user code), versus what must
be **in scope by a short name**. The answer to the second is: nothing.

### 2.1 Must be loaded

| Need | What | Where |
|---|---|---|
| Built-in syntax and natives | The registry: about 150 built-ins (`Nat`, `Nat.add`, `Decidable.toBool`, `Bool.ifThenElse`, `List`, `Cons`, `Text.append`, `MkChar`, `Builtin.UnitType`, `Eq.sym`/`Eq.trans`/`Nat.leTrans`/`Nat.lessTrans` for `calc`, about 40 `Effect.*`, `IO`, …). All are `Home::Core` today: the library list is empty | `crates/core/src/registry.rs:56` (`LIBRARY`), `:97-237` |
| Operators | `+ * < <=` go through the `Add`, `Mul` and `Ord` dictionaries, found by full key | `numbers.rs:827-830`, `interfaces.rs:1432-1448`, `:1637` |
| `==`, `!=`, `if h: x = y` | `DecEq` and its instances | `interfaces.rs:1484` |
| Interpolation, `deriving (Show)` | `Show` and its instances | `derive_show.rs`, `interfaces.rs:1440` |
| `deriving (DecEq, Ord)` | Writes source with full names: `Std.Eq.cong`, `Std.Nat.equal`, `Std.Decidable.Yes`, `Std.Ord.fromCompare`, `Std.Ordering.byTagTrans`, … (about 40 names) | `derive.rs:555-647`, `derive_ord.rs` |
| Decisions in conditions | `Std.Bool.True`/`False` written by name | `logic.rs:281` |
| `auto` | Every `instance` whose result is `Decidable …` (D58), and every interface instance (D170) | `auto.rs:307` |
| Compact text, JS natives | `List` and `Char` pinned by content hash; `Nat`, `Int`, `Text` and the 14 text natives pinned by hash in the JS backend | `chars.rs:140-162`, `crates/js/src/lib.rs:2455-2492` |
| The runner | `Std.Pair.fst (Std.IO.simulate …)` | `crates/driver/src/run.rs:271` |

**Instances drag their laws in.** `Nat.instAdd` needs `Nat.addAssoc` and `Nat.addComm`
(`core.sw:2011-2012`); `Ord` instances need their `compare` laws; `List.instOrd` needs
`List.compareLex` and its three laws. Since `a + b` on `Nat` goes through `Nat.instAdd`
(the bootstrap note at `core.sw:2008-2010`), these proofs must be checked before any
program that adds two numbers. This is why core grew back to 2,021 lines after stage 3
left it at 1,085 (std-library.md, "Stage 3"): the interfaces lanes put instances and laws
in core, as D170 required.

### 2.2 Must be in scope by a short name: nothing

Every compiler reference above is by identity (the registry) or by a full key starting
`Std.` (`derive.rs`, `numbers.rs`, `interfaces.rs`, `logic.rs`, `run.rs`) **[checked:
grep for quoted `"Std.` and for unqualified names such as `"Yes"`, `"Cons"` in
`crates/elab/src`; the only short one is the alias target `"Bool.not"`, `scope.rs:35`]**.
`Std.…` always resolves, whatever the file imports (`Qualifier::Std`). So the compiler can
use `Std.List.append` for `++` without the user having `List.append`, or even the prefix
`List.`, in scope.

**Consequence:** the prelude can be chosen for users alone. The only constraint the
compiler puts on it is that error messages and the printer show types such as `List Nat`,
which should be nameable by the reader. That is the main reason to keep the types.

## 3. The proposed prelude

**Rule: the prelude is the vocabulary of the built-in syntax, plus `Option`.** A name is
in it if a literal, operator or keyword produces or needs it, or if nearly every signature
mentions it. It holds types, interfaces, one ability, their constructors, and `not`. No
functions and no theorems.

| Name (with constructors) | Why it's in |
|---|---|
| `Nat` (`Zero`, `Succ`) | Number literals; `+ - * / %` |
| `Int` (`OfNat`, `NegSucc`) | Unary `-` and literals at type `Int` |
| `Bool` (`True`, `False`) | `if`, `==`, `<` as booleans |
| `Char` (`MkChar`) | `'a'` |
| `Text` (`MkText`) | `"…"`, `++`, interpolation |
| `List` (`Nil`, `Cons`) | `[…]`, `++`, list patterns |
| `Pair` (`MkPair`) | `(a, b)` |
| `Option` (`Some`, `None`) | Not syntax, but in every mainstream prelude (Rust, Scala, Haskell, Elm, Idris), and returned by `Text.toNat`, `List.head`, … |
| `Ordering` (`Less`, `Equal`, `Greater`) | The result of `Ord`'s `compare` |
| `Unit` (`Trivial`), `Void`, `Not` | `!=` is `Not`; `Not p` is `p -> Void`; `auto` proves `Unit` |
| `And` (`Both`), `Or` (`Inl`, `Inr`) | `&&`, `||` on propositions |
| `Decidable` (`Yes`, `No`) | `if h:`, `==`, and writing a decision procedure |
| `DecEq`, `Ord`, `Add`, `Mul`, `Show` | `==`, `<`, `+`, `*`, interpolation, and `deriving (…)` |
| `IO` | `main(): {IO} ()` |
| `not` | The alias of `Bool.not` (namespaces.md §4.6) |

That's 22 names, down from 26: **`Map`, `Set`, `Vec` and `Fin` leave** (D266). They are
library types that no syntax produces.

**A type's own declaration comes with it.** What the type's declaration generates is part
of the type, not of its namespace: constructors (`List.Cons`, also short `Cons`), record
fields, and an ability's operations (`IO.print`, `IO.readLine`, `IO.readAll`). These stay
usable with the type. Everything *added* to the namespace afterwards (functions such as
`List.map` or `IO.readAllLines`, and theorems such as `Nat.addComm`) needs the namespace
imported (D260). This is the same line Haskell draws between `data` and the functions in
`Data.List`, and Rust between a type and its trait methods.

## 4. Layout of everything else

**Imports are about namespaces; loading is about files.** In Stitchwort an import never
loads anything (namespaces.md §4.5), and a library file can add to any namespace
(std-library.md, "No namespace line in library files"). So "which namespace" decides what
you import, and "which file" decides what you pay for. They can be designed separately.

### 4.1 Namespaces (what you import)

The namespaces stay as they are. They're already the right units, and the names don't
change:

| Namespace | Holds | Import with |
|---|---|---|
| `Std.List` | List functions and lemmas, `List.Sorted`, `List.Distinct`, … | `import Std (List)` |
| `Std.Nat`, `Std.Int` | Arithmetic, digits, division, lemmas | `import Std (Nat, Int)` |
| `Std.Text`, `Std.Char` | Splitting, parsing, `Text.lines`, character classes | `import Std (Text, Char)` |
| `Std.Option`, `Std.Pair`, `Std.Bool`, `Std.Ordering` | Small helpers and lemmas | `import Std (Option)` … |
| `Std.Map`, `Std.Set`, `Std.Vec`, `Std.Fin` | Library types and their functions | `import Std (Map)` (now also needed for the type) |
| `Std.Eq`, `Std.Void`, `Std.And`, `Std.Or`, `Std.Decidable` | Logic lemmas (`Eq.trans`, `Void.absurd`, `And.left`) | `import Std (Eq, Void)` |
| `Std.Ord`, `Std.Show`, `Std.DecEq` | Interface helpers (`Ord.max`, `Show.fromText`) | `import Std (Ord)` |
| `Std.IO` | `IO.readAllLines`, `IO.simulate` | `import Std (IO)` |
| `Std.Effect`, `Std.Builtin` | The machinery behind abilities | as today |

### 4.2 Files (what you pay for): functions apart from proofs

**Proposal (D264): split each library area into a functions file and a proofs file, with
the same namespace and names.** For example:

```
std/List/List.sw          -- namespace Std.List: map, filter, sort, scanLeft, …
std/List/Properties.sw    -- namespace Std.List: lengthAppend, sortPerm, sortSorted, …
std/Nat/Nat.sw            -- digits, pow, divides, …
std/Nat/Properties.sw     -- modAddMod, addRotate, …
```

- A program that writes `xs.sort` loads `List/List.sw` only. A proof that mentions
  `List.sortPerm` also loads `List/Properties.sw`. Nobody imports anything different: both
  are in `Std.List`, and `import Std (List)` covers both.
- The rule: **a functions file may not depend on a proofs file.** A function whose
  definition needs a lemma (a termination argument, an `auto` side condition) keeps that
  lemma in its functions file. A library test checks the rule, like the no-cycle test.
- Large proof files can be split further by topic (`List/Properties/Sort.sw`), since the
  unit of loading is a file (D59).
- This is Agda's `Data.List.Base` / `Data.List.Properties`, except that Agda users must
  import both and conventionally give both the qualifier `List` [A2]. Here the names are
  one namespace from the start.

### 4.3 The core

- **Keep D58 and D170 for now.** Every `Decidable` procedure and every instance, with its
  laws, stays in core. Operators on `Nat` and `Int`, `==` on every built-in type and
  `deriving` need them before any program runs (§2.1).
- **Move what nothing in §2.1 needs**, as std-library.md's stage 3 did, using the existing
  `closure_report` tool: for example `Text.split`/`join`/`trim`, `Int.tdiv`/`fdiv`, the
  `Option` helpers, `Bool.xor` and its lemma. I estimate a few hundred lines, worth about
  0.01–0.02 s per program **[estimate: §7.2's per-line cost]**. Natives that move become
  `Home::Library` built-ins (D56; `registry.rs:56`).
- **Later, separately:** the instance index that interfaces.md §9.2 and std-library.md
  §4.5 already describe, an `(interface, head) → file` map that loads an instance's file on
  demand. That is the only way to take `List.instOrd`'s laws and the `Show` machinery out of
  core. It needs loading during checking, which stage 1 avoided. It isn't proposed here.

## 5. The semantic choices

Each is a decision in §9. For each: options, what follows, precedent, recommendation.

### 5.1 Is `List.map` usable without `import Std (List)`? (D260)

| Option | Example | Consequence |
|---|---|---|
| **A. As today:** a prelude type's prefix works everywhere | `List.map` just works | No surface change. Rust (`Vec::new`), Scala (`List.fill`), Elm (`List.map`), Lean (`List.map`) |
| **B. The type is in the prelude; its namespace needs an import** | `def f (xs: List Nat)` works; `List.map` needs `import Std (List)` | Every file says which library namespaces it uses by name. About 164 files need a line (§7.1). Haskell is the nearest: `[a]` is built in, but `sortOn` needs `import Data.List` |
| **C. Neither:** only syntax-produced types without import | Even `List Nat` in a signature needs the import | Agda (no prelude at all). Error messages would show types the reader can't write without an import |

**[recommendation: B]** It is what Matt asked for (list functions behind imports), it
matches his preference for explicit imports over free names, and the "type in scope,
functions imported" split is familiar from Haskell and from Rust's non-prelude types
(`HashMap::new` needs `use std::collections::HashMap` or the full path). With C, every signature and
every error message would depend on imports, for no gain in clarity. The error for B
reuses the existing hint (`scope.rs:884-895`): "`List.map` needs `import Std (List)`".

### 5.2 Does dot notation need the namespace imported? (D261)

`xs.map f` and `xs |> .map f` find `map` in the namespace of `xs`'s type.

| Option | Consequence | Precedent |
|---|---|---|
| **A. No import needed** (today) | `xs.map f` works in any file. Only qualified names need imports | Lean: "the identifier after the dot is looked up in the namespace of the term's type" [L3], no `open` needed. Rust: a type's own (inherent) methods need no `use`. Scala 3: an extension method "defined in the implicit scope of the type of `r`" applies without import [S3]. Go: methods work on a value from any package |
| **B. Same as the qualified name:** `xs.f` works exactly when `T.f` could be written | One rule ("dot is sugar for `T.f xs`"). 181 files need a line instead of 164, and `List` appears in 127 of them instead of 90 (§7.1). The loader could load exactly the imported namespaces' files instead of every file with an `f` | Rust trait methods need the trait in scope [R2]; Scala extension methods outside the type's implicit scope need an import [S3]; Kotlin extension functions |

**[recommendation: A]** Dot notation names nothing the reader has to find: the receiver's
type says where `map` comes from, which is the point of it. Every precedent where methods
need an import (Rust traits, Scala and Kotlin extensions) is about methods defined
*away from* the type by someone else; `Std.List`'s functions are the type's own, like Rust's
inherent methods. The AoC style leans on pipes (`turns |> .scanLeft … |> .count …`,
`aoc/src/Aoc/Day01/Day01.sw:35-38`), and requiring `import Std (List)` for those adds a
line that says only what the types already say. B's loading advantage is real, but it's an
implementation matter: the loader can be made exact by indexing `(namespace, member)`
instead of the last name component (std-library.md's "tightened" note), with no change in
meaning. If Matt prefers the single rule, B is consistent and cheap to implement; this is
the closest call in the note.

### 5.3 What does `auto` search? (D262)

| Option | Consequence |
|---|---|
| **A. All of `Std`, whatever is imported or loaded** (D58's meaning, today) | `if x == y` means the same in every file. Implemented by keeping procedures in core now, by an index later (§4.3) |
| B. Only imported namespaces | `x == y` on lists would fail without `import Std (List)`, though `List` is in the prelude. Whether a condition checks would depend on imports, which D172 rules out for instances |
| C. An explicit registry the user extends | Extra machinery; nothing needs it |

**[recommendation: A]** Imports decide which names can be written, nothing else
(namespaces.md §4.5). Lean, Haskell and Rust find instances regardless of what's imported
by name; Scala's givens are the exception, and they give up coherence for it
(interfaces.md §4.1).

### 5.4 Are instances found without importing their namespace? (D263)

**[recommendation: yes, keep D172]** `Ord (List a)` and `Show (Map k v)` are found
whether or not the file imports `List` or `Map`. The orphan rule (an instance lives with
its interface or its type, D158) means there's exactly one candidate, and it's in a file
the program already depends on, or in core. A file that uses a `Map` it got from a
function, without `import Std (Map)`, still compares and prints it. No precedent among
coherent languages makes instance search depend on imports; Haskell's orphan warnings exist
precisely because imports *can* affect it there [H2].

### 5.5 Theorems: how fine-grained are imports for proofs? (D264)

| Option | Example | Consequence |
|---|---|---|
| **A. Lemmas share the namespace with functions; files are split** | `import Std (List)` gives `List.map` and `List.lengthAppend` | One import per area; a program pays for proofs only if it names one (§4.2) |
| B. Separate namespaces (`Std.List.Properties`) | `import Std.List (Properties)`, then `Properties.lengthAppend` or `List.Properties.lengthAppend` | Proof code gets longer names or more imports, and the names change. Agda's split, which its own style guide papers over by importing both as `List` [A2] |

**[recommendation: A]** In Stitchwort imports don't load, references do, so the split that
saves time is the *file* split, and it needs no new names. A proof that wants the short
name writes `import Std.List (lengthAppend, sortPerm)`, as today. Lean and Mathlib also
keep lemmas in the type's namespace (`List.length_append`).

### 5.6 What does an import bring in? (D265)

Today's forms, from D50 (namespaces.md §4.5):

| Written | Gives |
|---|---|
| `import Std (List, Nat)` | The prefixes `List.` and `Nat.` (and the types, already in the prelude) |
| `import Std.List (map, filter)` | `map` and `filter` without a prefix |
| `import Std.List (..)` | Every name in `Std.List` without a prefix |
| `Std.List.map` | Always works, no import |

**[recommendation: keep these; add nothing]** `import Std (List, Nat, Text)` is one line
that says which areas a file uses. The alternative is Scala's form, `import Std.List`
with no list, meaning "the prefix `List`" [S1]. It reads well, but it's a second way to say
the same thing, and D50 deliberately left `import X ()` and the bare form free for later.
One detail changes: importing a prelude type (`import Std (List)`) is no longer a
duplicate, since it now adds the prefix; the "imported twice" warning (namespaces.md §4.5)
must not fire for it.

### 5.7 The REPL and `eval`

Inputs are checked like a file, with that file's imports. **Proposed:** the REPL accepts
`import` lines, and `stitchwort eval EXPR FILE` uses `FILE`'s imports. The playground's
REPL placeholder `List.length [1, 2]` (`web/index.html:1517`) becomes
`[1, 2].length`. This follows from D260 and isn't a separate decision.

## 6. How other languages do it

| Language | Always in scope | Lists | Proofs | Notes |
|---|---|---|---|---|
| **Lean 4** | `Init`, "automatically" imported [L1] | `List` and its functions, all in `Init`; `Batteries` adds more, as a separate package [L4] | Many lemmas in `Init` | Dot notation looks in the type's namespace with no `open` [L3]; `open Foo` gives short names [L1] |
| **Idris 2** | `Prelude`, "minimal": "the basic functions required by almost any non-trivial program" [I2] | `List`, `map`, `length` in the prelude; `Data.List` in `base` for the rest | "proofs of Nat/List properties that almost never get used in practice would probably be better in base libraries" [I2] | Our D49 in their words |
| **Agda** | Nothing | `open import Data.List` | `Data.List.Properties`, imported separately and conventionally under the same name `List` [A2] | The extreme of explicit |
| **Haskell** | `Prelude`, "imported by default into all Haskell modules unless … an explicit import statement for it" [H1] | `map`, `filter`, `foldr`, `length`, `zip`, `lines` unqualified [H1]; `sort` needs `Data.List`; `Data.Map` is imported qualified by convention | n/a | `import Prelude ()` opts out [H3] |
| **Scala** | `java.lang._`, `scala._`, `Predef._` | `List`, `Vector`, `Seq` aliased in package `scala`: "always available without an explicit import" [S1]; `Map`, `Set` in `Predef` [S2] | n/a | Collections in the default scope; extension methods outside a type's implicit scope need an import [S3] |
| **Rust** | `std::prelude`: "kept as small as possible, and is focused on things, particularly traits, which are used in almost every single Rust program" [R1] | `Vec`, `String`, `Option`, `Result`; `HashMap` needs `use std::collections::HashMap` | n/a | Trait methods need the trait in scope: "the user must bring the trait into scope as well as the types" [R2] |
| **Elm** | "as if every Elm file starts with" `import List exposing (List, (::))`, `import Maybe exposing (Maybe(..))`, `import String exposing (String)`, … [E1] | `List.map` works everywhere (the module is imported by default); `map` alone doesn't | n/a | Closest to Stitchwort today |
| **Unison** | No imports: a name resolves if it "is a suffix of exactly one fully qualified name in the environment" [U1] | `List.map` resolves by suffix to `base.List.map` [U1] | n/a | `use` is "purely a syntactic convenience" [U2] |

What this shows:

- **Everyone keeps the list *type* in the default scope** (except Agda). That supports
  keeping the types (§3).
- **Most mainstream languages also give list *functions* without an import** (Haskell
  unqualified, Elm/Scala/Lean/Rust through the type). So D260-B is stricter than they
  are. It is closest to Haskell for anything beyond the basics, and to Rust for any type
  outside the prelude. That's a deliberate choice for explicitness, not a common default.
- **Proof libraries separate lemmas from definitions** (Idris's comment, Agda's
  `Properties`), and Lean gets away without it only because it never re-checks imported
  code. Stitchwort re-checks the library on every run, so the file split (§4.2) matters
  more here than in Lean.
- **Dot notation without an import is the norm** wherever the method belongs to the type
  (Lean, Rust inherent methods, Scala implicit scope, Go). Imports are needed only for
  methods added from outside (Rust traits, Scala and Kotlin extensions).

## 7. Measured cost

### 7.1 Import lines

A throwaway script (`count_imports.py`, Appendix A) reads every `.sw` file under
`examples/` and `aoc/` and estimates the imports each would need. It is syntactic, so the
numbers are **[estimate]**s: it can't see types, so a dot call `.map` is attributed to one
namespace by a fixed preference (81 member names exist in several namespaces: `length`,
`map`, `toList`, …), and names the program declares itself are skipped.

| Rule | Files needing a new or longer import line | `aoc/` | Namespaces most imported (files) |
|---|---|---|---|
| **D260-B + D261-A (recommended):** prefixes need imports, dot doesn't | **164 of 617** (accept 78/120, extract 18/29, reject 33/278, soundness 3/50, projects 0/103) | **32 of 37** | `List` 90, `Nat` 84, `Bool` 29, `Text` 21, `Void` 20, `Pair` 19, `IO` 16, `Maybe` 16, `Int` 14, `Decidable` 11, `Vec` 9 |
| D260-B + D261-B: dot needs imports too | 181 of 617 | 36 of 37 | `List` 127, `Nat` 89, `Text` 76, … |
| Only D266 (`Map`, `Set`, `Vec`, `Fin` leave the prelude) | 16 of 617 | 7 of 37 | `Vec` 9, `Fin` 6, `Set` 2, `Map` 2 |

Most lines are short: under the recommended rule 84 files need one item, 25 two, 20
three, and 6 need six or more (the AoC proof files, which use `Bool`, `Void`,
`Decidable`, `And`, `List`, `Nat`). Rust tests that embed programs need the same edit:
about 30 `.rs` files mention `List.length`, `List.map` or `Nat.toText` **[checked: grep;
an upper bound, some are compiler sources]**. The playground bundles `aoc/` as is
(`web/bundle-projects.sh`), and its inline samples (`web/index.html:466-546`) use
`List.length` and `List.append`.

**A typical AoC program, before and after:**

```
-- before: aoc/src/Aoc/Day01/Day01.sw
namespace Aoc.Day01

-- after
namespace Aoc.Day01
import Std (Int, IO, List)
```

It writes `IO.readAllLines`, `List.replicate` and `Int.modNat` with prefixes; its pipes
(`|> .scanLeft … |> .count …`) and `t.uncons`, `rest.toNat` need nothing. `IO.print` is an
operation of the ability, so it comes with `IO` (§3).

**A proof file, before and after:**

```
-- before: aoc/src/Aoc/Day02/Proofs/Part1.sw
import Std (Eq)

-- after
import Std (Bool, Eq, List, Nat, Void)
```

### 7.2 Check time

Release CLI (`target/release/stitchwort` of the main checkout, built 21 Oct 21:09), this
machine, five runs each unless noted, while other lanes were running **[checked]**:

| Program | Wall | Peak RSS |
|---|---|---|
| `stitchwort --version` (process start) | 0.01 s | |
| `def z: Nat := 0` (core only) | 0.08–0.10 s | 22 MB |
| One reference into `List/Sort.sw` | 0.27 s | 30 MB |
| One reference into each of the 12 library files | 0.42–0.44 s | 35 MB |
| `examples/accept/list-patterns.sw` (3 runs) | 0.09–0.11 s | 22 MB |
| `examples/accept/pipe.sw` (3 runs) | 0.32–0.47 s | 31 MB |
| `aoc` namespace `Aoc.Day01` (3 runs) | 0.41 s | 42 MB |
| all of `aoc` (1 run) | 2.50 s | 109 MB |

What follows **[estimate: arithmetic on the table]**:

- **The core costs at most about 0.07 s** (0.08–0.09 s minus start-up), about 0.035 ms per
  line. Shrinking it by the few hundred movable lines (§4.3) saves 0.01–0.02 s per program.
  The surface change (D260) by itself saves nothing: scope isn't cost.
- **Library files cost about 0.085 ms per line**, more than core, because they're mostly
  proofs. Loading `List/Sort.sw` costs about 0.19 s; its 49 lines of code, alone, would
  cost about 0.01 s.
- **So the functions/proofs split (§4.2) is the cost lever.** An AoC program like Day 1
  (0.41 s, most of it library) could drop to roughly the core's 0.1 s plus its own code,
  if what it loads is functions only. The proof files (`Aoc.DayNN.Proofs`) would keep
  today's cost, since they use the lemmas.
- **Dot notation's over-approximation adds to this** (`xs.map` loads every file with a
  `map`). With functions files, the over-approximation loads only small files, so
  tightening it matters less.

## 8. Staging and risks

### 8.1 Stages (each separately mergeable)

1. **Prelude contents and prefixes (D260, D265, D266).** In `scope.rs`: a default name
   is a type but not a prefix, unless the file imports it or the member is part of the
   type's declaration (constructor, field, ability operation). `Map`, `Set`, `Vec`, `Fin`
   stop being default names. The error hint (`scope.rs:884-895`) covers prelude types too.
   Then migrate: run `check` over `examples/`, `aoc/`, the Rust test programs and the
   playground samples, and add the import each error names (an exact file list,
   mechanical work for DeepSeek). Update namespaces.md §4.6 and std-library.md §0.
2. **Split library files into functions and proofs (D264)**, one area per commit
   (`List`, `Nat`, `Text`, `Int`, `Map`/`Set`, `Vec`/`Fin`), with the "functions files
   don't depend on proofs files" test, and the hash comparison std-library.md §4.8 used.
   Measure an empty file, Day 1 and `aoc` after each.
3. **Trim core** of what nothing in §2.1 needs (§4.3), using `closure_report`.
4. **Later, own tickets:** an exact dot-notation loader; the instance/decider index
   (§4.3), which is what would shrink core substantially.

Stage 1 is the user-visible change and could go first or last; stages 2–3 change no
program's meaning, and can run in parallel with it.

### 8.2 Risks

- **Hash pins.** Compact text and the JS natives check `List`, `Char`, `Nat`, `Int`,
  `Text` and the text natives by content hash (`chars.rs:140-162`,
  `crates/js/src/lib.rs:2455-2492`). Moving a declaration to another file doesn't change
  its hash (hashes leave out names, and bodies move verbatim). A changed body would
  silently turn off compact text or a JS native; the existing tests catch that. SW-210's
  rename will change some hashes anyway.
- **`deriving` and other generated code** use full `Std.` names (§2.1), so D260 doesn't
  affect them. Moving one of those names *out of core* would: `derive_ord.rs` names
  `Std.Ordering.byTagTrans` and seven other `Ordering` lemmas. Stage 3 must keep every name
  in §2.1's table in core; the core-alone test (std-library.md stage 1) runs every compiler
  path that names a declaration.
- **Error messages.** Printed types (`List Nat`) stay readable because the types stay in
  the prelude. The hint for a missing prefix must say *which* import (`import Std (List)`)
  and not fire for dot notation.
- **The AoC proofs** get the longest lines (up to nine items, Appendix B). They're
  mechanical, but they touch every proof file; the playground bundle and the AoC docs
  quote some of them.
- **Ambiguity.** A file that imports `Std (List)` and declares its own `List.foo` in its
  namespace is already handled (`E-NAMESPACE-RESERVED` stops a program's namespace from
  starting with `List`; `scope.rs:424-433`).
- **Lazy-loading invariant.** None of this changes std-library.md §4.0: what's loaded
  never changes what a program means. D260 changes what *resolves*, and does so the same
  way whatever is loaded.

## 9. Decisions

| ID | Question | Recommendation |
|---|---|---|
| D260 | Do a prelude type's namespace functions and lemmas (`List.map`, `Nat.addComm`, `IO.readAllLines`) need `import Std (List)`, while the type, its constructors, fields and ability operations stay usable without one? (§5.1) | [Yes: option B] |
| D261 | Does dot notation (`xs.map`, `\|> .map`) need the namespace imported? (§5.2) | [No: the receiver's type picks the namespace, as in Lean, Rust's inherent methods and Scala's implicit scope] |
| D262 | Does `auto` search all of `Std` regardless of imports? (§5.3) | [Yes: keep D58's meaning; procedures stay in core until an index exists] |
| D263 | Are instances found without importing their namespace? (§5.4) | [Yes: keep D172] |
| D264 | Lemmas: same namespace as their functions, with each library area split into a functions file and a proofs file that functions files never depend on? (§4.2, §5.5) | [Yes] |
| D265 | Import forms: `import Std (List, Nat)` for prefixes and `import Std.List (map)` for short names, with no new bare `import Std.List` form? (§5.6) | [Yes] |
| D266 | The prelude is §3's 22 names: syntax's types, `Option`, `Ordering`, the five interfaces, `IO`, `not`; `Map`, `Set`, `Vec`, `Fin` leave it? (§3) | [Yes] |
| D267 | Stage as in §8.1: prefixes and migration; then the functions/proofs split; then trimming core; the instance index later? | [Yes] |

## As built (stage 3, 22 October 2026, SW-241)

`core.sw` went from 2,021 to 1,806 lines, and from 431 to 386 declarations as the checker
counts them (the closure report counts 375 source declarations before the move). Nothing
was renamed, so every full name is as it was, and a program needs the same imports
as before: scope depends on the namespace, not on which file declares a name.

**What moved, and where.**

- `Text/Basics.sw` (new, 100 lines): `Text.length`, `isEmpty`, `uncons`, `fold`, `trim`,
  `split`, `join`, `toNat`, `toInt`, and their helpers (`Text.foldChars`, `dropSpaces`,
  `splitChars`, `joinChars`, `readDigits`, `Char.isSpace`, `Char.digitValue`, and so on).
- `Int/Basics.sw` (new, 63 lines): `Int.abs`, `toNatChecked`, `sign`, `modNat`, `tdiv`,
  `tmod`, `fdiv`, `fmod`, and `Nat.toInt`.
- `Option/Option.sw` (new): `Option.map` and `Option.flatMap`.
- `Ord/Ord.sw` (new): `Ord.byKey`, `max`, `min`, `compareSelf` and `Ordering.flipSelf`.
- `Decidable/Decidable.sw` (new): the `Decidable.toBool…` lemmas, `Bool.decTrueToBool` and
  `DecEq.sound`.

The text and integer functions went into new small files, not into `Text/Text.sw` and
`Int/Int.sw`. My first try used those two, and a program that only called `Text.split`,
`trim` and `toNat` got slower: 69 ms before and 128 ms after, because `Text.sw` needs
`List/Toolkit.sw` and `Nat/Arith.sw`. The `Basics` files need the core alone (and
`Option.map`). The same program now takes 65 ms.

**Natives.** Eighteen built-ins are now `Home::Library` (`registry.rs`, `LIBRARY`): `Int.tdiv`,
`tmod`, `fdiv`, `fmod`, `modNat`, `abs`, `toNatChecked`, `sign`, `Nat.toInt`, `Text.toInt`,
`toNat`, `trim`, `split`, `join`, `length`, `isEmpty`, `uncons` and `fold`. Their JS and runtime pins are by content hash, which didn't change. When
the file isn't loaded the native just isn't bound, and the definition is used as written.

**Hashes.** Moving a declaration didn't change any hash: the `hash_stability` snapshots
(prelude, projects, examples) pass with no diff.

**What stayed in core, and why.**

- Every name in §2.1: the registry's built-ins, the names `deriving` writes in full
  (`Eq.cong`, `Nat.compareTrans`, `Ordering.byTagTrans`, `Show.arg` and the rest),
  `Bool.True` and `False`, `Pair.fst` and `IO.simulate` for the runner.
- Every `instance` and everything its law needs: the `Ordering` lemmas, `Nat.compare…`,
  `Int.compare…`, `List.compareLex…`, `Text.compare…`, the `Show` machinery
  (`Show.escapeChar` and friends), `Nat.add…` and `Nat.mul…` laws, the `Int.add` and `Int.mul`
  laws with `Bool.xor` and `Int.mulSigned`. This is why `Bool.xor` and its lemma, which the
  note listed, stay: `Int.mulAssoc` is a law of `Int.instMul`.
- Every `Decidable` procedure (D58) with its helpers (`Nat.equalSound`, `Bool.canon`,
  `List.decEq`, `Char.ext`, `Int.ofNatInjective`, …), and `Int.toNat`, which one of them uses.
- Compact-text and JS pins that name declarations in core: `Nat`, `Int`, `Text`, `List`,
  `Char`, `Text.toList`, `fromList`, `append`, `decEq`, `compare`, `Nat.toText` and
  `Int.toText` (the `Show` instances need the last two).
- The effect machinery (`Effect.*`, 30 declarations), including `swapOp`, `caseInject` and
  the rest of the `sigCase` family: the closure report can't see these as needed, because
  it doesn't resolve a name written inside its own namespace, but the registry's `sigCase`
  uses `caseInject` and `caseReply`.
- Small functions whose move would cost more than it saves: `List.length` (3 lines; its
  only home would be `List/Toolkit.sw`, 766 lines, for something nearly every program calls),
  `Nat.mulSucc` and `Nat.mulComm` (6 lines; `Nat/Arith.sw` is 517), `Nat.compareSucc`,
  `Int.addZero`, `Char.fromNat`, `Bool.inspect`.

**The tool.** `closure_report` now also treats every `instance` as a root and skips
built-ins whose home is a library file; `PRELUDE_ROOTS=<file>` adds more roots, one full name
per line (I used the `deriving` and runner names). Its answer was the move list above: with
those roots, 318 of 375 declarations are in the closure. The 57 outside are what moved, the
`Effect` ones and the small ones above.

**Cost** (release build, `STITCHWORT_TIMINGS=1`, the machine busy with other lanes):

| | before | after |
|---|---|---|
| `core` row, elab ms / kernel ms | 41-43 / 13 | 35-36 / 12 |
| `core` row, nodes / declarations | 21,678 / 431 | 20,144 / 386 |
| `check` of `aoc/`, total elab ms / kernel ms | 1,288-1,390 / 535-635 | 1,286-1,297 / 536 |
| `check` of a program using `Text.split`, `trim`, `toNat` | 69 ms wall | 65 ms wall |
| `check` of a program using `Int.tdiv`, `abs`, `Ord.max` | 67.5 ms wall | 67.5 ms wall |

So the core saves about 6 ms and 7% of its nodes per program, and no program that used a
moved name loads more than a few hundred lines for it. `aoc/` doesn't change: it loads
those files anyway. The saving is smaller than §7.2's estimate (0.01–0.02 s) because the
instance laws, which §2.1 and D170 keep, are most of what is left.

## As built (the core in small files, 22 October 2026, SW-260, D493)

`std/core.sw` (1,806 lines) is now the folder `crates/elab/src/std/core/`: 22 files of 17 to
192 lines (1,926 in all), each with a header saying what it holds and why it is in the core (§2.1). The
files are still all loaded up front, as one module, and nothing else changed: names,
namespaces, declaration order and the text of every declaration are as they were.

**How it loads.** `PRELUDE` (`crates/elab/src/lib.rs`) is the files' text joined in the order
the `core_files!` list gives, so every test that edits `PRELUDE` still works and the elaborator
sees the same declarations in the same order. The same macro builds `CORE_LAYOUT`, each file's
path and length, which maps a position in the core to its file. The files are in dependency
order (each uses only what the files before it declare); `Imports.sw` is first, so the one
`import Effect (...)` covers them all. A test (`the_core_layout_lists_every_core_file`) checks
the list against the directory and that the files join to `PRELUDE`.

**The files, in load order** (lines, header included):
`Imports` 17 (the header and the effect imports), `Logic` 45, `Data` 99 (`Nat`, `Bool`, `List`,
`Option`, `Pair`), `Equality` 58, `Decidable` 117, `Char` 37, `Division` 36,
`ListOptionPair` 76, `Ordering` 36, `Helpers` 25, `Text` 68, `Int` 143, `Effect` 185,
`IO` 41, `DecEq` 60, `Compare` 163 (laws for `Ordering`, `Nat`, `Int`), `CompareData` 150
(laws for `List`, `Pair`, `Option`, `Char`, `Text`), `Ord` 128, `OrdDerived` 79, `Show` 131,
`Arith` 192 (arithmetic laws), `AddMul` 40. The 1,806 old lines are cut where the old file had a
section comment, in the old order, so no declaration moved relative to another: reordering
would have changed instance search order (`auto` searches defs newest first). The headers add
the other 120 lines.

**Navigation.** The core is still one source file in a session (`<prelude>`), so error
messages that point into it show positions in the joined text. The navigation index
(`nav::index_json`) splits it: a core file is listed as `{"path":
"crates/elab/src/std/core/Data.sw","std":"core/Data.sw"}`, and line numbers are counted from the
start of that file. `std-source core/Data.sw`, the VS Code extension's read-only view and the
playground's library view read the file by that `std` name (`nav::std_source`). Both follow
the same `std` marker as any library file; the editor and the browser needed no change but
their tests' expectations (`core.sw` became `core/Data.sw` and `core/AddMul.sw`).

**Hashes.** No hash changed: `dev/t hashes` passes with no snapshot diff. The one snapshot
that changed is `crates/driver/tests/snapshots/navigation__nav-project.snap`, which prints
`<prelude>:line:col`: the headers shifted the core's lines (`Nat` from 60 to 76).

## Appendix A: the measurement scripts

Kept outside the repository, in the session scratchpad
`/private/tmp/claude-501/-Users-matt-repos-misc-funlang/63e6bfc9-6f2e-43e5-9da9-a59432a877ec/scratchpad/prelude-slim/`:

- `count_imports.py REPO [OUT.tsv]`: the §7.1 estimate. It collects every `Std`
  declaration's namespace and last name, treats constructors, record fields and ability
  operations as part of their type, strips comments and string literals (keeping `${…}`
  code), and then per file finds qualified uses (`List.map`), dot uses (`.map` after an
  expression or in a pipe section) and the four library type names, minus names the
  file's project declares and minus existing `import` lines. Known errors: a dot call is
  attributed by preference order (`List` before `Text` before `Nat` …), so `.map` on an
  `Option` counts as `List`; record fields of program types written on several lines may
  be miscounted as library names.
- `split.py REPO`: code, proof and test lines per library file (§1.1).
- `time.sh FILE…`, `time-aoc.sh [NAMESPACE]`: the §7.2 timings (`/usr/bin/time -l`).
- `empty.sw`, `sortonly.sw`, `all.sw`: the probe programs. The last two end in an
  unsolved-implicit error after loading, which doesn't affect what they measure.

## Appendix B: per-file imports for `aoc/`

Under D260-B with D261-B (the stricter rule; the recommended rule drops the namespaces
that only dot calls use). **[estimate: `count_imports.py`]**

| File | Import line |
|---|---|
| `Common/Range.sw` | `import Std (List, Text)` |
| `Common/Proofs/Range.sw` | `import Std (Bool, List, Nat, Void)` |
| `Day01/Day01.sw` | `import Std (IO, Int, List, Text)` |
| `Day01/Input.sw`, `Day03/Input.sw`, `Day05/Input.sw`, `Day06/Input.sw` | `import Std (Text)` |
| `Day01/Proofs/Part2.sw` | `import Std (Bool, Int, List, Nat, Text)` |
| `Day02/Day02.sw` | `import Std (List, Nat, Text)` |
| `Day02/Proofs/Part1.sw` | `import Std (Bool, List, Nat, Void)` (plus today's `Eq`) |
| `Day02/Proofs/Part2.sw` | `import Std (Bool, Decidable, List, Nat, Text, Void)` |
| `Day02/Proofs/Repeated.sw` | `import Std (Bool, Decidable, List, Nat, Void)` |
| `Day03/Day03.sw` | `import Std (Char, IO, List, Nat, Text)` |
| `Day03/Proofs/Best.sw` | `import Std (Bool, Char, Decidable, List, Nat, Or, Pair, Text, Void)` |
| `Day04/Day04.sw` | `import Std (IO, List, Maybe, Pair, Text, Vec)` |
| `Day04/Input.sw` | `import Std (List, Maybe, Text)` |
| `Day04/Proofs/Core.sw` | `import Std (And, Bool, Decidable, List, Nat, Text, Void)` |
| `Day04/Proofs/Parse.sw` | `import Std (Fin, List, Maybe, Nat, Text, Vec, Void)` |
| `Day04/Proofs/Part1.sw` | `import Std (Bool, List, Nat, Text, Vec)` |
| `Day04/Proofs/Part2.sw` | `import Std (And, Bool, List, Nat, Pair, Text, Vec, Void)` |
| `Day04/Proofs/Spec.sw` | `import Std (List, Maybe, Nat, Text, Vec)` |
| `Day04/Proofs/Sweep.sw` | `import Std (And, Bool, Decidable, List, Nat, Pair, Text, Vec, Void)` |
| `Day04/Proofs/Window.sw` | `import Std (And, Bool, Decidable, List, Nat, Text, Vec, Void)` |
| `Day05/Day05.sw` | `import Std (IO, List, Nat, Text)` |
| `Day05/Proofs/Part2.sw` | `import Std (Bool, List, Nat, Ordering, Text, Void)` |
| `Day06/Day06.sw` | `import Std (Char, IO, List, Maybe, Nat, Text)` |
| `Day06/Proofs/Correct.sw` | `import Std (Bool, List, Maybe, Nat, Text)` |
| `Day06/Proofs/Grid.sw` | `import Std (List, Nat, Text)` |
| `Day06/Proofs/Spec.sw` | `import Std (Char, List, Maybe, Nat, Text)` |
| `Day07/Day07.sw` | `import Std (IO, List, Maybe, Nat, Text)` |
| `Day07/Input.sw` | `import Std (List, Maybe, Text)` |
| `Day07/Proofs/Distinct.sw` | `import Std (Bool, List, Maybe)` |
| `Day07/Proofs/Grid.sw` | `import Std (List, Maybe, Nat, Text)` |
| `Day07/Proofs/Part1.sw` | `import Std (Bool, DecEq, List, Maybe, Nat, Text, Void)` |
| `Day07/Proofs/Part2.sw` | `import Std (List, Maybe, Nat, Void)` |
| `Day07/Proofs/Spec.sw` | `import Std (List, Maybe, Text)` |

## Sources

- [L1] Theorem Proving in Lean 4, "Interacting with Lean": Lean "automatically imports the
  contents of the library `Init` folder"; "`open Foo` then creates temporary aliases".
  https://lean-lang.org/theorem_proving_in_lean4/Interacting-with-Lean/
- [L3] The Lean Language Reference, "Function Application", generalized field notation:
  "The identifier after the dot is looked up in the namespace of the term's type".
  https://lean-lang.org/doc/reference/latest/Terms/Function-Application/
- [L4] Batteries, "The 'batteries included' extended library for Lean 4", added as a
  package dependency. https://github.com/leanprover-community/batteries
- [I2] Idris 2 `Prelude` source, module header ("The Prelude is minimal", "proofs of
  Nat/List properties … better in base libraries").
  https://www.idris-lang.org/Idris2/prelude/source/Prelude.html
- [A2] Agda standard library style guide: `Base` "for basic operations", `Properties` "for
  lemmas about them"; "`Data.List.Properties` as `List`".
  https://github.com/agda/agda-stdlib/blob/master/doc/style-guide.md
- [H1] Haskell `base`, `Prelude`: "imported by default into all Haskell modules unless
  … there is an explicit import statement for it"; list operations.
  https://hackage.haskell.org/package/base/docs/Prelude.html
- [H2] GHC orphan instances, via interfaces.md [H4] (`-Worphans`).
- [H3] Haskell 2010 Report §5.6: "the explicit `import Prelude()` declaration prevents the
  automatic import of Prelude". https://www.haskell.org/onlinereport/haskell2010/haskellch5.html
- [S1] Scala standard library, `package.scala`: "Core Scala types. They are always
  available without an explicit import"; `type List[+A] = scala.collection.immutable.List[A]`.
  https://github.com/scala/scala/blob/2.13.x/src/library/scala/package.scala
- [S2] Scala `Predef.scala`: "accessible in all Scala compilation units without explicit
  qualification"; `type Map[K, +V] = immutable.Map[K, V]`, `type Set[A] = immutable.Set[A]`.
  https://github.com/scala/scala/blob/2.13.x/src/library/scala/Predef.scala
- [S3] Scala 3 reference, "Extension Methods", translation rules: applicable when
  "visible under a simple name, by being defined or inherited or imported", or "defined in
  the implicit scope of the type of `r`".
  https://github.com/scala/scala3/blob/main/docs/_docs/reference/contextual/extension-methods.md
- [R1] Rust `std::prelude`: "kept as small as possible, and is focused on things,
  particularly traits, which are used in almost every single Rust program".
  https://doc.rust-lang.org/std/prelude/index.html
- [R2] The Rust Book, ch. 10.2: "the user must bring the trait into scope as well as the
  types". https://doc.rust-lang.org/book/ch10-02-traits.html
- [E1] elm/core README: "it is as if every Elm file starts with these imports".
  https://github.com/elm/core/blob/master/README.md
- [U1] Unison, "Name resolution and the environment": a name resolves if it "is a suffix of
  exactly one fully qualified name in the environment".
  https://www.unison-lang.org/docs/language-reference/name-resolution-and-the-environment/
- [U2] Unison, "Use clauses": "purely a syntactic convenience".
  https://www.unison-lang.org/docs/language-reference/use-clauses/

## As built (§5.7, REPL imports, 22 October 2026, SW-225)

`stitchwort repl` takes a line starting with `import` and adds it to the imports that
expressions see, on top of the loaded file's. They accumulate over the session, and the
forms are a file's (`import Std (List, Nat)`, `import Std.List (map)`, `(..)`). A bad
import gives the usual error (`E-IMPORT-UNKNOWN`, with the same notes), and a repeat gives
`W-IMPORT-TWICE`; the names that were fine are kept. A declaration typed in is still not
accepted. There was no `:imports` command and the REPL has no other meta-commands beyond
`:t` and `:q`, so none was added. The CLI REPL loads one file, so it has no project
namespaces; the playground's Evaluate tab does, for a project's own (`import Aoc.Day02
(solvePart1)`). The Evaluate tab keeps the `import` lines entered in a list above the input,
checks each one when it is entered (`evaluate` takes the imports so far and an expression,
which may be empty to only check them), and forgets them when the example or day changes.
The code is `Session::add_imports` (`crates/driver/src/driver.rs`), which parses the line as
a module of imports and resolves them as a file's, in file 0's table, where a single file's
own imports already are.
