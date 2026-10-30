# Stitchwort: Design

**Status:** Draft 3, revised after a second review, 14 October 2026

Stitchwort is a small, strict, pure functional language. It's a fun project for exploring ideas, not a production language. It combines four ideas that usually live in separate languages:

1. **Totality you can trust.** Functions terminate by default. Anything that might not terminate says so in its type, and the guarantee covers everything a function calls.
2. **Proofs about programs.** Dependent types let you state and prove properties of your code in the language itself.
3. **Unison-style abilities.** Effects are tracked in types and implemented by handlers, in direct style without monads.
4. **Content-addressed caching.** Definitions are identified by a hash of their contents, so tests and proofs whose dependencies haven't changed are never re-run.

Proven code can be **extracted to JavaScript** as a normal ES module with TypeScript types, for use as a library inside a JS/TS application.

The name comes from a British wildflower. Stitchwort is meant to stitch small proven pieces together. File extension: `.sw`.

### Changes since draft 2

The second review recommended a targeted revision followed by implementation. These close the questions that must be settled before building the kernel, the elaborator and the extractor.

| Area | Draft 2 | Draft 3 |
|---|---|---|
| Totality statement | "A closed term whose type has no abilities" | Stated with an effect judgment `t: A ! ε`: building a partial closure is pure, calling it isn't |
| `Prop` elimination | "Fields are all erased" (which wrongly allowed hiding a type) | Lean's rule, stated over the constructor declaration: each field is a proof or appears in the result type's indices |
| Product rules | Unstated | `Prop` is impredicative. Effectful arrows are never in `Prop` |
| Explicit implicit arguments | `map [Nat] [Nat] f xs`, which clashes with list literals | `map [a := Nat] [b := Nat] f xs` |
| Records vs ability rows | "Abilities never contain a colon" | Decided by the top level of the braces only |
| `auto` | Only runs decision procedures | Uses supplied evidence, then hypotheses in scope, then decision procedures |
| Assumptions | Reported by a command | Exports must be assumption-free. Test results show their assumptions automatically |
| `State s` | Any `s` | `s` must be data-only, checked transitively |
| JS exports | "Pure, first-order" | An exportability check: concrete types with codecs, decidable preconditions, assumption-free |
| Numbers | `Int` division and `Float` unspecified | `Int` division is Euclidean, with truncating and flooring variants named. `Float` is outside the first extraction milestone |
| Caching | Elaboration keyed on dependency "interfaces" | Keyed on whole-declaration hashes. Module identity is logical, not a file path |
| Test harness | Rejection tests must fail | Must fail *with the expected error code*. Differential tests for extraction |

### Changes from draft 1 to draft 2

Draft 1 stated several guarantees more strongly than its rules justified. This draft makes them precise ([§3](#3-precise-guarantees)) and narrows the initial subset to what can actually be justified.

| Area | Draft 1 | Draft 2 |
|---|---|---|
| Universes | `Type: Type`, fix later | Numbered universes in the kernel from day one. `Type: Type` breaks termination, not just logic |
| Handler termination | Trusted if each clause resumes at most once | That rule has counterexamples. Draft 2: deep handlers, first-order operations, non-recursive clauses, recorded as a conjecture. Since replaced: a handler is translated into a fold over `Effect.Comp`, and the kernel's termination check covers it ([§8](#8-abilities-and-handlers)) |
| `withFuel` | Generic handler for `Partial` | Postponed. Explicit fuel arguments for now. `Partial` can't be handled by user code |
| Erasure | Open question | `Prop`-based, with restricted elimination |
| `auto` | "By computation" | Via a `Decidable` mechanism, which also produces the JS boundary checks |
| Division | `n / 0 = 0` or a proof, undecided | `/` needs a non-zero proof. `divideChecked` returns `Option` |
| Implicit arguments | `{a: Type}` | `[a: Type]`. `{a: Type}` was ambiguous with a one-field record type |
| JS integers | `number`, checked | `bigint`. Inputs that pass validation could produce outputs a `number` can't represent |
| JS `Option` | `a \| null` | `A \| undefined`, an optional property in a record's field (D582). `null` merged `None` and `Some None`; a nested `Option` stays tagged |
| JS inputs | Validated in place | Decoded into an owned copy first, then validated |
| Hashing | Body + dependency hashes | Whole declaration, recursive groups, nominal identity, explicit cache trust |
| Dependent records | Mixed with row-polymorphic records | Kept separate. Updates must re-establish dependent fields |

---

## Contents

1. [Goals and non-goals](#1-goals-and-non-goals)
2. [Core principles](#2-core-principles)
3. [Precise guarantees](#3-precise-guarantees)
4. [Language tour](#4-language-tour)
5. [Totality and partiality](#5-totality-and-partiality)
6. [Proofs, universes and erasure](#6-proofs-universes-and-erasure)
7. [Tests](#7-tests)
8. [Abilities and handlers](#8-abilities-and-handlers)
9. [Records](#9-records)
10. [Numbers](#10-numbers)
11. [Content hashing and caching](#11-content-hashing-and-caching)
12. [JavaScript extraction](#12-javascript-extraction)
13. [Soundness policy](#13-soundness-policy)
14. [Implementation](#14-implementation)
15. [Roadmap](#15-roadmap)
16. [Open questions](#16-open-questions)
17. [Related work](#17-related-work)
18. [Glossary](#18-glossary)

---

## 1. Goals and non-goals

### Goals

- **Explore ideas** and have fun. Prefer a small subset with precise guarantees over a broad one with vague ones.
- **Totality as a real guarantee.** A function with no `Partial` in its type terminates, along with everything it calls. See [§3](#3-precise-guarantees) for exactly what that covers.
- **Programming first, proving second.** It should feel like a pleasant functional language that *also* lets you prove things, not a proof assistant you happen to be able to program in.
- **Good everyday ergonomics:** structural records, pattern matching, implicit arguments, direct-style effects.
- **Never redo work.** Cache kernel checks, tests and generated code by content hash.
- **Proven JS libraries.** Extract pure functions to idiomatic JS/TS, with their guarantees intact at the boundary.
- **Runs in a browser.** A WASM playground for demos.

### Non-goals (for now)

- Performance, of the compiler or of generated code.
- Production readiness, stability or backwards compatibility.
- Unison's codebase-in-a-database model. Code lives in ordinary text files. We only borrow the hashing.
- A tactic language like Lean's. Proofs are written as ordinary terms.
- Package management, an LSP or editor integration.

---

## 2. Core principles

These are the rules the rest of the design must respect. If a feature conflicts with one of them, the feature changes.

1. **No `Partial`, no divergence.** In the assumption-free fragment, a computation whose type has no `Partial` terminates ([§3](#3-precise-guarantees) gives the exact statement). Calling a `Partial` function makes the caller `Partial`. No annotation, attribute or handler can quietly remove it.
2. **Checking never runs effects.** Types may *mention* effectful function types, but forming and comparing types only ever evaluates pure, total code.
3. **Every unchecked assumption is visible.** Escape hatches (`assume`, foreign functions declared total, unproven conjectures the checker relies on) are tracked. A command lists every assumption a definition depends on.
4. **A small trusted kernel.** The large, clever front-end produces simple core terms, and a small, separately written checker re-checks them. Only the kernel has to be right for proofs to be trustworthy.
5. **Identity is content.** A definition is identified by the hash of its elaborated declaration and its dependencies, not by its name. Nominal types are the one deliberate exception ([§11](#11-content-hashing-and-caching)).
6. **Guarantees hold at the boundary.** Extracted JS decodes and validates its inputs, and proven properties hold for every input that gets through.
7. **One meaning per word.** "Checked", "total", "erased" and "preserved" each have exactly one definition ([§3](#3-precise-guarantees)). When a feature would blur one, the feature waits.

---

## 3. Precise guarantees

This section defines what the rest of the document promises.

**Reference semantics.** The language's own definition of evaluation (the kernel's evaluator), independent of any backend. Statements about termination and results are about the reference semantics.

**Checked.** The kernel has accepted a definition's elaborated core declaration (its type and its body), either in this run or as recorded in the local cache ([§11](#11-content-hashing-and-caching)).

**Assumption-free.** A definition that doesn't depend, directly or indirectly, on any tracked assumption: `assume`, a foreign function declared total, a proof hole, or a conjecture the checker relies on. Today there are none to depend on: there's no `assume` yet, so every checked definition is assumption-free ([docs/core.md](docs/core.md#how-this-differs-from-designmd-today)), and handler termination is no longer a conjecture but follows from the kernel's checks ([§8](#8-abilities-and-handlers)). A command to list tracked assumptions (principle 3) will come with the first of them; the CLI has none today. "Assumption-free" is relative to the core theory, which includes the quotient axiom `Quot.sound`: that axiom doesn't block anything, and `stitchwort axioms <name>` lists it (and any later axiom) for a definition that depends on it, directly or through what it uses. An empty axiom report says no axiom is used; it doesn't say the term computes to data in the kernel.

**Effect judgment.** Internally, the type checker establishes judgments of the form

```
Γ ⊢ t : A ! ε
```

meaning "evaluating `t` produces a value of type `A`, and may perform the abilities in `ε`". The abilities that *evaluating* an expression may perform are different from the abilities mentioned *inside* its type:

```
() => spin 0          -- : () -> {Partial} Nat  ! {}         building the closure is pure
(() => spin 0) ()     -- : Nat                  ! {Partial}  calling it is partial
```

**Total.** If `⊢ t : A ! {}` is checked and assumption-free, with `t` closed, then evaluating `t` reaches a value in finitely many steps. Here "evaluating" means running, with proofs and types erased ([§6](#6-proofs-universes-and-erasure)). The checker's evaluator, which doesn't erase, also terminates, but a closed term that moves data along an opaque equality proof (one made by `Quot.sound` or `Quot.ind`) may stop at a term that isn't a value. `A` may itself contain function types with abilities: those apply when the function is called, not when `t` is evaluated. How this extends to other cases:

| Case | What's guaranteed |
|---|---|
| Pure function `f: A -> B` | Applying it to any value of `A` terminates. |
| Function returning a partial closure, `mk: Nat -> (() -> {Partial} Nat)` | Calling `mk` terminates (`mk 3: … ! {}`). Calling the closure it returns is not covered. |
| Open ability row, `g: A -> {e} B` | Terminates once every ability in `e` is handled by an admissible handler ([§8](#8-abilities-and-handlers)). The handled computation is then covered. |
| `Abort` | May stop without producing a `B`. Once handled (into `Option B`), covered. |
| `IO` and host-provided operations | Trusted contracts. They may block (waiting for input or the network). The guarantee covers the computation between them, not the operations themselves. |
| Depends on assumptions | The guarantee holds only if the listed assumptions are true. |

Total is about running a program, not about what the type checker's evaluator computes. One function is total but not *kernel-executable*: `Float.toText`, which each runtime supplies (JS's `String(x)`) and the checker never computes ([docs/core.md](docs/core.md#float)). `Float.toText 0.5` reaches a `Text` when run, but in the checker it stays as written, and so does anything computed from the text, so a `test` about it doesn't run there.

"Finitely many steps" doesn't mean "quickly". Tools that run code (tests, the type checker's evaluator, the playground) have resource budgets. Running out of budget is reported as **inconclusive**, never as pass or fail.

**Conditional results are labelled automatically.** Anything that reports success (a test, a theorem, an export) shows the assumptions it depends on, without the user having to run a separate command. Exports are refused outright if they depend on assumptions ([§12](#12-javascript-extraction)).

**Proved.** If a checked, assumption-free theorem `p: P` exists, then `P` holds, assuming the kernel is correct.

**Erased.** A value is erased if it's a type or a proof (its type is in `Prop`, [§6](#6-proofs-universes-and-erasure)). Erased values don't exist at runtime, and the kernel's elimination rules ensure runtime results never depend on them.

**Preserved at the JS boundary.** If decoding and validation of an exported function's inputs succeed, the function returns the encoding of the Stitchwort result for the decoded inputs. This trusts the code generator, the encoders and decoders, the JS engine, and that there is enough memory and stack ([§12](#12-javascript-extraction)).

---

## 4. Language tour

The syntax is whitespace-sensitive and ML/Lean-like. Everything here is a sketch and open to change. Constructor names start with an uppercase letter, which is how patterns tell constructors apart from variables.

### Brackets

| Brackets | Meaning | Example |
|---|---|---|
| `( )` | grouping, explicit arguments | `(xs: List a) -> …` |
| `[x: A]` in a type | implicit argument binder: the compiler fills it in | `[a: Type] -> List a -> Nat` |
| `[auto x: P]` in a type | implicit proof the compiler finds ([§6](#6-proofs-universes-and-erasure)) | `[auto ok: i < length xs]` |
| `[x := e]` in an expression | supplying an implicit argument explicitly, by name | `map [a := Nat] [b := Nat] f xs` |
| `[e, …]` in an expression | list literal | `[1, 2, 3]`, `[x]`, `[]` |
| `{ }` with `name: Type` fields | record types | `{ name: Text, age: Nat }` |
| `{ }` right after an arrow | ability rows | `Nat -> {State Nat} Nat` |

**Square brackets.** In a type, `[` always starts an implicit binder. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list literal, so `length [1]` and `get [10] 0` mean what they look like. The `:=` also keeps `[a := b]` distinct from `[a = b]`, a one-element list containing an equality.

**Curly braces.** Record types and ability rows are told apart by the *top level* of the braces, not by whether a colon appears anywhere inside:

- If the top-level entries have the form `name: Type`, it's a record type.
- Otherwise it's an ability row, whose entries are abilities applied to arguments. Those arguments may themselves contain record types: `Nat -> {State { count: Nat }} Nat` is an ability row containing `State` applied to a record type.
- `{}` is always the empty record type. An empty ability row is never written: a pure arrow has no braces.

These rules get golden parser tests before anything is built on them, including nested and empty cases.

### Data types and pattern matching

```
type Shape =
  | Square (side: Nat)
  | Rect (width: Nat) (height: Nat)

def area: Shape -> Nat
  | Square s => s * s
  | Rect w h => w * h

-- Lowercase type variables in signatures are bound implicitly.
-- Equivalent to: def map [a: Type] [b: Type] (f: a -> b): List a -> List b
def map (f: a -> b): List a -> List b
  | []        => []
  | x :: xs   => f x :: map f xs

def doubled := map (x => x * 2) [1, 2, 3]                 -- a and b inferred
def doubled := map [a := Nat] [b := Nat] (x => x * 2) [1, 2, 3]   -- supplied by name
```

**`==` on a declared data type is derived automatically**, with no `deriving` clause: when `Shape` is declared, the compiler also derives a `DecEq` instance for it, from a proved decision procedure for `=` (named so that source can't refer to it), which `==` finds (docs/proposals/interfaces.md §5.11). It's what one expects of `==` on plain data, a module's own `instance Shape.instDecEq: DecEq Shape` replaces it, and a type that can't have one says why when `==` is used. It's derived when every field is data that can be compared (of the type itself, or of a type with `DecEq`, including through the type's parameters: `Tree a` asks for `DecEq a`), or a proof of an equation in a type with `DecEq`, which isn't compared. Function fields, other proof fields and types defined together get none (`E-INSTANCE-NONE`, with a note). It's generated eagerly, at the declaration, rather than on first use: that's simpler, and costs a few milliseconds per type (`crates/elab/src/derive.rs`).

### Records

```
type Person = { name: Text, age: Nat }

def alice: Person := { name = "Alice", age = 30 }

def birthday (p: Person): Person := { p | age = p.age + 1 }

-- Works on any record that has a `name` field
def greet (x: { name: Text | r }): Text := "Hello, " ++ x.name
```

### Totality

```
-- Structural recursion: accepted automatically
def length: List a -> Nat
  | []      => 0
  | _ :: xs => 1 + length xs

-- Not structural: name a measure that decreases.
-- `b@(Succ _)` names the argument and records that it isn't zero,
-- which `%` requires.
def gcd: Nat -> Nat -> Nat
  | a, 0          => a
  | a, b@(Succ _) => gcd b (a % b)
  decreasing b

-- Opt out: partiality is an ability, visible in the type
def collatz: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatz (if even n then n / 2 else 3 * n + 1)
```

### Proofs

```
theorem appendLength: (xs ys: List a) -> length (xs ++ ys) = length xs + length ys
  | [],      ys => rfl
  | x :: xs, ys => Eq.cong Succ (appendLength xs ys)

-- The proof that the index is in range is found by `auto`
def get (xs: List a) (i: Nat) [auto ok: i < length xs]: a := ...

def third := get [10, 20, 30] 2      -- fine: 2 < 3 is decided at compile time
def oops  := get [10, 20, 30] 5      -- error: 5 < 3 is false
```

### Data bundled with its guarantees

```
def IsSorted: List Nat -> Prop := ...

-- `sorted` is a proof, so it's erased: at runtime this is just a List
type SortedList = { items: List Nat, sorted: IsSorted items }

def insert (n: Nat) (s: SortedList): SortedList :=
  { items  = insertList n s.items
  , sorted = insertPreservesSorted n s.items s.sorted }
```

### Abilities

```
ability State s where
  get: () -> {State s} s
  put: s -> {State s} ()

def tick(): {State Nat} Nat :=
  let n := get()
  put (n + 1)
  n
```

### Tests

```
test "reverse twice" :=
  reverse (reverse [1, 2, 3]) == [1, 2, 3]
```

```
$ stitchwort test
  ✓ reverse twice          cached
  ✓ tick twice             ran (3ms)     ← tick's hash changed
  ✓ appendLength           proof cached
```

### JS export

```
export def applyDiscount: (pct: Nat) -> [auto ok: pct <= 100] -> Price -> Price
```

```ts
// generated .d.ts
export function applyDiscount(pct: bigint, price: Price): Price;
```

---

## 5. Totality and partiality

### What we want to avoid

Lean 4 checks termination to keep its *logic* consistent, and deliberately separates that from execution. A `partial def` is an opaque constant to the kernel: "Functions marked `partial` are treated as opaque constants by the kernel and are neither unfolded nor reduced" ([Lean reference: recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)). Calls to partial definitions don't propagate any divergence effect, so ordinary definitions can call them:

```lean
partial def spin (n: Nat): Nat := spin n
def innocent (n: Nat): Nat := spin n + 1   -- accepted as an ordinary def
```

This matches the documented behaviour, though this exact snippet hasn't been run. An ordinary Lean function type such as `Nat → Nat` doesn't certify that its compiled implementation terminates. Stitchwort aims for a stronger link between what the types say and what runs.

### Partiality is in the type

`Partial` appears in function types and spreads to callers. It's written in
a row, like an ability, but it isn't one: it has no operations, and it
makes the result an `Effect.Delay` (a computation that may not finish) rather than
an `Effect.Comp`. Stage 1 is implemented ([docs/proposals/partial.md](docs/proposals/partial.md),
"As built"):

```
def spin (n: Nat): {Partial} Nat := spin n

-- type error: calls spin, which uses Partial
def innocent (n: Nat): Nat := spin n + 1

-- OK: partiality is visible
def innocent (n: Nat): {Partial} Nat := spin n + 1
```

### Rules

1. A recursive definition must pass the termination checker, or have `Partial` in its type.
2. Calling a function whose type has `Partial` adds `Partial` to the caller's abilities.
3. Pattern matches must be **exhaustive**. A missing case is a compile-time error.
4. **Only the runtime handles `Partial`**, at program entry (`main`) and when `stitchwort test` runs a test. `Partial` has no operations, and no handler may have it in the computation it handles, nor may it stand for a row variable. Otherwise a handler that acknowledges every step could turn an infinite computation into a supposedly total one.
5. Tests may run `Partial` code ([§7](#7-tests)): `stitchwort test` runs them, as `stitchwort run` runs a partial `main`. A test is a runtime check, not a proof, so this removes nothing from rule 4 or principle 1: no total code can observe the result.
6. Foreign functions that might not return must declare `Partial`. Declaring one total is an `assume`, which is tracked.
7. The type checker never evaluates `Partial` code (principle 2).

### Termination checking

Checking is deliberately conservative. It may reject total functions, but it must never accept a non-terminating one.

- **POC:** structural recursion, checked by size change ([docs/core.md](docs/core.md#definitions)). Each recursive call must pass, in each position, a sub-part of a pattern-matched argument, the argument itself, or something unknown, and some argument must get smaller however the calls are repeated: so lexicographic recursion (Ackermann's function) and swapped arguments are accepted. Definitions can be written in any order, and definitions that call each other are checked as a group, with every call between any two of them in the analysis ([proposal](docs/proposals/mutual-recursion.md)). Data types that refer to each other (a tree and a forest) are checked as a group too, with positivity across the group, and a field of a sibling type matched out of an argument is smaller than it.
- **Next:** `decreasing <measure>` clauses for well-founded recursion. The compiler tries to prove the measure decreases with simple arithmetic and asks for a proof if it can't.
- **Later:** handling recursion through higher-order functions (e.g. `map size children` on a rose tree), probably by automatically attaching "this element is in the list" facts, as recent Lean versions do.

When termination checking fails, the error should say *which call* failed and *what it couldn't show*, and suggest `decreasing` or `{Partial}`.

### Fuel

For now, bounded versions of partial algorithms take an explicit fuel argument. They terminate by structural recursion on the fuel, so no special support is needed:

```
def collatzFuel: Nat -> Nat -> Option Nat
  | 0,         _ => None
  | Succ fuel, 1 => Some 0
  | Succ fuel, n => map (+ 1) (collatzFuel fuel (next n))
```

A generic `withFuel: Nat -> (() -> {Partial | e} a) -> {e} Option a`, which bounds *any* partial computation, is attractive but postponed. It needs:

- **Ticks in the core semantics.** Every unbounded recursion must pass through a "tick", and the kernel must check this. It can't be optional instrumentation added by the front-end.
- **No opaque divergence.** A foreign function that loops internally can't be interrupted between ticks, so foreign `Partial` must be excluded or treated differently.
- **Specified fuel semantics.** Counting recursive calls and counting evaluation steps give different results, and optimisations must preserve whichever is chosen.

---

## 6. Proofs, universes and erasure

### Proofs

- **Propositions are types; proofs are values.** `xs ++ [] = xs` is a type, and a value of that type is a proof.
- **`theorem`** is a definition whose type is a proposition (in `Prop`). It's always erased at runtime and must be total and pure.
- **Equality** is a built-in proposition `a = b` with `rfl: a = a`, plus library functions `Eq.cong`, `Eq.sym` and `Eq.trans`. Equational proofs use `calc` chains and `rewrite p in t`, both built (docs/syntax.md); `rewrite` is elaborator syntax, not a library function, and elaborates to `J` ([calc-rewrite.md](docs/proposals/calc-rewrite.md)).
- **Proof by computation.** Types are compared by evaluating them, so `rfl` proves anything that holds by just computing both sides (`2 + 2 = 4`, `List.length [1, 2] = 2`).
- **No tactics.** Proofs are ordinary terms, written by pattern matching and recursion. `calc` writes a chain of `=`, `<=` and `<` steps one per line (docs/syntax.md); it elaborates to `Eq.trans`, `J` and `Nat.leTrans` terms. `rewrite` finds the motive of `J` by looking for the equation's left side in the goal.

Conventions that make proofs go through by computation should be documented. For example, `+` on `Nat` recurses on its *first* argument, so `Succ m + n` reduces to `Succ (m + n)`.

### Universes

```
Prop:   Type 0
Type 0: Type 1
Type 1: Type 2
…
```

- `Type` on its own means `Type 0`, where ordinary data lives.
- The kernel checks universe levels **from the first milestone**. `Type: Type` was rejected because it allows paradoxes (Girard's) that produce non-terminating terms without any recursion, which would break principle 1, not just the logic.
- **No universe polymorphism at first.** Each data type is declared at a fixed level, so `List` holds `Type 0` values. Universe polymorphism and inference come later, and are mostly an elaboration feature.

### Which universe a function type lives in

Having numbered universes doesn't settle where function types live. The rules:

| Function type | Lives in | Note |
|---|---|---|
| `(x: A) -> B`, pure, `B: Prop` | `Prop` | Whatever `A`'s universe. This is **impredicativity**, as in Lean and Rocq: "for every `x: A`, `B x` holds" is itself a proposition |
| `(x: A) -> B`, pure, `A: Type i`, `B: Type j` | `Type (max i j)` | `Prop` counts as level 0 here |
| `(x: A) -> {ε} B`, with a non-empty ability row | `Type (max i j)`, **never** `Prop` | Even when `B` is a proposition |

The last rule matters once abilities exist. In

```
def loggedProof: () -> {IO} True
```

the function is runtime data, not an erasable proof: calling it performs IO, and only the `True` it returns is erased. Treating it as a proposition would erase the IO.

### Erasure via `Prop`

A value is erased if its type is in `Prop`. `sorted: IsSorted items` is erased because `IsSorted items: Prop`, not because of its name or where it came from. Types are erased too.

**The restriction that makes this safe:** runtime results must never depend on *which* proof was given, or on data hidden inside a proof. So pattern matching on a proof may only produce something outside `Prop` when the proposition passes this check, which is Lean's rule ("subsingleton elimination"; Rocq's is similar).

The check reads the **inductive declaration itself**, distinguishing its parameters, its indices and each constructor's fields. A proposition may be eliminated into any universe when:

1. it has **at most one constructor**, and
2. every **field** of that constructor (an argument that isn't one of the type's parameters) is either
   - a **proof** (its type is in `Prop`), or
   - a variable that **appears among the indices of the constructor's result type**, so it's determined by the type and carries no hidden information.

Otherwise, matching on it can only produce another proof.

**With indices, as built.** The rule is read over the declaration as above, with two additions and one omission ([indexed families](docs/proposals/indexed-families.md), §6.4). A match whose every branch is impossible may produce anything, since it's never reached (`Le (Succ n) 0 -> Nat`). A proposition matched into data also has its impossible branches counted, so a proposition with two constructors where only one is possible at that index still needs the one-constructor test on the *declaration* (D140). The "appears in an index" clause (second bullet above) is **deferred**: it isn't adopted yet, so a field that the proof's indices determine still disqualifies (`type IsSucc: Nat -> Prop = | MkIsSucc: IsSucc (Succ n)` can't be read into `Nat`: `E-PROP-ELIM`). It can be added later without making an accepted program wrong.

The check is over the declaration. It must **not** be implemented by asking "would the compiler erase this field?", because types are erased but can still carry information:

```
type HiddenType: Prop =
  | HideType (a: Type)

def reveal: HiddenType -> Type      -- rejected: `a` is a type, not a proof,
  | HideType a => a          -- and it doesn't appear in an index
```

| Proposition | Can be matched on to produce data? | Why |
|---|---|---|
| `a = b` (constructor `rfl: a = a`) | Yes | No fields. The `a` in `rfl` is a parameter or index, not a field. Needed for transport (rewriting a value's type along an equality) |
| `False` | Yes | No constructors. Needed for ruling out impossible cases (`Void.absurd`) |
| `p ∧ q` | Yes | One constructor, whose fields are proofs |
| `p ∨ q` | **No** | Two constructors: the result could depend on which side was proved |
| `∃ x, p x` | **No** | The witness `x` is data that doesn't appear in an index |
| `HiddenType` | **No** | The field `a: Type` is neither a proof nor an index |

The kernel implements this rule and nothing looser. Each "No" row is a "must reject" test, paired with an accepted test for a nearby "Yes" row ([§13](#13-soundness-policy)). Definitional proof irrelevance (treating any two proofs of the same proposition as equal during type checking) isn't needed for the POC.

Data indices like a vector's length are **not** erased, because they're data, not proofs: a constructor's forced implicit fields (`n` in `VCons`) are stored, while its proof fields are erased even in a family that is data (`Certified n`). That costs some runtime space and work (the field is computed from whatever the elaborator inferred for it, so `fromList` should pass the length down rather than recompute it), which is acceptable since performance isn't a goal. A more general relevance system (Idris 2-style usage annotations) can come later if needed.

### Four separate questions about an argument

These are independent, and the design keeps them so:

| Question | Controlled by |
|---|---|
| Does the caller write it? | Explicit `( )` vs implicit `[ ]` |
| How is it found? | Unification for `[x: A]`. A decision procedure for `[auto x: P]` |
| Does it exist at runtime? | Erased if and only if its type is in `Prop`, or it's a type |
| How often may it be used at runtime? | Unrestricted. (Continuations may later need "at most once" for JS; see [§8](#8-abilities-and-handlers)) |

In particular, an implicit argument isn't automatically erased (`[n: Nat]` exists at runtime), and `auto` doesn't mean erased either.

### `auto` and `Decidable`

`[auto ok: p]` asks the compiler to find a proof of `p`. Evaluating `2 < 3` to `true` doesn't by itself produce a proof, so `auto` uses decision procedures, values of this type:

```
type Decidable (p: Prop): Type =
  | Yes (proof: p)
  | No  (refutation: Not p)
```

`Decidable p` lives in `Type`, not `Prop`: whether the answer is `Yes` or `No` is runtime data. Only the proof inside each branch is erased.

To fill in `[auto ok: p]`, the compiler tries, in order:

1. **Evidence supplied explicitly**: `[ok := myProof]`.
2. **A hypothesis already in scope** whose type matches `p`, e.g. the `h` from `if h: d != 0 then …`. This is simple matching against the local context, not general proof search.
3. **A registered decision procedure** for `p`, evaluated at compile time.

Possible outcomes, each with its own error message:

| Outcome | Result |
|---|---|
| Evidence found, or the decision procedure says `Yes proof` | Uses that proof |
| The decision procedure says `No` | Error: `p` is false |
| The decision procedure is stuck, because its inputs aren't known at compile time | Error: supply a proof, or establish it with a branch (`if h: i < length xs then … else …`) |
| No decision procedure is registered for `p` | Error: no way to decide `p` |
| The budget ran out | Inconclusive: try a larger budget |

**The same decision procedure has two uses.** It can run during elaboration when its inputs are known well enough, or be compiled into a runtime check at the JS boundary ([§12](#12-javascript-extraction)). A predicate can have a perfectly good decision procedure that's stuck at compile time on symbolic inputs. That's exactly the case where a runtime check is useful.

### Dependent pattern matching

Pattern matching in proofs requires the compiler to learn facts about types in each branch. In full generality this is one of the hardest parts of any dependently-typed language. **For the POC, patterns are kept simple:** constructors (nested), variables, numbers and `()`, compiled into a tree of simple `case` expressions. Equations are tried top to bottom. Indexed families add one thing, unification of the constructor's indices with the scrutinee's (the kernel's `case` rule, `docs/core.md`): a branch where that finds a conflict is impossible and needs no arm, a stuck one is `E-INDEX-STUCK`, and an arm that can never match is the warning `W-UNREACHABLE`. There's no other overlap or redundancy warning yet.

### Effects and dependent types

The rule (principle 2) is about **executing** effects, not mentioning them:

- `f: (n: Nat) -> {IO} Vec Nat n` is fine. The result type `Vec Nat n` is pure, even though calling `f` performs IO.
- A type expression that would itself *perform* an operation (e.g. `Vec Nat (readNat())`) is rejected. During type checking, effectful applications never reduce.
- When an effect's result is later used as an index (`let n = readNat()` and then `Vec Nat n`), `n` is just a variable as far as the type is concerned. The precise rules for sequencing effectful code with dependent types are an open question ([§16](#16-open-questions)).

### Running vs comparing

The type checker and the program runner share an evaluator, but use it with **different policies**:

| | Running a program | Comparing types |
|---|---|---|
| Goal | Reach a value | Reach a normal form, so two types can be compared |
| Goes inside `x => …`? | No | Yes |
| Reduces effectful applications (including `Partial`)? | Yes, via handlers | **Never**. They stay as stuck terms |
| Budget | Per run | Per check. Running out is inconclusive |

The core typing rules will state exactly which terms the comparison is allowed to reduce, since that's what keeps type checking terminating once partial closures exist.

---

## 7. Tests

A test is a named, closed `Bool` expression that must be checked and pure. It's a **runtime check**, like a unit test in other languages, not a proof: proofs are theorems ([§6](#6-proofs-universes-and-erasure)).

```
test "tick twice" :=
  runState 0 (() => tick(); tick()) == (1, 2)
```

`stitchwort test` runs it, on the fast runtime by default and on the reference evaluator with `--reference`. Results are cached by content hash, as theorems are ([§11](#11-content-hashing-and-caching)).

- **Outcomes:** pass or fail; or no result, when a run exceeds the runner's resource budget, which is never cached.
- **Tests may run `Partial` code** (D1183), with nothing extra to write: a test whose expression is partial is a partial computation of a `Bool`, and `stitchwort test` steps it as `stitchwort run` steps a partial `main`, with no tick limit. A test that never finishes is a bug in the test or the code, and whoever runs it stops it.
- **Only `stitchwort test`, and the playground's Tests tab, run tests.** The type checker, the editor's language server and the playground's checks never do, so a test that loops can't hang them (principle 2).
- **Effectful code is tested via pure handlers**, like `runState` above.
- **Assumptions are to be shown with the result**, once there are tracked assumptions ([§3](#3-precise-guarantees)): a test that depends on one will report as conditional. None exists today, so no result is conditional. `tick twice` goes through `runState`, a handler, and handlers no longer rest on a conjecture: `runState` is a fold over `Effect.Comp` that the kernel has checked terminates ([§8](#8-abilities-and-handlers)). So it reports like any other test:

  ```
  ✓ reverse twice          ran
  ✓ tick twice             ran
  ```

### Property tests (later)

`forall xs. reverse (reverse xs) == xs`, checked on random inputs, sits between tests and theorems. When added:

- The cache key includes the generator, sample count, size schedule, seed and configuration, not just the seed.
- "Replay these known samples" and "search for new counterexamples" are separate commands.
- The UI presents a passing property test as **evidence about the sampled cases**, never as a theorem.

---

## 8. Abilities and handlers

Abilities follow Unison's design, which comes from Frank.

- **Direct style.** Effectful code reads like ordinary code (`let n = get()`), with no `do`-notation or monads.
- **Ability rows on arrows.** `a -> {State s, IO} b`. A plain arrow `a -> b` means pure *and* total.
- **Ability polymorphism with row variables.** `{State s | e}` means "State, plus whatever else `e` is".

### Deep handlers

Handlers are **deep**: the continuation `k` already includes the handler, so a clause never needs to call the handler again. That makes a handler a *fold* over the tree of operations a computation performs:

```
def runState [auto d: IsData s] (init: s) (prog: () -> {State s | e} a): {e} (a, s) :=
  let run :=
    handle prog() with
      | return x     => s => (x, s)
      | get(), k => s => k s s
      | put s', k => _ => k() s'
  run init
```

Each clause returns a function waiting for the current state. `k s` resumes the computation with result `s`, giving back another such function, which is then applied to the state.

The `IsData s` constraint is explained under rule 2 below.

### When handlers are trusted to terminate

Draft 1 proposed trusting any handler that resumes `k` at most once. **That rule is wrong.** These two counterexamples are now in the "must reject" suite.

*The handler restarts the computation instead of resuming it:*

```
ability Ping where
  ping: () -> {Ping} ()

def bad (prog: () -> {Ping} a): a :=
  handle prog() with
    | return x    => x
    | ping(), k  => bad prog     -- never resumes k, loops forever

bad (() => ping())
```

*Landin's knot: storing a function that reads itself back:*

```
ability Cell where
  read : () -> {Cell} (() -> {Cell} ())
  write: (() -> {Cell} ()) -> {Cell} ()

def knot: () -> {Cell} ()
  | () =>
    let f := () => (read()) ()
    write f
    f()           -- f reads f and calls it, forever
```

Each continuation here is resumed exactly once. The recursion comes from the stored function, not from the handler. Koka's design makes the same point: higher-order mutable state can cause divergence that a check for syntactic recursion can't see.

**POC rule (draft 2, superseded).** The rule and conjecture below were draft 2's plan. They are kept for the reasoning; what is built is under *How handlers terminate today*, after them. `IsData` was never built. A handler is admissible when:

1. **It's deep, and its clauses aren't recursive.** A clause can't call the handler or any function that leads back to it. The only way to continue is `k`. This rejects `Ping`.
2. **Its ability's operations are data-only.** Operation arguments and results can't contain functions, anywhere. This rejects `Cell`. It's checked **transitively, after type parameters are filled in**, not just by looking for `->` in the operation's signature, because a function can hide inside a constructor or record. So `State Nat` is fine, but `State (List (Nat -> Nat))` and `State { f: Nat -> Nat }` are rejected. For parameterised abilities like `State s`, the handler must require `IsData s`, a property of types that the compiler decides by looking through their definitions. Without that, `runState` could be used with function-valued state and reintroduce Landin's knot.
3. **Its clauses are total and pure** apart from the outer row `e`.
4. **It isn't for `Partial`** ([§5](#5-totality-and-partiality)).

**Conjecture (draft 2).** An admissible handler terminates, *whether or not* it resumes `k` more than once. The argument has two parts:

1. **The computation:** under these typing and termination rules, an effectful computation corresponds to a *well-founded* tree of operations. Every path through it is finite, and data-only operations can't smuggle in recursion.
2. **The handling:** an admissible deep handler is a fold over such a tree with total clauses, so it doesn't introduce divergence of its own.

Splitting it this way avoids assuming "the computation is total" before totality has been defined for open, effectful computations, and shows that the restrictions on operations belong to part 1. Draft 2 planned to track it as an assumption until it was written up. It was never written up, and the implementation made it unnecessary.

**How handlers terminate today.** Abilities are translated into ordinary data before the kernel sees them ([docs/core.md](docs/core.md#abilities); [abilities.md](docs/proposals/abilities.md), Part 2, option B). An effectful computation is a value of the prelude's `Effect.Comp`, a strictly positive tree of operations, and `handle` becomes `Effect.foldComp` (`crates/elab/src/effects.rs`, module comment; `crates/elab/src/std/core/Effect.sw`, `Effect.foldComp`). So the parts of the conjecture become checks the kernel already makes:

1. **The computation** is a `Comp` value. It's well founded because the type is strictly positive (the positivity check).
2. **The handling** is a structural fold: the termination checker accepts recursion on `rest y` for a recursive function field `rest` ([docs/core.md](docs/core.md#abilities); `crates/core/src/termination.rs`, module comment). A clause that handles the computation again, as `Ping` does, rebuilds the parameter, which isn't smaller, and is refused with `E-TERMINATION` (`examples/soundness/ping-handler.sw`). Landin's knot is refused: written as an `ability`, by the elaborator (`E-ABILITY`, `examples/soundness/cell-ability.sw`); written by hand against `Comp`, by positivity (`cell-operation.sw`) or termination (`cell-result.sw`). There's no `IsData` rule: the kernel's own checks on the translation take its place ([abilities.md](docs/proposals/abilities.md), "`IsData` is replaced by the kernel's own checks").

Nothing here is a tracked assumption. What is trusted instead:

- **The kernel's termination rule for function fields.** abilities.md says, under "The termination rule": "Not yet verified: a soundness proof for these rules in this kernel." Its soundness argument assumes every data type's values are well founded (`termination.rs`, module comment). Like the rest of the kernel, this is trusted and covered by must-reject tests, not proved ([§13](#13-soundness-policy)).
- **That the translation is faithful.** The kernel checks that the *translated* program terminates. That the translation matches the semantics of abilities.md Part 1 is the elaborator's obligation, tested by comparing behaviour ([abilities.md](docs/proposals/abilities.md), "Changes since draft 1"; the semantic tests in `examples/accept/abilities.sw`). A wrong translation could give a program the wrong meaning. It can't make a total program loop, because everything it generates is re-checked by the kernel (`effects.rs`, module comment).

`Partial` is outside all this: a partial computation is an `Effect.Delay`, which only the runtime runs. A handler around partial code is partial too, so it can't make looping code total (`E-PARTIAL`, `examples/soundness/partial-handled-total.sw`; [docs/proposals/partial-handlers.md](docs/proposals/partial-handlers.md)).

**Operational semantics to pin down before milestone 7.** Answered in [`docs/proposals/abilities.md`](docs/proposals/abilities.md), which also chooses an implementation: effects are translated into an inductive tree type, so the kernel's positivity and termination checks prove that handlers terminate, replacing the conjecture above. `Partial` is a separate open proposal, [`docs/proposals/partial.md`](docs/proposals/partial.md). "Deep" isn't a complete specification. Before implementing handlers, the core rules must say:

- whether a clause runs *inside* or *outside* the handler it belongs to (i.e. what happens if a clause itself performs an operation of the ability being handled);
- how operations the handler doesn't handle are forwarded to outer handlers;
- the exact type of the continuation `k`.

Resuming more than once doesn't by itself cause divergence. Exploring both branches of a finite tree terminates.

**"At most once" is a separate concern.** Compiling handlers to JS generators ([§12](#12-javascript-extraction)) requires each continuation to be resumed at most once *at runtime*, including through closures and helper functions, so counting occurrences of `k` in the source isn't enough. This only matters when handlers are extracted to JS, which comes after the first extraction milestone. It's not part of the termination argument.

### Built-in abilities

| Ability | Purpose |
|---|---|
| `Partial` | Might not terminate ([§5](#5-totality-and-partiality)). Not an ability with operations but a mode: a partial computation is an `Effect.Delay`, which only the runtime runs (`stitchwort run`, the playground), one recursive call (tick) at a time ([docs/proposals/partial.md](docs/proposals/partial.md)) |
| `IO` | The console (`IO.print`, `IO.readLine`, `IO.readAll`). Performed for real only by the runtime, at `main`; Stitchwort handlers may interpret it as data, as the prelude's `IO.simulate` does ([docs/proposals/text-and-io.md](docs/proposals/text-and-io.md)). A trusted contract that may block |
| `Abort` | Stop early. Handled into `Option` or `Either` |
| `State s` | State, handled purely. `s` must be data-only |

---

## 9. Records

Records come in two kinds, kept separate at first. The plan, in stages, is [docs/proposals/records.md](docs/proposals/records.md); stage 1, declared records, is built ([as built](docs/proposals/records.md#65-as-built-stage-1), [syntax](docs/syntax.md#records)).

### Declared records (built)

- **Nominal.** `type Person = { name: Text, age: Nat }` declares a new type, as `type … = | …` does: `Person` and a `Pet` with the same fields are different types. It's a data type with one constructor and a projection per field, so the kernel needs nothing new. A nickname for a record type is an ordinary definition (`Point: Type; Point = …`, once anonymous record types exist).
- **Literals** `{ name = "A", age = 3 }` need an expected type; **access** `p.name` needs `p`'s type known; **updates** `{ p | age = p.age + 1 }`; **patterns** `{ name, .. }`. In a computation, field expressions run in the order written.
- **`==`** is derived only when a checked decision for the whole record can be built; otherwise the user writes one.
- In JS, a plain object without a tag ([§12](#12-javascript-extraction)).

### Row-polymorphic records (planned)

- **Structural.** `{ name: Text, age: Nat }` is a type in its own right, the same type whatever order its fields are written in.
- **Row polymorphic.** `{ name: Text | r }` accepts any record with at least a `name` field.
- **Conveniences:** update syntax `{ p | age = p.age + 1 }`, field punning `{ name, age }`, and `.age` as an accessor function.
- **No dependencies between fields.**

### Dependent records

- **Closed and ordered.** Later fields may refer to earlier ones: `{ items: List Nat, sorted: IsSorted items }`. Field order matters, and there's no row variable.
- **Updates must re-establish dependent fields.** For `s: SortedList`, `{ s | items = [2, 1] }` is a type error, because `s.sorted` proves something about the *old* `items`. An update that changes a field must also supply every later field whose type depends on it:

  ```
  { s | items = xs', sorted = proofAbout xs' }
  ```
- **Proof fields are erased** at runtime. Passed in from JS, each is re-established by a decision procedure.
- These are declared records: anonymous and row-polymorphic records don't have dependent fields.

### Nominal types

- **Data types (`type … = | …`) and declared records are nominal**: two declarations with the same constructors, or fields, are still different types. (Their TypeScript aliases are structural, as all TS object types are.)
- To keep IDs apart, use single-constructor data types or records:

  ```
  type UserId  = UserId Nat
  type OrderId = { order: Nat }
  ```

---

## 10. Numbers

- `Nat` and `Int` are arbitrary-precision integers.
- **Division and remainder need a non-zero divisor.** `/` and `%` take an implicit proof `[auto ok: d != 0]`. For literal divisors (`n / 2`) or divisors matched as `Succ _`, the compiler finds it automatically. For unknown divisors there are two routes:
  - establish the fact with a branch (`if h: d != 0 then n / d else …`), or
  - use `divideChecked: Nat -> Nat -> Option Nat` (and `remainderChecked`).

  The laws of `/` and `%` (e.g. `a % b < b` when `b != 0`) are part of the standard library, since proofs like `gcd`'s termination depend on them.
- **`Nat` subtraction stops at zero** (`3 - 5 = 0`), documented prominently, with `subtractChecked: Nat -> Nat -> Option Nat` as the alternative. Code that needs negative results should use `Int`.
- **`Int` division is Euclidean.** `/` and `%` on `Int` are `Int.div` and `Int.mod`: `a = d * (a / d) + a % d` with `0 <= a % d < |d|` for every non-zero divisor, so `(-18) % 100 = 82` and `(-7) / 3 = -3`. The truncating and flooring variants are separately named, with the same `[auto ok: d != 0]` argument: `Int.tdiv` and `Int.tmod` round toward zero, and `Int.fdiv` and `Int.fmod` round toward negative infinity. The laws are in the standard library (`Int.divAddMod`, `Int.modNonneg`, `Int.modLtAbs`). Extracted JS uses `BigInt`'s truncating operators with a one-step correction, so it gives the same results.
- **Literals are typed by context.** A numeral is a `Nat` unless an expected type, another operand or a minus sign makes it an `Int`; a negative literal such as `-5` is always an `Int`. So `let x: Int := 5` is an `Int`, while `let n := 5` is a `Nat`.
- **The `3 - 5` trap.** `Nat` subtraction stops at zero, so `let d := 3 - 5` with no type anywhere is a `Nat` and `d` is `0`; write `let d: Int := 3 - 5` to get `-2`. A later `d + i` with `i: Int` is a type error, because the binding keeps its `Nat` type.
- **`Float` is unspecified for now**, and stays out of the first extraction milestone. Defining its semantics (IEEE 754 doubles, and what that means for equality and proofs) is a separate piece of work.
- **Fixed-size numbers** (`U32` etc.) come later. Their mathematical meaning comes first, e.g. `U32` as a `Nat` below 2³² with explicitly wrapping operations, so their laws can be proved. Efficient machine representations come after that.

---

## 11. Content hashing and caching

Because the language is pure and total, a definition always produces the same result. That makes caching by content safe.

### What gets hashed

A definition's hash covers its **whole elaborated declaration**:

- its **type** as well as its body. A proof's body alone doesn't identify which proposition it proves.
- its universe, ability and erasure information, and the identities of any primitives it uses.
- the hashes of everything it refers to, in its type or its body. Local variables are replaced by positions (de Bruijn indices), so renaming them changes nothing.

**Names of functions and values aren't part of the hash.** Renaming a function doesn't invalidate anything.

**Recursive groups.** A recursive function refers to itself, and mutually recursive functions refer to each other, so they can't be hashed one at a time with their dependencies first. Each group of mutually recursive definitions is hashed as a unit, with members referring to each other by their index within the group. This follows Unison's cycle hashing. As built ([docs/core.md](docs/core.md#groups-of-definitions)): members are ordered by their hash with references to members blanked out, ties broken by source order, so moving members around doesn't change their hashes; a single recursive definition refers to itself by a fixed marker. Data types that refer to each other are hashed the same way, ordered by name ([docs/core.md](docs/core.md#groups-of-data-types)).

**Nominal types.** Two nominal data types with identical structure must still be different, so their identity needs something extra. Unison stores a unique identifier in its codebase. With plain text files, the policy is: **a nominal type's hash includes its logical module name and its own name.**

- The **logical module name** is the module's name within the project (e.g. `Pricing.Discounts`), not a filesystem path. Moving the repository to another machine or directory changes nothing.
- Once there can be several packages, the package's identity is included too, so identically named modules in unrelated packages don't produce the same types.
- Renaming a nominal type, or moving it to another module, creates a new type, and everything that uses it gets a new hash. Copying a declaration under a new name creates a new, different type. Backwards compatibility isn't a goal, so this is acceptable.

Stable identifiers written in the source can come later if needed.

### Cache layers

| Layer | Key | Result | When |
|---|---|---|---|
| Source → elaborated declaration | Hash of the declaration's source text, the **whole-declaration hashes** of its dependencies, and the set of registered decision procedures | Elaborated core declaration | Later |
| Kernel check | Definition hash | Accepted / rejected | POC |
| Test result | Test hash | Pass / fail | POC |
| Generated JS | Definition hash + export names + representation options | JS and `.d.ts` | POC |

Every key also includes the compiler version. The test-result key also includes a fingerprint of the compiler's source and the evaluation modes (natives, compact text), so a result is never reused by another build, or with natives switched off ([docs/core.md](docs/core.md#tests-and-content-hashes)).

The elaboration key must use dependencies' full hashes, bodies included, not just their signatures. If `bound: Nat` changes from `3` to `4`, its signature is the same, but elaborating something of type `Vec Nat bound`, or deciding an `auto` proof involving `bound`, can give a different result. Tracking exactly which definitions elaboration looked inside would allow finer-grained keys, but whole-declaration hashes are simpler and always correct. Adding or changing a decision procedure can also change what `auto` finds, so that's part of the key too.

In the POC only the core-hash layers exist, so **elaboration always re-runs**. What's skipped is kernel re-checking, test runs and code generation. That's still the expensive part for proofs and tests.

**Inconclusive results are never cached** as rejections or failures. A larger budget always retries.

### Cache trust

A content hash identifies an object, but doesn't prove it was checked. The policy:

- The **local** cache (`.stitchwort/cache/`, or IndexedDB in the playground) is trusted. A cached kernel success counts as "checked" ([§3](#3-precise-guarantees)).
- `stitchwort check --no-cache` re-checks everything from scratch.
- The check cache (docs/proposals/check-cache.md) is local in this sense: a hit loads a library file's or namespace's declarations without the kernel checking them again (stage 3, D1660), as Lean imports `.olean` files.
- There's no shared or remote cache. If there ever is one, its results must be re-checked locally before being trusted.

---

## 12. JavaScript extraction

**Use case:** write library functions in Stitchwort (validation, parsing, pricing rules, state machines…), prove properties about them, and call them from an ordinary JS/TS application. From the TS side it should look like any well-typed npm library.

```
$ stitchwort build --js src/pricing.sw -o dist/
  dist/pricing.js      (ES module)
  dist/pricing.d.ts    (TypeScript types)
```

### First milestone scope

The first extraction milestone supports a deliberately narrow subset. An **exportability check** refuses an `export` unless all of these hold:

1. **Pure.** The exported function performs no abilities.
2. **Concrete boundary types with codecs.** Every input and output type is fully concrete (no type parameters such as `identity: [a: Type] -> a -> a`), and has a supported encoder and decoder: `Nat`, `Int`, `Bool`, `Text`, `Char`, `List`, and data types built from these (such as the prelude's `Option` and `Pair`). Records will join them once they're built. No functions, no `Float`. Polymorphic helpers are fine *inside* the library, just not at the boundary.
3. **Decidable preconditions.** Every erased proof argument of the exported function has a registered decision procedure ([§6](#6-proofs-universes-and-erasure)), which becomes a runtime check.
4. **Assumption-free.** The exported function, everything it depends on, *and the decision procedures used by its validators* are assumption-free ([§3](#3-precise-guarantees)). Otherwise an assumed proof hidden inside a decision procedure could let invalid input through as validated, and an assumed falsehood can make extracted code wrong or non-terminating even though the assumption itself is erased. (Rocq's extraction documentation warns about exactly this.) For example, this is refused:

   ```
   assume impossible: False

   export
   bogus: Nat -> Nat
   bogus n = Void.absurd impossible
   ```

   An explicit experimental flag (`--allow-assumptions`) could permit assumptions later. It would emit a manifest listing them and make the guarantee explicitly conditional.

Host-provided abilities, exporting handlers, and functions as arguments come later.

### The contract

Each exported function is wrapped like this:

1. **Decode** every input into a fresh internal representation that the wrapper owns, reading each property once and only an object's own properties ([Objects at the boundary](#objects-at-the-boundary)). After this, the original JS objects are never read again, so mutating them (even through another reference) can't affect the result. TypeScript's `readonly` doesn't prevent mutation at runtime.
2. **Validate** the decoded value: its shape, and any decidable preconditions (e.g. `pct <= 100`). Invalid input throws a `StitchwortInputError` saying what was wrong.
3. **Compute** with the extracted Stitchwort code.
4. **Encode** the result back into JS values. Encoding is lossless, so it can't fail.

**The guarantee** ([§3](#3-precise-guarantees)): if decoding and validation succeed, the function returns the encoding of the Stitchwort result for the decoded inputs. The trusted parts are the code generator, the **encoders and decoders**, the JS engine, and enough memory and stack.

The guarantee starts *after* decoding succeeds. It makes no promise that decoding an arbitrary hostile JS object terminates or succeeds: a getter can loop or throw, and a structure can be cyclic. Decoder tests cover cyclic inputs, shared inputs, inherited properties and getter-backed properties, so these fail cleanly where possible.

### Boundary representations

| Stitchwort | TypeScript at the boundary |
|---|---|
| `Nat` | `bigint` (decoding rejects negative values) |
| `Int` | `bigint` (decoding accepts negative values) |
| `SafeNat`, `SafeInt` (the library's records `{ value: Nat, fits: value <= 2^53 - 1 }` and `{ value: Int, fits: Int.natAbs value <= 2^53 - 1 }`) | `number`: a whole number from 0 (`SafeNat`) or -(2^53 - 1) (`SafeInt`) to 2^53 - 1 (decoding refuses anything else) |
| `Float` (the library's double, `std/Float/Float.sw`) | `number`, any number: `NaN`, the infinities and `-0` included (decoding refuses only non-numbers) |
| `Bool` | `boolean` |
| `Text` | `string`, well-formed (decoding refuses lone surrogates) |
| `Char` | `string` holding exactly one Unicode scalar value |
| `List a` | `readonly A[]` as a function's parameter, `A[]` everywhere else (in a data type's declaration, as a result). Arrays are copied on decode and built fresh on encode, so a caller may keep and change one it gets, and may pass either kind in; a type an app wrote with `T[]` is assignable both ways |
| a record `type Person = { name: Text, age: Nat }` | `export type Person = { readonly name: string; readonly age: bigint }`: no tag, keys in declared order |
| an anonymous record `{ name: Text, age: Nat }` (planned) | `{ readonly age: bigint; readonly name: string }`, keys in sorted order |
| `Map Text a` (the library's `Map`, ordered by `Text`'s own order) | `{ readonly [k: string]: A }` as a function's parameter, `{ [k: string]: A }` in a result and in a data type's declaration (the same rule as lists): a plain object, a dictionary from string keys to values. Decoding reads the object's own enumerable string keys; encoding makes a fresh plain object with its entries in key order. Maps from other key types (except a `@[js.unboxed]` record over `Text`), or in another order, aren't exportable (`E-EXPORT`, "only maps from `Text`, or from a `js.unboxed` record over `Text`, cross"). See the note below |
| `Option a` | `A \| undefined`; in a record's field, or a constructor's field with `@[js.optional]`, an optional property `readonly f?: A`. `undefined` (or a missing property) is `None`, anything else is `Some` of it, and `null` is refused. An `Option` inside an `Option` is the tagged `{ $tag: "None" } \| { $tag: "Some"; value: A }` (`Option<A>`), so `Some None` and `None` differ (D582) |
| sum type `Square … \| Rect …` | `{ $tag: "Square"; side: bigint } \| { $tag: "Rect"; … }` (exported constructors must name their fields; the tag key, tag values and field keys can be chosen with attributes, see [Attributes](#attributes)) |
| proof arguments and fields | omitted (a record's proof fields are re-established by decision procedures when decoded; other data types with proof fields can't cross yet) |
| data types with parameters, such as `Pair Char Nat` | `Pair<string, bigint>`: generic aliases, whose codecs take the arguments' codecs |
| indexed families (`Vec a n`), anywhere in an export's inputs or result: directly, through a synonym, in a container or in a record field | not exportable yet (`E-EXPORT`): decoding would have to check the indices. An export may use them internally |
| functions, abilities, `Float`, type parameters of the exported function | not exportable yet |

Notes:

- **Integers are `bigint`** for now. With `number`, an input that passes validation could produce an output too large to represent exactly: `addTwo 9007199254740991` would give `9007199254740993`, which a JS `number` can't hold. The library's `SafeNat` and `SafeInt` are the bounded types that cross as `number` (below), where the type itself rules this out. `Int` division and remainder are Euclidean, not `BigInt`'s truncating pair: the generated code applies a one-step correction to `BigInt`'s `/` and `%`, while `Int.tdiv` and `Int.tmod` use them directly ([§10](#10-numbers), [integers.md](docs/proposals/integers.md#as-built-stage-5)).
- **`SafeNat` and `SafeInt` are `number`s** (SW-337, `std/Int/Safe.sw`). Inside Stitchwort each is an ordinary record of a `Nat` or `Int` and a proof that its magnitude is at most 2^53 - 1, the largest whole number a JS `number` holds exactly. At the boundary the pair is one leaf codec, chosen by the data type's content hash like `Nat`'s and `Text`'s (so a changed bound or field turns it off, leaving an ordinary record with a `bigint` field, and a program's own `SafeNat` never gets it). Decoding is a checked step, and refuses with `StitchwortInputError`: a non-`number` (`a: expected a number`; a `bigint` and a numeric string included), `NaN`, an infinity or a fraction (`expected a whole number`), and a whole number outside the bounds (`expected a whole number from 0 to 9007199254740991`, or from `-9007199254740991`). A whole `number` beyond 2^53 - 1 is refused rather than trusted, since it may be a rounded value. `-0` is read as 0, which is the same whole number. Encoding is exact and can't fail: the type's proof field bounds every value Stitchwort code can build, so there's never a result that doesn't fit, and no function that returns a `SafeNat` can overflow into a rounded value (it has to show `fits`, or return `None` through `SafeNat.ofNat`). The `.d.ts` says `number`, which is structurally all TypeScript can say about it; the bound is a runtime check. The proof field is not decoded separately: the codec's range check is its check, and the hash ties the two together. Examples: `examples/extract/safe-numbers.sw`, tested in `crates/cli/tests/extract.rs` (`safe_numbers_cross_the_boundary_as_numbers`).
- **`Float` is a `number`** (D685, docs/proposals/float.md §5, `examples/extract/floats.sw`), inside generated code too. Decoding accepts every `number` and refuses anything else (a `bigint`, a string) with `StitchwortInputError`; encoding passes the number on. A `number` that crosses in and back out is the same value under `Object.is`. Every NaN denotes `Float.nan`: observing its bits through Stitchwort (`.bits`) gives the canonical pattern, though the number itself may keep whatever payload it had. All bit reinterpretation is in one module of the generated runtime, `toCanonicalBits`/`fromCanonicalBits`, the only place a typed array or `DataView` appears (D701). Finiteness is not checked at the boundary: it belongs on the application's own types (D702). The codec applies to the library's `Float` as the kernel binds it (by content hash); `==` is `Object.is` and `Float.ieeeEq` is `===`.
- **`Map Text a` is a dictionary** (D651, D665, `std/Map/Map.sw`, `examples/extract/dictionary.sw`): a plain object from string ids to values, which is how a TypeScript app holds a `Record<Id, V>`. A `Map` is a record of a balanced tree and a proof that the tree's keys are in order, and a proof can't be checked at runtime, so the generated code doesn't decode its fields. It reads the entries and makes the map with the library's own `Map.fromList`, so the invariant holds as it does for any map, and reads one with `Map.toList`. Both are generated, at `Text.instOrd`; nothing is hashed (the generated code uses only the library's own functions, whatever they are), and the extractor accepts a map by identity (`Builtin::Map`, an ordering that is `Text.instOrd`). The elements' values are decoded by the value type's codec, so a value may be a record, a list, an `Option` (`{ readonly [k: string]: bigint | undefined }`, an entry whose value is `undefined` encoded as the property present and `undefined`; JSON drops it) or another `Map`.
  - **Decoding** reads the object's own enumerable string keys (`Object.keys`), in the engine's order, and each value once; symbol keys, inherited properties and non-enumerable ones aren't entries. Each key is checked as `Text` (a lone surrogate is refused, `scores["\ud800"]: the key isn't well-formed text: …`). Keys of an object are distinct, so the duplicate keys `Map.fromList` would resolve (the later one wins) can't occur, and entries are inserted in the engine's order; the result doesn't depend on it. A key `__proto__` is accepted when it's an own property (which `JSON.parse` makes): nothing here assigns to an object by key, so it's an entry like any other. The path in an error quotes a key that isn't a name: `people["we ird"].age`.
  - **What is refused**: `null`, `undefined`, any primitive, a function, an array (`expected an object, not an array`) and a non-plain object. Unlike a record, which is read from its own properties whatever its prototype (below), a dictionary must be *plain*: its prototype is `Object.prototype` (of this realm or another, so `vm` contexts and iframes work) or `null`. A JS `Map`, a `Date`, a `Set` or a class instance has no entries as own properties, so reading it as a dictionary would silently give an empty map, which is never what a caller meant (`expected a plain object, not a Map, a class instance or another kind of object`). A getter that throws is refused with the error as the `cause`, as for any property. Shared sub-objects are decoded once and cyclic input is refused, as everywhere.
  - **Encoding** makes a fresh `{}` and defines each key with `Object.defineProperty` as an ordinary writable, enumerable, configurable data property, so `__proto__`, `constructor`, `toString`, `hasOwnProperty` and the empty string are entries like any other, and no setter on `Object.prototype` is called. The result has `Object.prototype` as its prototype, so it behaves as any object a TypeScript app would write: it compares, spreads (`{ ...d }` copies an own `__proto__` as data), `JSON.stringify`s (`{"__proto__":1}`), `structuredClone`s and passes `isPlainObject` checks. A null-prototype object would be safe too, but it lacks `hasOwnProperty`, `toString` and the rest, which breaks `String(d)`, `d.hasOwnProperty(k)` and some test matchers in an app that doesn't expect it, and `JSON.parse` doesn't produce one. What the defined-property approach doesn't change is TypeScript's own hazard: reading `d["toString"]` on a dictionary with no such entry gives `Object.prototype`'s method, as for any `Record<string, V>`, and a consumer should use `Object.hasOwn`.
  - **Key order on output** is the map's, which is `Text`'s order: by Unicode code point (not JS's UTF-16 code unit order, which puts U+1F600 before U+FFFF), so `["", "B", "a", "b", "é"]`. JS itself lists keys that are array indices (`"9"`, `"10"`) first, in numeric order, whatever order they're defined in, so those keys come out in that order. The order is a promise only to that extent: don't depend on it for anything but a stable output.
  - **TypeScript**: arguments are `{ readonly [k: string]: A }` and results, and maps inside a declaration, `{ [k: string]: A }` (a list or map inside a declaration is mutable, so an app's record holding a `Record<Id, V>` is assignable both ways: `extract.rs` checks it), the same type as `Record<string, A>`. That accepts an app's `Record<SpeakerId, V>` where `SpeakerId` is a flavoured string (`string & { _flavor?: … }`) or a branded one (`string & { __brand: … }`), an index signature, a `Readonly<Record<…>>`, and a type alias for an object type with known keys (`{ a: bigint; b: bigint }`). An `interface` with known keys isn't assignable to an index signature, which is TypeScript's rule, not the declarations': a `type` alias is (`examples`' `extract.rs` checks each of these with `tsc`). Results assign back to a `Record<SpeakerId, V>`; a `Record<'a' | 'b', V>` (a finite union of keys) needs a cast, since the result might lack keys.
  - **Only `Text` keys cross**, and only in `Text`'s own order, or keys of a `@[js.unboxed]` record over `Text` (a microtype, `Map UserId V`) in its derived order, which compares the field by `Text`'s, so the keys sort the same (D1068; the `.d.ts` names the key, `{ readonly [k: UserId]: V }`, and a key's proof fields are checked). Every other `Map k v` (`Map Nat v`, `Map (Text, Text) v`, a `Map Text v [ord := reversed]`, a microtype key in an order the program wrote) is refused at extraction with `E-EXPORT`: "`Map Nat Nat` can't cross the JS boundary: only maps from `Text`, or from a `js.unboxed` record over `Text`, cross, as plain objects". Keys that are numbers, characters or tuples would need their own string forms, which isn't decided; `Set Text` isn't covered either.
- **`Option` is `T | undefined`** (D582, `examples/extract/options.sw`). `undefined` is `None`; any other value is decoded as a `T` and is `Some` of it. Encoding gives `undefined` for `None` and the encoded value for `Some`. In a record's field, and in a constructor's field written `@[js.optional]` (docs/syntax.md, Attributes), the TypeScript property is optional (`readonly nick?: string`): a missing property or `undefined` is `None`, and an encoded `None` leaves the property out rather than setting it to `undefined`, so the declarations also type-check under `exactOptionalPropertyTypes`. Everywhere else (arguments, results, list elements, a constructor's fields without `js.optional`, the arguments of a parameterised type such as `Box (Option Nat)`) the type is `T | undefined`, written `(T | undefined)[]` in a list. `null` is refused (`p.nick: expected a value or undefined, not null`), not read as `None`: `null` and `undefined` are different values, and a separate `Nullable` type for APIs that use `null` is undecided. Only the outermost `Option` is `T | undefined`; an `Option` inside an `Option` stays the tagged object, `{ $tag: "None" }` or `{ $tag: "Some"; value: T }` (`Option<T>` in the declarations), because `T | undefined` can't tell `Some None` from `None`: `Option (Option Nat)` is `Option<bigint> | undefined`.
- **Fields with defaults** (docs/proposals/named-arguments.md §5.3, D1101, D1114, `examples/extract/field-defaults.sw`): a parameter may leave out a field that has a default, and the decoder fills it, in field order, by calling the default's generated helper (`RangeOptions.step.default`) with the earlier fields it takes; a result always has every field. A parameter's type is the input shape, `RangeOptionsInput`, with the defaulted fields optional, and every type holding one has an input shape too (`JobInput`); a result's is the complete `RangeOptions`. Only a missing own property asks for the default: a present `undefined` is decoded as given, so for a defaulted `Option` field it is `None` (`colour?: string | undefined` going in), and such a field is always present coming out (`colour: string | undefined`), so a round trip keeps `None`. `Option` fields without a default keep the encoding above. See docs/syntax.md, Field defaults.
- **`Text`** is a sequence of Unicode scalar values, so decoding refuses a JS string containing an unpaired surrogate (which JS allows) with `StitchwortInputError`, rather than repairing it. Encoding then gives back exactly the string that was decoded. See [the text proposal](docs/proposals/text-and-io.md#the-javascript-boundary). Inside the generated code, too, a `Text` is that well-formed string (strings are immutable, so it needs no copy), and the prelude's text operations (`Text.length`, `==`, `Text.compare`, `Text.split`, `Text.join`, `Text.fold` and the rest) are native JS working on scalar values, not code units. Code that matches or builds `MkText cs` itself converts between the string and its `List Char` in a loop, only when `cs` is used ([compact text](docs/proposals/compact-text.md#as-built-stage-1)).
- **Decoding and encoding don't recurse.** Each boundary type is described by data (`list(NAT)`, `data(info$Tree)`, `option(TEXT)`), and one loop in the generated module's runtime decodes or encodes a value of any of them, keeping its own stack. So a user's list a million long, or a tree a million deep, crosses the boundary both ways; what the exported function then does with it may still run out of stack ([Caveats](#caveats)). Decoding works depth first, reading each property once and in order, each completely before the next, so the first problem found is the same as a recursive decoder's. An error message gives the path to the problem (`order.items[2].price: expected a non-negative bigint`), summarised for deeply nested input: a run of the same step is written once with a count (`c(.tail ×999999).head`), and the middle of a long path that doesn't repeat is left out.

### Objects at the boundary

A decoder takes the data it needs from an input object and nothing else, so that what a call means depends only on the object's own data:

- **Only own properties count.** A tag, field or array element must be the object's own property (an ordinary one or a getter). An inherited one is refused (`shape.side: inherited, not the object's own property`), so nothing can come from a prototype: not from a class's getters, and not from `Object.prototype`, which any code in the app can add to ("prototype pollution"), filling in a field the caller left out. An array with a hole is refused for the same reason (`items[1]: a hole in the array`).
- **Any prototype is fine otherwise.** Objects made by `Object.create(null)`, or by a class whose constructor sets the fields, are accepted: TypeScript's types are structural, so the `.d.ts` accepts them, and their own properties are all a decoder reads.
- **Extra properties are ignored.** TypeScript allows them too (on any object that isn't a literal), and an app's objects often carry more than a library needs.
- **Arrays and objects aren't interchangeable.** A `List` must be an array (`Array.isArray`), and a data value mustn't be one.
- **Frozen objects are fine.** Decoding never writes to its input.
- **Each property is read once** each time its object is decoded, so a getter is called once there, and can't give one answer to validation and another to the computation. If reading a property throws, the input is refused with a `StitchwortInputError` whose `cause` is what was thrown.
- **Shared parts are decoded once.** An array or object reached again by another path (but not inside itself, which is a cycle and refused) isn't read or decoded again: the value decoded the first time is used, for each type it's decoded at. Stitchwort values are never changed, so sharing them is safe. So decoding takes time and memory in proportion to the number of distinct objects in the input, not the number of paths through it: a DAG 60 levels deep whose nodes' two children are the same object has 2^60 paths but 61 objects. (An object whose fields are all numbers, booleans, text, string unions or optional versions of those, a record's included, is decoded again wherever it's reached, which costs no more than reading it, and is quicker than remembering it.)
- **A fast path, with the same answers.** Each type that crosses has a decoder and an encoder specialised to it, generated into the module as straight-line code: no description of the type is interpreted per value, and no path is kept. The fast decoder keeps the same books as the general one (what has been decoded at each type, so sharing and cycles are handled as above, and each property is read once), and hands a value nested more than 100 deep to the general decoder, which uses no stack for nesting. It never explains a refusal: on any failure the general decoder runs on the whole input and says where and why, or accepts it, so what is accepted and every message are the general decoder's. The only trace is that an input that is refused has been partly read before. The encoder gives up the same way, to the general encoder.

### Names

Stitchwort names (ASCII letters, digits, `_` and primes) don't line up with JavaScript's, and some names mean something to JS objects or to the generated module. These rules make sure nothing a program names can clash with anything else, by construction rather than by a list of names to avoid:

- **The tag.** A data type's objects say which constructor they are in the property `$tag` (D612), unless the type chooses another key with `js.tag` ([Attributes](#attributes)). A Stitchwort name starts with a letter or `_`, and only its later primes become `$`, so no field's default key is `$tag`: `MkLabelled (tag: Text) (count: Nat)` is `{ $tag: "MkLabelled"; tag: string; count: bigint }`.
- **Fields.** A field's key, in boundary objects and in the `.d.ts`, is its name with each prime written `$` (`x'` is `x$`), unless `js.name` gives it another. Stitchwort names can't contain `$`, so two fields' default keys never clash. The key `__proto__` is refused (`E-JS-NAME-CLASH`): assigning it to an object sets the prototype instead of making a property. A field called `__proto__` therefore needs a `js.name`, which is reported once an export reaches its type, so a type that never crosses the boundary isn't affected (D612); a type with any `js.*` attribute has its names checked where it's declared. Other names with a meaning on JS objects (`constructor`, `toString`, `length`) or reserved in JS (`class`, `default`) are fine as keys, so they're kept. Inside the generated code a field's key is its own (`tag` and `__proto__` are `$tag` and `$__proto__` there, and the constructor is in `tag`); the codec translates between the two.
- **Constructors** only appear as tag strings, so any name works (`"MkBox'"`), as does any non-empty `js.name` (`"__proto__"` and `"constructor"` included: tags are looked up in a `Map`).
- **Data types** are named by their short name with each prime as `$` in the `.d.ts` (`Box'` is `Box$`, `Geometry.Shape` is `Shape`). Two different types at the boundary with the same short name are refused (`E-EXPORT`); the same type reached twice is one type. A data type at the boundary can't be called `StitchwortInputError` or `StitchwortResourceError`, which the module exports itself.
- **Exports** are imported by their short name (`Geometry.area` is `area`; two exports with the same short name are `E-EXPORT`), which must be a JS identifier (so no primes) that aren't reserved in JS (`delete`, `class`, `this`, `eval`, `undefined`, …), or they couldn't be imported by name; nor can they be the module's own two exports. An export isn't a name in the module's own scope: its wrapper is `$$name`, exported with `export { $$name as name }`. So an export can be called anything else, `Set`, `BigInt` or `decode`, without hiding a JS global or one of the runtime's helpers.
- **Everything else in the module** has a namespace of its own. Definitions are `$` and their full logical name (`Std.List.length`, `Main.area`) encoded injectively: `'` is `$p`, `.` is `$d`, the `%` of a generated name (`State.%elim`) is `$g`, and any other character `$u` and six hex digits (docs/proposals/namespaces.md §7.3). Wrappers are `$$name`, data type descriptions `info$` and the encoded full name, and locals generated names (`v0`, `s0`, `arg0`). The runtime's helpers have plain names, which only exports could have reached. A parameter's Stitchwort name appears only in the `.d.ts` and in error messages; a reserved word there is replaced by the name in the equations, or `arg0`.

`examples/extract/names.sw` uses each of these, and a property-style test (`awkward_names_never_collide` in `crates/cli/tests/extract.rs`) generates data types and exports from a pool of awkward names, and attributes choosing awkward tag keys, tag values and keys, and checks that every object has its own key for each field, values round-trip, and the `.d.ts` accepts exactly the objects the module takes.

### Attributes

A TypeScript app usually has a wire format already: the discriminant is `type`, its values are `"CIRCLE"`, a key is `center_x`. Attributes (`@[…]`, [docs/syntax.md](docs/syntax.md#attributes), [attributes.md](docs/proposals/attributes.md)) say how a data type crosses the boundary, where the type is declared:

```
@[js.tag "type"]
type Shape =
  | @[js.name "DOT"] Dot
  | @[js.name "CIRCLE"] Circle (radius: Nat) (@[js.name "center_x"] centerX: Nat)
```

crosses as `{ readonly type: "DOT" } | { readonly type: "CIRCLE"; readonly radius: bigint; readonly center_x: bigint }`.

- **`js.tag "KEY"`** on a data type (not a record, which has no tag): the tag's key instead of `$tag`. Not empty, not `__proto__`.
- **`js.enum`** on a data type whose constructors have no fields (a proof or type field or a type parameter doesn't count; a record, a type with no constructors or `js.tag` alongside is `E-ATTRIBUTE`): the type crosses as a plain string, each constructor as its `js.name`, or else its name, and the declaration is `export type Label = "IMPORTANT" | "SLIDE_TEXT";`. Decoding accepts exactly those strings, so anything else (another string, a non-string, a `{ $tag }` object, a name inherited from `Object.prototype`) is refused with the allowed strings and the path in the message; encoding writes the string. Equal strings are `E-JS-NAME-CLASH`. It works wherever the type does (a field, an `Option`, a list, a dictionary, a function's argument or result). A TypeScript `enum` of the same strings is assignable *to* the union but not *from* it, so an app's type test compares against `` `${Label}` `` (docs/syntax.md, Attributes). Example: `examples/extract/string-enums.sw`.
- **`js.unboxed`** on a record without parameters that has exactly one field with a property (proof and type fields don't count; that field not an `Option`): the record crosses as its field's own JS form, both ways, wherever it appears, and its declaration is a plain alias, `export type UserId = string;`, named at every use (D1065, D1066). Decoding decodes the field and checks the record's proof fields; inside generated code the record already is its field (D866), so encoding writes the field. A `Map` from one over `Text`, in its derived order, is a plain object (D1068). `E-ATTRIBUTE` on a data type with constructors, a constructor, a field, a parameterised record, one with no field or two with a property, an `Option` field, alongside a `js.name` on its field, with an argument or twice. Example: `examples/extract/microtypes.sw` (docs/proposals/microtypes.md, "As built").
- **`js.name "NAME"`** on a constructor: its tag value; on a constructor's or record's field that has a property (not a proof or a type field): its key. Written exactly, never mangled, and escaped correctly in the JS and the `.d.ts`. The same logical field may have a different key in each constructor.
- **One representation.** The tag key, then each constructor's tag value, then each field's key are resolved once, from the attributes or the defaults, and checked: tag values distinct, a constructor's keys distinct and none the tag key, no key `__proto__` (`E-JS-NAME-CLASH`). The codec tables and the `.d.ts` both read that one result. `@[js.tag "$tag"]` is exactly the same as writing nothing.
- **They don't change meaning inside Stitchwort**: patterns, `show`, `==`, the order, `stitchwort run` and proofs use the Stitchwort names, and the kernel never sees attributes. They aren't part of content hashes, so a logical hash doesn't identify a JS interface (D598): they're kept beside the data type, read only by the JS backend, and cached with the namespace that declares the type.
- **A closed set.** An unknown attribute is `E-ATTRIBUTE-UNKNOWN`; a known one where it doesn't apply (a theorem, a function's parameter, a lambda, a namespace, an interface, an export for now), with a missing argument, twice on one target, or on a type with a built-in boundary form (`Nat`, `Int`, `SafeNat`, `SafeInt`, `Float`, `Bool`, `Text`, `Char`, `List`, `Option`, whose codecs couldn't honour it) is `E-ATTRIBUTE`. Nothing is silently ignored.

Renaming types and exports (`js.name` on them) and `js.nullable` (a required `T | null` field) are later stages of the proposal.

### Code generation

1. **Erase** types, proofs and proof fields.
2. **Lower** to a small untyped IR: functions, constructors, `case`.
3. **Generate JS**, with a function's tail calls to itself turned into loops (including calls in the branches of an `if` or `if h:`, in a lifted `match`, through another member of its group, or through the `%step` of a definition by `decreasing`; [docs/core.md](docs/core.md), "Tail calls as loops").
4. **Wrap** each `export` with the decode → validate → compute → encode steps, and export the wrapper under the export's name ([Names](#names)).
5. **Emit** `.d.ts` from the Stitchwort types.

### Caveats

- **Stack depth.** JS engines generally don't optimise tail calls. A function's tail calls to itself become loops, and so do tail calls between two members of a group, like `isEven` and `isOdd` ([docs/core.md](docs/core.md), "Tail calls as loops"); other recursion, such as `List.length` or `List.append` over a long list, or a user's own recursion over a text's characters, uses a stack frame per step and can overflow the stack (in Node, after a few thousand elements; the [text proposal](docs/proposals/text-and-io.md#as-built) has measurements). The prelude's text operations are native, and they and the conversions between a text and its `List Char` don't use stack space proportional to a text's length, so they handle millions of characters. The guarantee doesn't cover that, but it's reported cleanly: the export throws a `StitchwortResourceError`, with the engine's error as its `cause`. Decoding and encoding themselves don't use the JS stack (see above).
- **Encoding doesn't share.** Each output is a tree of fresh objects, so a result with much sharing (such as a shared input passed straight back, or a tree built by a function that uses one subtree twice at each level) is encoded once per path, which can take exponentially long. Similarly, decoding checks a string each place it appears, so the same long string in many places is checked many times.
- **Erasure must be correct.** The `Prop` elimination rules ([§6](#6-proofs-universes-and-erasure)) ensure nothing that runs depends on an erased value.

### Later: effects from the host

Exported functions that need abilities could get them from the host app, much like dependency injection:

```ts
const total = await checkout(cart, {
  http: { get: (url) => fetch(url).then((r) => r.json()) },
});
```

Host implementations are **trusted contracts**: JS can't be checked for purity or totality. Values they return are decoded and validated like inputs. Handlers compile to JS generators, which needs the runtime "at most once" restriction ([§8](#8-abilities-and-handlers)). If any host operation is async, the exported function returns a `Promise`.

---

## 13. Soundness policy

"Sound" means the guarantees in [§3](#3-precise-guarantees) actually hold. Some soundness problems are ordinary bugs, fixable whenever. Others are core design decisions that are painful to change later. **We get the core decisions right from the start, and track the rest explicitly.**

### From day one

| Measure | Why |
|---|---|
| **Small trusted kernel** that re-checks all elaborated declarations | Bugs in the large front-end can't produce false proofs. Later fixes stay in one place. |
| **Numbered universes** in the kernel | `Type: Type` allows paradoxes that break both proofs and termination. |
| **`Prop` elimination rules** | Runtime results can't depend on erased proofs. |
| **Strict positivity check** on data types | Without it, `type Bad = MkBad (Bad -> Void)` lets you prove anything. A type nested in another (`List Packet`) is allowed only at that type's nestable parameters, computed by the kernel from its constructors, never declared (Lamiaux, Forster, Sozeau and Tabareau's rule, with one extra restriction; [docs/core.md](docs/core.md#nestable-parameters)). That an accepted nested type has a mutual encoding the kernel accepts without nesting is tested on generated declarations (`crates/driver/tests/nested_oracle.rs`). |
| **Exhaustiveness checking** of pattern matches | A missing case is a hidden crash. |
| **Conservative termination checking** | Rejecting too much is safe. It can be relaxed later without breaking anything. |
| **Checking never runs effects** | Principle 2. |
| **Tracked assumptions** | Planned (principle 3): a command listing every `assume`, foreign function, proof hole and conjecture a definition depends on. There are none to list yet: no `assume` exists ([docs/core.md](docs/core.md#how-this-differs-from-designmd-today)), and handler termination is checked, not assumed ([§8](#8-abilities-and-handlers)). The CLI has no such command; `stitchwort axioms` lists axioms. |
| **Axiom report** | `stitchwort axioms <name>` lists the axioms a definition depends on, transitively (today only `Quot.sound`, found even when it sits inline in a body). It reports foundational dependencies only; it doesn't promise the term computes to data in the kernel. |
| **A "must reject" test suite** | Readable example programs that must fail to type-check. |
| **Native arithmetic is listed and tested** | A few prelude definitions on `Nat` run natively, in the kernel's evaluator and in extracted JS. `Int` has no kernel natives (decision K1): its operations are ordinary definitions over `Nat` constructors, so only `Nat`'s natives run in the kernel. Each native is trusted, so each is compared with its own definition by tests, as the whole result: a native returning a proof must give the definition's own proof term, so natives never change which `rfl` proofs check ([`docs/core.md`](docs/core.md#numbers)). |
| **`+` computing on both sides is listed and tested** | Two reduction rules for `Nat.add` that aren't its definition: `m + Zero → m` and `m + Succ n → Succ (m + n)`, applied by both kernel evaluators, natives on or off, only when `add`'s own case tree is stuck on its first argument ([`docs/core.md`](docs/core.md#numbers), `crates/core/src/nat_add.rs`). They are trusted reduction rules, not axioms: typed, left-linear, first-order rules on constructor patterns whose equations are derivable from the definition, confluent with the rest of the kernel's reduction (four critical pairs, all joining) and terminating on their own; that the whole core stays strongly normalising with them added is expected, not proved ([nat-add-recursion.md](docs/proposals/nat-add-recursion.md) §9, with every assumption). Bound only to the library's exact `Nat.add` by content hash (which covers `Nat`; for another, the rules stay off), with `Nat.addZero` and `Nat.addSucc` checked to state the two equations as a safety net. Tests: the four critical pairs joined with both evaluators, natives on and off; stuck sums compared across evaluators; a copy of `Nat.add` gets no rules. A wrong rule could prove something false, as a wrong native could. |
| **Compact text in the kernel is listed and tested** | A text literal's characters are one compact range in the checked term and in the evaluator, standing for `Cons (MkChar c rfl) … Nil`. The rules for it (typing, matching, conversion, quotation, hashing) are trusted, and only used with the exact prelude `List` and `Char` they were written for (by content hash); otherwise literals are constructors. Tests compare complete results with the constructor form ([compact text](docs/proposals/compact-text.md#as-built-stage-2)). A wrong rule could prove something false, as a wrong native could. |
| **`Float`'s reduction rules and natives are listed and tested** | `Float.add` and `sub` are definitions (exact, then rounded, through `Float.Model`). The other rounding operations (`Float.mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`, `ofInt`, `ofNat`) are bodyless primitives the kernel computes with Rust's `f64` on known doubles, under a versioned contract (`FLOAT_CONTRACT` in their hashes, the toolchain in the build fingerprint): no new propositional axioms, but new trusted reduction rules. `Float.toText` is a bodyless primitive the kernel never computes, with a meaning each runtime supplies. `neg`, `abs`, `isNaN`, `isFinite`, `ieeeLt`, `ieeeLe`, `toInt`, `decEq`, `add` and `sub` have natives that give their definitions' whole results, used only while a program or test runs: checking computes the definitions, so the natives are not in the kernel's trusted base. All are bound to the library's exact declarations by content hash, and tested: definitional agreement with the natives on and off on the native and WebAssembly kernels, and the four execution paths (both kernels, the runtime, Node) compared as canonical bits ([float.md](docs/proposals/float.md)). |
| **Native text and `Int` in extracted JS are listed and tested** | In extracted JS only (not the kernel), 14 prelude text operations and 23 prelude `Int` operations are native JS, each used only for the exact definition it was written for (by content hash) and compared with the definition compiled without the native ([compact text](docs/proposals/compact-text.md#as-built-stage-1), [integers.md](docs/proposals/integers.md#as-built-stage-5)). There are two fallbacks: a changed operation's definition disables only that native, while a changed `Int` data type disables the `bigint` representation, the boundary codec and every `Int` native together. A wrong one would give a wrong answer in JS, not a false theorem. |

### The "must reject" suite

Each rejected example is paired with a nearby example that must be **accepted**, so a check can't pass by rejecting everything.

| Must be rejected | Because | Paired accepted example |
|---|---|---|
| Non-positive data type (`MkBad (Bad -> Void)`) | Positivity check | A positive recursive type (`List`) |
| A negative occurrence through a sibling (`Bad1 = MkBad1 (Bad2 -> Void)`, `Bad2 = MkBad2 Bad1`) | Positivity across the data group | `Tree`/`Forest` |
| A type nested in a container that takes its parameter as input (`Bad = MkBad (inner: Neg Bad)`); nested in `Option` but as a function's input (`Option WithCheck -> Bool`) | Nested positivity: only at nestable parameters ([nested types](docs/core.md#nestable-parameters)) | `Packets (items: List Packet)`; `MkStored (next: Option Stored)` |
| A field depending on an earlier field that holds the type (`Fnat`'s `same: n = m`) | No inductive-inductive types | An equation between fields that don't hold it (`Checked`) |
| A type nested at a parameter another parameter's type mentions (`List.Member Q []`) | Nestable parameters, condition 2 | Nested in `Option` (`Chain`) |
| Matching on a proposition with a nested field to produce data (`MkP (h: And P Unit)` to `Nat`) | `Prop` elimination: it counts as defined together with the copy of `And` | Matching it to produce a proof |
| A type nested in a `Map` (a quotient) | Quotients aren't data types | Nested in a `List` |
| Girard / Hurkens paradox | Universe levels | A function quantifying over `Type 0` values |
| A total function calling a `Partial` one | Ability checking | The same function declared `{Partial}` |
| A missing pattern-match case | Exhaustiveness | The complete match |
| Matching on `p ∨ q` to produce data | `Prop` elimination | Matching on `p ∧ q` to produce data |
| Extracting the witness of `∃ x, p x` as data | `Prop` elimination | Using the witness inside another proof |
| `reveal: HiddenType -> Type` ([§6](#6-proofs-universes-and-erasure)) | `Prop` elimination: a type field isn't a proof | Transport along `a = b` |
| `loggedProof: () -> {IO} True` treated as erasable | Effectful arrows are never in `Prop` | Erasing the `True` it returns |
| `n / d` with nothing known about `d` | No evidence for `d != 0` | `if h: d != 0 then n / d else 0` |
| `Ping`: a handler restarting its computation ([§8](#8-abilities-and-handlers)) | Handler clauses can't recurse | A handler that only resumes `k` |
| Landin's knot through `Cell` ([§8](#8-abilities-and-handlers)) | Operations must be data-only | `State Nat` |
| `runState` with `State (List (Nat -> Nat))` | `IsData` checked transitively | `runState` with `State (List Nat)` |
| A user handler for `Partial` | Only the runtime handles `Partial` | Running `Partial` code from `main` |
| Updating `items` of a `SortedList` without a new proof | Dependent record updates | Supplying `items` and a new `sorted` proof |
| Exporting `bogus` (depends on `assume impossible: False`) | Exports must be assumption-free | Exporting an assumption-free function |
| Exporting `identity: [a: Type] -> a -> a` | No codec for an unknown type | Exporting `identity` specialised to `Nat` |
| Exporting `head: Vec Nat (Succ n) -> Nat`, `List (Vec Nat 3) -> Nat`, a function through `type Row = Vec Bool 5`, or `Grid -> Grid` with `Vec` in a record field | No codec checks indices | Exporting a `List Nat -> Nat` function that uses `Vec` inside |
| Matching `v: Vec a (n + m)` with `n` and `m` unknown; `Ty (List Nat)` against `TList` | The unifier is stuck (`E-INDEX-STUCK`), never guessing | The same after matching `n`; `append`; `Ty c` |
| Matching `l: Loop n n` where `MkLoop: Loop m (Succ m)`; stuck dependent injectivity | Occurs check; no comparison at the wrong type | `Loop n k`; the same with variables for the stuck side |
| A `Prop` conflict or injectivity taken through a proposition (`SameP A B`, `Hide 0 = Hide 1`, a proof field before data) | Proofs are never taken apart as data (the `Prop` guard) | The same in `Type`, which does conflict |
| A body on an impossible branch, or no body on a possible one, built directly | The kernel re-checks which branches are impossible | The branch marked correctly |
| `down [n: Nat]: Vec Bool n -> Nat` recursing on a solved index; Agda #6654 in `Prop` (`noBad`) | Termination reads no decrease from an index equation | The same recursing on `xs`; `leToLeq` |
| `type Bad: Type = \| B (f: (p: Type) -> p -> p): Bad f` and `type Ty: Type -> Type`, a large index or field | Universe rule for fields and indices | The same in `Type 1` |
| `def wrap: Type 0 := Type 4294967295`, which a release build accepted before SW-902 (the step up wrapped at `u32::MAX`, a cyclic hierarchy), and a field of that type in `Type 0`; `Type 65536`; `Type 65535` used as a term | The largest universe, `Type 65535`, has no universe above it: the kernel's `Sort::succ` refuses it rather than wrapping or saturating, and the parser refuses larger levels ([docs/core.md](docs/core.md#universes)) | `Type 65533 : Type 65534`, and a type in `Type 65534` |
| Rocq CVE-2026-72703: a group whose only calls are cross-calls, each on a larger argument (`f n := g (Succ n)`, `g n := f (Succ n)`), with two or three members | Size change over the closure of the whole group's calls | `countdown`/`step` and `total`/`inner` in `accept/mutual.sw` |
| Rocq CVE-2026-72705: a recursive function passed, bare or under a lambda, to a recursive function that applies it to `1`; the same producing `T ≡ T → Void` | Saturation, and lambda-bound arguments are unknown to size change | `walk`/`stepBy` in `accept/mutual.sw` |
| Lean Kernel Arena `k-rec-conv`: `(x => x) = (z => y)`, and `J … 5 h = 5` on a hypothesis `h: 0 = y`, by `rfl` | K is a unification rule, not a reduction; `J` computes only on `rfl` | `kOnRfl` in `accept/kernel-2026-neighbours.sw` |
| Arena `eta-unit-like-proof-field`: `p = q` by `rfl` for two values of `{ h: 0 = 0 }` | No record eta, no definitional proof irrelevance | `box` in the same file |
| lean4#14806: `(f x, f y) = (g x, g x)` and a chain of pairs found equal before a false one, in one comparison | Conversion memos are keyed by the exact pair, never closed transitively | `good` in the same file |
| Arena `forged-quot-ind`: a user `type Quot` or `def Quot.ind` | Quotients are a term former, and their names are reserved | `accept/quot-forms.sw` |
| `IsSucc k -> Nat` reading the index field; `Le m n -> Bool` by matching | `Prop` elimination with indices (the index clause is deferred) | `IsSucc k -> k != 0`; `Le (Succ n) 0 -> Nat` |

**A rejection only counts if it's for the right reason.** Every diagnostic has a stable error code (e.g. `E-POSITIVITY`), and each "must reject" example declares the code it expects. A crash, a timeout, a syntax error in the example, or an unrelated error (like an unknown name) is a test failure, not a pass.

### Known gaps

| Gap | Status |
|---|---|
| **Handler termination** | Checked by the kernel's positivity and termination checks on the translation into `Effect.Comp` ([§8](#8-abilities-and-handlers)). Trusted: the termination rule for recursive function fields, with no soundness proof for this kernel ([abilities.md](docs/proposals/abilities.md), "The termination rule"); and that the translation is faithful to the semantics, which is tested by comparing behaviour, not proved. |
| **Extractor and encoders/decoders** | Trusted, not verified. Rocq's extraction has the same caveat. |
| **Local cache** | Trusted ([§11](#11-content-hashing-and-caching)). `--no-cache` re-checks everything. |

---

## 14. Implementation

**Current state:** milestones 1–4 and 6 are implemented (including decoders that refuse cyclic inputs and read each property once), and milestone 5 in part: tests, declaration hashes, a test-result cache and a cache of checked declarations ([docs/proposals/check-cache.md](docs/proposals/check-cache.md)), but not yet caching generated JS. Evaluation keeps its pending work on the heap and runs within per-operation resource budgets ([docs/proposals/stack-safe-evaluation.md](docs/proposals/stack-safe-evaluation.md)). Numbers are native (arbitrary precision, with native arithmetic); `Int` is implemented as a data type over `Nat`, with its own extracted-JS natives. Milestone 7 is implemented, with `Partial` at stage 1 ([docs/proposals/partial.md](docs/proposals/partial.md)): abilities, rows, direct-style effectful code and handlers, translated into the inductive `Comp` trees chosen in [docs/proposals/abilities.md](docs/proposals/abilities.md). `stitchwort run` performs a program's `IO` for real ([docs/proposals/text-and-io.md](docs/proposals/text-and-io.md)). The playground (`web/`, `crates/web`) runs the compiler as WebAssembly, in a Web Worker, and can run `main` with scripted input; it caches test results in the browser, as the CLI does. The elaborator and kernel are separate, as principle 4 requires. [`docs/core.md`](docs/core.md) gives the core rules as implemented, including where the implementation still differs from this document. [`docs/syntax.md`](docs/syntax.md) describes the implemented syntax.

Written in **Rust**. The compiler itself compiles to **WASM** for the browser playground.

### Pipeline

```
 source (.sw)
    │ parse
    ▼
 surface AST ──── elaborate ────► core declarations ──── kernel check ────► checked declarations
 (spans, sugar)   (implicits,      (small, explicit)     (types, universes,      │
                   unification,                           Prop elimination,      ├─► hash → cache
                   auto, pattern                          positivity,            ├─► evaluate (run, test)
                   matching)                              exhaustiveness,        └─► erase → JS + .d.ts
                                                          termination)
```

### Techniques

- **Bidirectional type checking** with **normalisation by evaluation (NbE)**. The same evaluator compares types during checking and runs programs, with different reduction policies for each ([§6](#6-proofs-universes-and-erasure)). It's a simple tree-walking interpreter, and performance isn't a goal. The evaluator has a step budget, so it reports "inconclusive" rather than hanging the tool.
- **Metavariables and pattern unification** for implicit arguments, following András Kovács' [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).
- **The kernel** checks core declarations with no metavariables, implicit arguments or sugar. It checks universe levels, `Prop` elimination, positivity, exhaustiveness and termination on core `case` trees.
- **Effect rows** checked alongside types, following Koka.
- **Layout specification before the parser.** A short written spec of the indentation rules (continuation lines, nested `handle` clauses, `where` blocks, delimiters, tabs), backed by golden parsing tests.

### Crates

| Crate | Responsibility |
|---|---|
| `syntax` | Source files, spans, diagnostics. Lexer, parser, surface AST |
| `core` | Core terms, values, evaluator, **kernel** |
| `elab` | Elaboration: implicits, unification, `auto`, pattern matching, abilities |
| `cli` | The `stitchwort` command, the compiler driver, diagnostic rendering |
| `cache` (later) | Hashing and the result cache |
| `js` (later) | Erasure, JS code generation, `.d.ts`, encoders/decoders |
| `web` (later) | `wasm-bindgen` bindings and the playground page |

### Testing

Example `.sw` programs are the main test suite, so behaviour can be reviewed without reading type theory (see `examples/README.md`):

- `examples/accept/` must type-check. Their outputs are snapshot-tested with `cargo insta`.
- `examples/reject/` must fail **with the error code the file declares**. Their error messages are snapshot-tested, which also keeps errors readable.
- `examples/soundness/` holds the "must reject" suite and its paired accepted examples ([§13](#13-soundness-policy)). Known gaps are marked with `-- known-gap`.
- A panic, or a budget running out, is always a test failure, never a rejection.
- **Differential extraction tests:** run each extracted function on the same inputs both in the reference evaluator and as generated JS under Node, and check the results agree through the specified encoding. This is what actually tests the preservation guarantee. Separately, the generated `.d.ts` is type-checked with `tsc`.

### Tooling

All tooling comes from the Nix flake (`flake.nix`). Run `nix develop`, or use direnv via `.envrc`. `nix flake check` builds, tests, runs clippy and checks formatting. The Rust version is pinned in `rust-toolchain.toml`. The `wasm-bindgen` crate version must exactly match the `wasm-bindgen-cli` provided by Nix (currently 0.2.129).

---

## 15. Roadmap

Each milestone ends with something demonstrable.

| # | Milestone | Demo |
|---|---|---|
| 1 | **Core spec, kernel and REPL.** Written typing rules for the core, including which universe function types live in, the `Prop` elimination rule, the effect judgment and the reduction policies. Dependent functions, numbered universes, `Prop`, evaluation with a step budget, stable error codes | Type an expression, get its type and value. A universe paradox is rejected with the right error code |
| 2 | **Data types, pattern matching, totality.** `Nat`, `List`, structural recursion, positivity and exhaustiveness checks, `Prop` elimination, `rfl`/`Eq.cong` | `appendLength` checks. Non-terminating functions, non-positive types, `∨`-elimination into data and `HiddenType` are rejected, each for the right reason |
| 3 | **Implicit arguments and `auto`.** Unification, implicitly bound type variables, `[a := …]`, `Decidable`, local hypotheses, `/` with non-zero proofs | Write `map f xs` instead of `map [a := Nat] [b := Nat] f xs`. `get [10, 20, 30] 5` is a compile-time error. `if h: d != 0 then n / d else 0` checks |
| 4 | **JS extraction, first-order subset.** Erasure, codegen, `bigint`, tagged encodings, the exportability check, decode/validate wrappers, `.d.ts`, differential tests | Prove a function, extract it, call it from a TS file, and see its results agree with the reference evaluator. Invalid input is rejected at the boundary |
| 5 | **Hashing and caching.** Declaration hashes, recursive groups, nominal identity, kernel/test/JS caches | `stitchwort test` shows `cached` vs `ran` as you edit |
| 6 | **Browser playground.** Compiler as WASM, editor, run/test/extract buttons, resource budgets | A link you can send to people |
| 7 | **Abilities.** First, written operational semantics for handlers ([§8](#8-abilities-and-handlers)). Then deep handlers with the admissibility rules, `IsData`, `State`, `Abort`, `IO`, `Partial` (runtime only) | Effectful code tested through pure handlers, with its assumptions shown. `Ping`, `Cell` and function-valued state are rejected |
| 8 | **Records.** Row-polymorphic records, closed dependent records with checked updates | The record examples from [§4](#4-language-tour) |

**Later:** universe polymorphism, generic `withFuel`, host-provided abilities and handlers in JS, property tests, fixed-size numbers, the source-level elaboration cache, `number` representations for other bounded types (`SafeNat` and `SafeInt` are the first).

Until milestone 7 there is no `Partial` at all. The termination checker rejects non-terminating definitions, and universes are checked from milestone 1, so principle 1 holds from the start, apart from bugs in the kernel.

---

## 16. Open questions

Reviewers' opinions are especially welcome here. The second review recommended settling the `Prop` rule, the product rules, the bracket syntax and how `auto` uses local evidence before building the kernel and elaborator. Those are now decided ([§4](#4-language-tour), [§6](#6-proofs-universes-and-erasure)). What remains:

### Before or during milestone 1

1. **The written core rules.** The typing rules, the effect judgment, the `Prop` elimination check (including indexed propositions), and exactly what type comparison may reduce. These are decided in outline, and writing them down is the first task of milestone 1.
2. **Layout rules.** The written spec described in [§14](#14-implementation).
3. **Universes.** Should universes be cumulative (`Type 0` values also usable as `Type 1`)? When to add universe polymorphism?

### Before later milestones

4. **Finding decision procedures** (milestone 3). How does the compiler find the `Decidable p` for a given `p`? Type-class-style instances, or something simpler?
5. **`Text`** (milestone 4). Settled in [docs/proposals/text-and-io.md](docs/proposals/text-and-io.md): Unicode scalar values, with `Text` meaning a list of them, and strict JS decoding.
6. **Handler admissibility** (milestone 7). Settled by the translation into `Effect.Comp` ([§8](#8-abilities-and-handlers), [abilities.md](docs/proposals/abilities.md)): the draft 2 conjecture and its "data-only operations" rule are replaced by the kernel's positivity and termination checks. Still open: a soundness argument for the termination rule on recursive function fields in this kernel.
7. **Handler operational semantics** (milestone 7). The points listed in [§8](#8-abilities-and-handlers).
8. **Effects and dependency.** The precise typing rules for sequencing effectful code when its results are used as type indices.
9. **Runtime "at most once" for continuations.** How to check it, including through closures, for when handlers are extracted to JS.
10. **Generic `withFuel`.** What representation of partial computation makes it sound ([§5](#5-totality-and-partiality))? Stage 1 of `Partial` gives it one, `Effect.Delay`, with exact tick counts, but observing an `Effect.Delay` from total code (stage 2) needs its own argument: [docs/proposals/partial.md](docs/proposals/partial.md) §10.1 lists what.
11. **`Float`.** Its semantics, and whether it can ever be exported.

### Syntax

12. **Implicitly bound variables.** Only lowercase *type* variables in signatures are bound automatically. Value-level indices never are, so a misspelt index name is an error rather than a silent new parameter. Is that the right line?

### Naming

13. **CLI name.** `stitchwort` is long. `stitch` clashes with an existing program-synthesis tool called Stitch. Option `sw`, `wort`, or something else?

---

## 17. Related work

No existing language combines all four pillars. These overlap most:

| Language | What we borrow or learn from |
|---|---|
| **Lean 4** | Programming and proving in one language, `Prop` and its elimination rules, `Decidable`, good records. Also the contrast: partial definitions don't propagate a divergence effect ([§5](#5-totality-and-partiality)). |
| **Idris 2** | Dependent types aimed at programming, totality checking, erasure via usage annotations (a more general alternative to `Prop`), JS backend. |
| **F\*** | Dependent types plus an effect system where divergence is an effect (`Tot` vs `Dv`). The closest existing design to our `Partial` idea. |
| **Agda** | Total by default, dependent pattern matching, records. |
| **Rocq (Coq)** | Extracting verified programs to other languages. Subsingleton elimination. |
| **Unison** | Abilities, direct-style effects, content-addressed definitions, cycle hashing for recursive groups, unique types, cached tests. |
| **Koka** | Row-typed effects, inferring `total` vs `div`, and why higher-order state needs divergence tracking. |
| **Frank, Effekt** | Research languages for abilities and handlers. |
| **Hillerström & Lindley, "Shallow Effect Handlers"** | Deep handlers as folds, shallow handlers as case splits. |
| **Dhall** | Total, pure, with imports identified by a hash of their normalised form. |
| **PureScript, Roc** | Structural records with row polymorphism. |
| **elaboration-zoo**, **pi-forall** | Small reference implementations of dependent type checkers. |

---

## 18. Glossary

- **Total function:** always returns a result, for every input. It never loops forever or crashes.
- **Dependent types:** types that can mention values, such as `Vec Nat 3` or `length xs = 0`. This is what lets types express properties and proofs.
- **Proposition / proof:** with dependent types, a statement like `xs ++ [] = xs` is a type, and a value of that type is a proof of it.
- **`Prop`:** the universe of propositions. Values whose type is in `Prop` are proofs, and are erased at runtime.
- **Subsingleton elimination:** the rule that you may only pattern match on a proof to produce data when the proposition can't have two observably different proofs (e.g. equality, but not "or").
- **`Decidable p`:** a computation that produces either a proof of `p` or a proof that `p` is false.
- **Impredicativity (of `Prop`):** a statement that quantifies over anything, even over all types, is still a proposition.
- **Effect judgment (`t: A ! ε`):** "evaluating `t` produces an `A` and may perform the abilities in `ε`". Separate from any abilities mentioned inside `A`.
- **`IsData`:** a property of types meaning "contains no functions, however deeply nested". Required for state handlers.
- **Parameter / index / field:** in a declaration like `type Vec (a: Type): Nat -> Type`, `a` is a parameter (fixed across all constructors), the `Nat` is an index (can differ between constructors), and constructor arguments are fields.
- **Ability / handler:** an ability declares operations (`get`, `put`). A handler decides what they do. The same code can be run with different handlers, e.g. real IO vs a pure test double.
- **Continuation:** "the rest of the computation", which a handler can resume with a value.
- **Deep vs shallow handler:** a deep handler stays installed when the computation is resumed, so it acts like a fold over all the operations. A shallow handler handles one operation and must re-install itself.
- **Landin's knot:** creating recursion without any recursive definition, by storing a function in mutable state and having it call whatever is stored.
- **Elaboration:** turning the convenient surface language into the small explicit core, by filling in implicit arguments, desugaring pattern matching and so on.
- **Kernel:** a small, simple checker for core terms. The only part that must be correct for proofs to be trusted.
- **Reference semantics:** the language's own definition of evaluation, which every backend must agree with.
- **Normalisation by evaluation (NbE):** comparing types by evaluating them to values and comparing the results.
- **Unification:** working out unknown implicit arguments from how things are used.
- **Erasure:** removing compile-time-only parts (types, proofs) before running or generating JS.
- **Strict positivity:** a rule on data type definitions that prevents a type from being defined in terms of functions that consume itself, which would make the logic inconsistent.
- **Universe:** the "type of types". `Type 0: Type 1: …`. Allowing `Type: Type` permits paradoxes (Girard's).
- **Row polymorphism:** functions that work on any record (or ability set) containing *at least* certain fields.
- **De Bruijn indices:** naming variables by position rather than by name, so renaming doesn't change a term's hash.
