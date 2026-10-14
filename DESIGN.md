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
| Totality statement | "A closed term whose type has no abilities" | Stated with an effect judgment `t : A ! ε`: building a partial closure is pure, calling it isn't |
| `Prop` elimination | "Fields are all erased" (which wrongly allowed hiding a type) | Lean's rule, stated over the constructor declaration: each field is a proof or appears in the result type's indices |
| Product rules | Unstated | `Prop` is impredicative. Effectful arrows are never in `Prop` |
| Explicit implicit arguments | `map [Nat] [Nat] f xs`, which clashes with list literals | `map [a := Nat] [b := Nat] f xs` |
| Records vs ability rows | "Abilities never contain a colon" | Decided by the top level of the braces only |
| `auto` | Only runs decision procedures | Uses supplied evidence, then hypotheses in scope, then decision procedures |
| Assumptions | Reported by a command | Exports must be assumption-free. Test results show their assumptions automatically |
| `State s` | Any `s` | `s` must be data-only, checked transitively |
| JS exports | "Pure, first-order" | An exportability check: concrete types with codecs, decidable preconditions, assumption-free |
| Numbers | `Int` division and `Float` unspecified | `Int` division truncates toward zero. `Float` is outside the first extraction milestone |
| Caching | Elaboration keyed on dependency "interfaces" | Keyed on whole-declaration hashes. Module identity is logical, not a file path |
| Test harness | Rejection tests must fail | Must fail *with the expected error code*. Differential tests for extraction |

### Changes from draft 1 to draft 2

Draft 1 stated several guarantees more strongly than its rules justified. This draft makes them precise ([§3](#3-precise-guarantees)) and narrows the initial subset to what can actually be justified.

| Area | Draft 1 | Draft 2 |
|---|---|---|
| Universes | `Type : Type`, fix later | Numbered universes in the kernel from day one. `Type : Type` breaks termination, not just logic |
| Handler termination | Trusted if each clause resumes at most once | That rule has counterexamples. Now: deep handlers, first-order operations, non-recursive clauses, recorded as a tracked conjecture |
| `withFuel` | Generic handler for `Partial` | Postponed. Explicit fuel arguments for now. `Partial` can't be handled by user code |
| Erasure | Open question | `Prop`-based, with restricted elimination |
| `auto` | "By computation" | Via a `Decidable` mechanism, which also produces the JS boundary checks |
| Division | `n / 0 = 0` or a proof, undecided | `/` needs a non-zero proof. `divideChecked` returns `Optional` |
| Implicit arguments | `{a : Type}` | `[a : Type]`. `{a : Type}` was ambiguous with a one-field record type |
| JS integers | `number`, checked | `bigint`. Inputs that pass validation could produce outputs a `number` can't represent |
| JS `Optional` | `a \| null` | Tagged. `null` merged `None` and `Some None` |
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

**Assumption-free.** A definition that doesn't depend, directly or indirectly, on any tracked assumption: `assume`, a foreign function declared total, a proof hole, or a conjecture the checker relies on (currently the handler rule in [§8](#8-abilities-and-handlers)). `stitchwort assumptions <name>` lists them.

**Effect judgment.** Internally, the type checker establishes judgments of the form

```
Γ ⊢ t : A ! ε
```

meaning "evaluating `t` produces a value of type `A`, and may perform the abilities in `ε`". The abilities that *evaluating* an expression may perform are different from the abilities mentioned *inside* its type:

```
\() -> spin 0          -- : () -> {Partial} Nat  ! {}         building the closure is pure
(\() -> spin 0) ()     -- : Nat                  ! {Partial}  calling it is partial
```

**Total.** If `⊢ t : A ! {}` is checked and assumption-free, with `t` closed, then evaluating `t` reaches a value in finitely many steps. `A` may itself contain function types with abilities: those apply when the function is called, not when `t` is evaluated. How this extends to other cases:

| Case | What's guaranteed |
|---|---|
| Pure function `f : A -> B` | Applying it to any value of `A` terminates. |
| Function returning a partial closure, `mk : Nat -> (() -> {Partial} Nat)` | Calling `mk` terminates (`mk 3 : … ! {}`). Calling the closure it returns is not covered. |
| Open ability row, `g : A -> {e} B` | Terminates once every ability in `e` is handled by an admissible handler ([§8](#8-abilities-and-handlers)). The handled computation is then covered. |
| `Abort` | May stop without producing a `B`. Once handled (into `Optional B`), covered. |
| `IO` and host-provided operations | Trusted contracts. They may block (waiting for input or the network). The guarantee covers the computation between them, not the operations themselves. |
| Depends on assumptions | The guarantee holds only if the listed assumptions are true. |

"Finitely many steps" doesn't mean "quickly". Tools that run code (tests, the type checker's evaluator, the playground) have resource budgets. Running out of budget is reported as **inconclusive**, never as pass or fail.

**Conditional results are labelled automatically.** Anything that reports success (a test, a theorem, an export) shows the assumptions it depends on, without the user having to run a separate command. Exports are refused outright if they depend on assumptions ([§12](#12-javascript-extraction)).

**Proved.** If a checked, assumption-free theorem `p : P` exists, then `P` holds, assuming the kernel is correct.

**Erased.** A value is erased if it's a type or a proof (its type is in `Prop`, [§6](#6-proofs-universes-and-erasure)). Erased values don't exist at runtime, and the kernel's elimination rules ensure runtime results never depend on them.

**Preserved at the JS boundary.** If decoding and validation of an exported function's inputs succeed, the function returns the encoding of the Stitchwort result for the decoded inputs. This trusts the code generator, the encoders and decoders, the JS engine, and that there is enough memory and stack ([§12](#12-javascript-extraction)).

---

## 4. Language tour

The syntax is whitespace-sensitive and ML/Lean-like. Everything here is a sketch and open to change. Constructor names start with an uppercase letter, which is how patterns tell constructors apart from variables.

### Brackets

| Brackets | Meaning | Example |
|---|---|---|
| `( )` | grouping, explicit arguments | `(xs : List a) -> …` |
| `[x : A]` in a type | implicit argument binder: the compiler fills it in | `[a : Type] -> List a -> Nat` |
| `[auto x : P]` in a type | implicit proof the compiler finds ([§6](#6-proofs-universes-and-erasure)) | `[auto ok : i < length xs]` |
| `[x := e]` in an expression | supplying an implicit argument explicitly, by name | `map [a := Nat] [b := Nat] f xs` |
| `[e, …]` in an expression | list literal | `[1, 2, 3]`, `[x]`, `[]` |
| `{ }` with `name : Type` fields | record types | `{ name : Text, age : Nat }` |
| `{ }` right after an arrow | ability rows | `Nat -> {State Nat} Nat` |

**Square brackets.** In a type, `[` always starts an implicit binder. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list literal, so `length [1]` and `get [10] 0` mean what they look like. The `:=` also keeps `[a := b]` distinct from `[a = b]`, a one-element list containing an equality.

**Curly braces.** Record types and ability rows are told apart by the *top level* of the braces, not by whether a colon appears anywhere inside:

- If the top-level entries have the form `name : Type`, it's a record type.
- Otherwise it's an ability row, whose entries are abilities applied to arguments. Those arguments may themselves contain record types: `Nat -> {State { count : Nat }} Nat` is an ability row containing `State` applied to a record type.
- `{}` is always the empty record type. An empty ability row is never written: a pure arrow has no braces.

These rules get golden parser tests before anything is built on them, including nested and empty cases.

### Data types and pattern matching

```
type Shape =
  | Square (side : Nat)
  | Rect (width : Nat) (height : Nat)

area : Shape -> Nat
area (Square s) = s * s
area (Rect w h) = w * h

-- Lowercase type variables in signatures are bound implicitly.
-- Equivalent to: map : [a : Type] -> [b : Type] -> (a -> b) -> List a -> List b
map : (a -> b) -> List a -> List b
map f []        = []
map f (x :: xs) = f x :: map f xs

doubled = map (\x -> x * 2) [1, 2, 3]                 -- a and b inferred
doubled = map [a := Nat] [b := Nat] (\x -> x * 2) [1, 2, 3]   -- supplied by name
```

### Records

```
type Person = { name : Text, age : Nat }

alice : Person
alice = { name = "Alice", age = 30 }

birthday : Person -> Person
birthday p = { p | age = p.age + 1 }

-- Works on any record that has a `name` field
greet : { name : Text | r } -> Text
greet x = "Hello, " ++ x.name
```

### Totality

```
-- Structural recursion: accepted automatically
length : List a -> Nat
length []        = 0
length (_ :: xs) = 1 + length xs

-- Not structural: name a measure that decreases.
-- `b@(Succ _)` names the argument and records that it isn't zero,
-- which `%` requires.
gcd : Nat -> Nat -> Nat
gcd a 0          = a
gcd a b@(Succ _) = gcd b (a % b)
  decreasing b

-- Opt out: partiality is an ability, visible in the type
collatz : Nat -> {Partial} Nat
collatz 1 = 0
collatz n = 1 + collatz (if even n then n / 2 else 3 * n + 1)
```

### Proofs

```
theorem appendLength : (xs ys : List a) ->
    length (xs ++ ys) = length xs + length ys
appendLength []        ys = rfl
appendLength (x :: xs) ys = cong Succ (appendLength xs ys)

-- The proof that the index is in range is found by `auto`
get : (xs : List a) -> (i : Nat) -> [auto ok : i < length xs] -> a

third = get [10, 20, 30] 2      -- fine: 2 < 3 is decided at compile time
oops  = get [10, 20, 30] 5      -- error: 5 < 3 is false
```

### Data bundled with its guarantees

```
IsSorted : List Nat -> Prop

-- `sorted` is a proof, so it's erased: at runtime this is just a List
type SortedList = { items : List Nat, sorted : IsSorted items }

insert : Nat -> SortedList -> SortedList
insert n s =
  { items  = insertList n s.items
  , sorted = insertPreservesSorted n s.items s.sorted }
```

### Abilities

```
ability State s where
  get : () -> {State s} s
  put : s -> {State s} ()

tick : () -> {State Nat} Nat
tick () =
  let n = get ()
  put (n + 1)
  n
```

### Tests

```
test "reverse twice" =
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
export
applyDiscount : (pct : Nat) -> [auto ok : pct <= 100] -> Price -> Price
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
partial def spin (n : Nat) : Nat := spin n
def innocent (n : Nat) : Nat := spin n + 1   -- accepted as an ordinary def
```

This matches the documented behaviour, though this exact snippet hasn't been run. An ordinary Lean function type such as `Nat → Nat` doesn't certify that its compiled implementation terminates. Stitchwort aims for a stronger link between what the types say and what runs.

### Partiality is an ability

`Partial` appears in function types and spreads to callers:

```
spin : Nat -> {Partial} Nat
spin n = spin n

innocent : Nat -> Nat          -- type error: calls spin, which uses Partial
innocent n = spin n + 1

innocent : Nat -> {Partial} Nat   -- OK: partiality is visible
innocent n = spin n + 1
```

### Rules

1. A recursive definition must pass the termination checker, or have `Partial` in its type.
2. Calling a function whose type has `Partial` adds `Partial` to the caller's abilities.
3. Pattern matches must be **exhaustive**. A missing case is a compile-time error.
4. **Only the runtime handles `Partial`**, at program entry (`main`). No user-written handler can remove it. Otherwise a handler that acknowledges every step could turn an infinite computation into a supposedly total one.
5. Tests may not use `Partial` ([§7](#7-tests)).
6. Foreign functions that might not return must declare `Partial`. Declaring one total is an `assume`, which is tracked.
7. The type checker never evaluates `Partial` code (principle 2).

### Termination checking

Checking is deliberately conservative. It may reject total functions, but it must never accept a non-terminating one.

- **POC:** structural recursion. A recursive call must be on a direct sub-part of a pattern-matched argument.
- **Next:** `decreasing <measure>` clauses for well-founded recursion. The compiler tries to prove the measure decreases with simple arithmetic and asks for a proof if it can't.
- **Later:** handling recursion through higher-order functions (e.g. `map size children` on a rose tree), probably by automatically attaching "this element is in the list" facts, as recent Lean versions do.

When termination checking fails, the error should say *which call* failed and *what it couldn't show*, and suggest `decreasing` or `{Partial}`.

### Fuel

For now, bounded versions of partial algorithms take an explicit fuel argument. They terminate by structural recursion on the fuel, so no special support is needed:

```
collatzFuel : Nat -> Nat -> Optional Nat
collatzFuel 0           _ = None
collatzFuel (Succ fuel) 1 = Some 0
collatzFuel (Succ fuel) n = map (+ 1) (collatzFuel fuel (next n))
```

A generic `withFuel : Nat -> (() -> {Partial | e} a) -> {e} Optional a`, which bounds *any* partial computation, is attractive but postponed. It needs:

- **Ticks in the core semantics.** Every unbounded recursion must pass through a "tick", and the kernel must check this. It can't be optional instrumentation added by the front-end.
- **No opaque divergence.** A foreign function that loops internally can't be interrupted between ticks, so foreign `Partial` must be excluded or treated differently.
- **Specified fuel semantics.** Counting recursive calls and counting evaluation steps give different results, and optimisations must preserve whichever is chosen.

---

## 6. Proofs, universes and erasure

### Proofs

- **Propositions are types; proofs are values.** `xs ++ [] = xs` is a type, and a value of that type is a proof.
- **`theorem`** is a definition whose type is a proposition (in `Prop`). It's always erased at runtime and must be total and pure.
- **Equality** is a built-in proposition `a = b` with `rfl : a = a`, plus library functions `cong`, `sym`, `trans` and `rewrite`.
- **Proof by computation.** Types are compared by evaluating them, so `rfl` proves anything that holds by just computing both sides (`2 + 2 = 4`, `length [1, 2] = 2`).
- **No tactics.** Proofs are ordinary terms, written by pattern matching and recursion. A `calc` block for readable chains of equalities is a likely later addition.

Conventions that make proofs go through by computation should be documented. For example, `+` on `Nat` recurses on its *first* argument, so `Succ m + n` reduces to `Succ (m + n)`.

### Universes

```
Prop   : Type 0
Type 0 : Type 1
Type 1 : Type 2
…
```

- `Type` on its own means `Type 0`, where ordinary data lives.
- The kernel checks universe levels **from the first milestone**. `Type : Type` was rejected because it allows paradoxes (Girard's) that produce non-terminating terms without any recursion, which would break principle 1, not just the logic.
- **No universe polymorphism at first.** Each data type is declared at a fixed level, so `List` holds `Type 0` values. Universe polymorphism and inference come later, and are mostly an elaboration feature.

### Which universe a function type lives in

Having numbered universes doesn't settle where function types live. The rules:

| Function type | Lives in | Note |
|---|---|---|
| `(x : A) -> B`, pure, `B : Prop` | `Prop` | Whatever `A`'s universe. This is **impredicativity**, as in Lean and Rocq: "for every `x : A`, `B x` holds" is itself a proposition |
| `(x : A) -> B`, pure, `A : Type i`, `B : Type j` | `Type (max i j)` | `Prop` counts as level 0 here |
| `(x : A) -> {ε} B`, with a non-empty ability row | `Type (max i j)`, **never** `Prop` | Even when `B` is a proposition |

The last rule matters once abilities exist. In

```
loggedProof : () -> {IO} True
```

the function is runtime data, not an erasable proof: calling it performs IO, and only the `True` it returns is erased. Treating it as a proposition would erase the IO.

### Erasure via `Prop`

A value is erased if its type is in `Prop`. `sorted : IsSorted items` is erased because `IsSorted items : Prop`, not because of its name or where it came from. Types are erased too.

**The restriction that makes this safe:** runtime results must never depend on *which* proof was given, or on data hidden inside a proof. So pattern matching on a proof may only produce something outside `Prop` when the proposition passes this check, which is Lean's rule ("subsingleton elimination"; Rocq's is similar).

The check reads the **inductive declaration itself**, distinguishing its parameters, its indices and each constructor's fields. A proposition may be eliminated into any universe when:

1. it has **at most one constructor**, and
2. every **field** of that constructor (an argument that isn't one of the type's parameters) is either
   - a **proof** (its type is in `Prop`), or
   - a variable that **appears among the indices of the constructor's result type**, so it's determined by the type and carries no hidden information.

Otherwise, matching on it can only produce another proof.

The check is over the declaration. It must **not** be implemented by asking "would the compiler erase this field?", because types are erased but can still carry information:

```
type HiddenType : Prop =
  | HideType (a : Type)

reveal : HiddenType -> Type      -- rejected: `a` is a type, not a proof,
reveal (HideType a) = a          -- and it doesn't appear in an index
```

| Proposition | Can be matched on to produce data? | Why |
|---|---|---|
| `a = b` (constructor `rfl : a = a`) | Yes | No fields. The `a` in `rfl` is a parameter or index, not a field. Needed for transport (rewriting a value's type along an equality) |
| `False` | Yes | No constructors. Needed for ruling out impossible cases (`absurd`) |
| `p ∧ q` | Yes | One constructor, whose fields are proofs |
| `p ∨ q` | **No** | Two constructors: the result could depend on which side was proved |
| `∃ x, p x` | **No** | The witness `x` is data that doesn't appear in an index |
| `HiddenType` | **No** | The field `a : Type` is neither a proof nor an index |

The kernel implements this rule and nothing looser. Each "No" row is a "must reject" test, paired with an accepted test for a nearby "Yes" row ([§13](#13-soundness-policy)). Definitional proof irrelevance (treating any two proofs of the same proposition as equal during type checking) isn't needed for the POC.

Data indices like a vector's length are **not** erased, because they're data, not proofs. That costs some runtime space, which is acceptable since performance isn't a goal. A more general relevance system (Idris 2-style usage annotations) can come later if needed.

### Four separate questions about an argument

These are independent, and the design keeps them so:

| Question | Controlled by |
|---|---|
| Does the caller write it? | Explicit `( )` vs implicit `[ ]` |
| How is it found? | Unification for `[x : A]`. A decision procedure for `[auto x : P]` |
| Does it exist at runtime? | Erased if and only if its type is in `Prop`, or it's a type |
| How often may it be used at runtime? | Unrestricted. (Continuations may later need "at most once" for JS; see [§8](#8-abilities-and-handlers)) |

In particular, an implicit argument isn't automatically erased (`[n : Nat]` exists at runtime), and `auto` doesn't mean erased either.

### `auto` and `Decidable`

`[auto ok : p]` asks the compiler to find a proof of `p`. Evaluating `2 < 3` to `true` doesn't by itself produce a proof, so `auto` uses decision procedures, values of this type:

```
type Decidable (p : Prop) : Type =
  | Yes (proof : p)
  | No  (refutation : Not p)
```

`Decidable p` lives in `Type`, not `Prop`: whether the answer is `Yes` or `No` is runtime data. Only the proof inside each branch is erased.

To fill in `[auto ok : p]`, the compiler tries, in order:

1. **Evidence supplied explicitly**: `[ok := myProof]`.
2. **A hypothesis already in scope** whose type matches `p`, e.g. the `h` from `if h : d != 0 then …`. This is simple matching against the local context, not general proof search.
3. **A registered decision procedure** for `p`, evaluated at compile time.

Possible outcomes, each with its own error message:

| Outcome | Result |
|---|---|
| Evidence found, or the decision procedure says `Yes proof` | Uses that proof |
| The decision procedure says `No` | Error: `p` is false |
| The decision procedure is stuck, because its inputs aren't known at compile time | Error: supply a proof, or establish it with a branch (`if h : i < length xs then … else …`) |
| No decision procedure is registered for `p` | Error: no way to decide `p` |
| The budget ran out | Inconclusive: try a larger budget |

**The same decision procedure has two uses.** It can run during elaboration when its inputs are known well enough, or be compiled into a runtime check at the JS boundary ([§12](#12-javascript-extraction)). A predicate can have a perfectly good decision procedure that's stuck at compile time on symbolic inputs. That's exactly the case where a runtime check is useful.

### Dependent pattern matching

Pattern matching in proofs requires the compiler to learn facts about types in each branch. In full generality this is one of the hardest parts of any dependently-typed language. **For the POC, patterns are kept simple:** one constructor deep, with no overlapping or nested patterns, which then get compiled into a series of simple `case` expressions. That's enough for the standard proofs about lists and numbers. Nested patterns can be added later.

### Effects and dependent types

The rule (principle 2) is about **executing** effects, not mentioning them:

- `f : (n : Nat) -> {IO} Vec Nat n` is fine. The result type `Vec Nat n` is pure, even though calling `f` performs IO.
- A type expression that would itself *perform* an operation (e.g. `Vec Nat (readNat ())`) is rejected. During type checking, effectful applications never reduce.
- When an effect's result is later used as an index (`let n = readNat ()` and then `Vec Nat n`), `n` is just a variable as far as the type is concerned. The precise rules for sequencing effectful code with dependent types are an open question ([§16](#16-open-questions)).

### Running vs comparing

The type checker and the program runner share an evaluator, but use it with **different policies**:

| | Running a program | Comparing types |
|---|---|---|
| Goal | Reach a value | Reach a normal form, so two types can be compared |
| Goes inside `\x -> …`? | No | Yes |
| Reduces effectful applications (including `Partial`)? | Yes, via handlers | **Never**. They stay as stuck terms |
| Budget | Per run | Per check. Running out is inconclusive |

The core typing rules will state exactly which terms the comparison is allowed to reduce, since that's what keeps type checking terminating once partial closures exist.

---

## 7. Tests

A test is a named, closed expression of type `Bool` that must be checked, total and pure:

```
test "tick twice" =
  runState 0 (\() -> tick (); tick ()) == (1, 2)
```

Running it to `true` checks `expr = true` by computation, so a passing test is a proof of one specific fact. Tests and theorems are cached in the same way ([§11](#11-content-hashing-and-caching)).

- **Outcomes:** pass, fail, or **inconclusive** (the resource budget ran out). A checked test can't diverge in the reference semantics, but it can take impractically long. An inconclusive result is never cached as a failure: running again with a larger budget retries it.
- **No `Partial`** in tests. Partial algorithms are tested through their explicit-fuel versions.
- **Effectful code is tested via pure handlers**, like `runState` above.
- **Assumptions are shown with the result.** `tick twice` goes through `runState`, whose termination relies on the handler conjecture ([§8](#8-abilities-and-handlers)). So it reports as conditional, not as an assumption-free proof:

  ```
  ✓ reverse twice          passed
  ✓ tick twice             passed, assuming: handler-termination
  ```

### Property tests (later)

`forall xs. reverse (reverse xs) == xs`, checked on random inputs, sits between tests and theorems. When added:

- The cache key includes the generator, sample count, size schedule, seed and configuration, not just the seed.
- "Replay these known samples" and "search for new counterexamples" are separate commands.
- The UI presents a passing property test as **evidence about the sampled cases**, never as a theorem.

---

## 8. Abilities and handlers

Abilities follow Unison's design, which comes from Frank.

- **Direct style.** Effectful code reads like ordinary code (`let n = get ()`), with no `do`-notation or monads.
- **Ability rows on arrows.** `a -> {State s, IO} b`. A plain arrow `a -> b` means pure *and* total.
- **Ability polymorphism with row variables.** `{State s | e}` means "State, plus whatever else `e` is".

### Deep handlers

Handlers are **deep**: the continuation `k` already includes the handler, so a clause never needs to call the handler again. That makes a handler a *fold* over the tree of operations a computation performs:

```
runState : [auto d : IsData s] -> s -> (() -> {State s | e} a) -> {e} (a, s)
runState init prog =
  let run =
    handle prog () with
      | return x     -> \s -> (x, s)
      | get ()  => k -> \s -> k s s
      | put s'  => k -> \_ -> k () s'
  run init
```

Each clause returns a function waiting for the current state. `k s` resumes the computation with result `s`, giving back another such function, which is then applied to the state.

The `IsData s` constraint is explained under rule 2 below.

### When handlers are trusted to terminate

Draft 1 proposed trusting any handler that resumes `k` at most once. **That rule is wrong.** These two counterexamples are now in the "must reject" suite.

*The handler restarts the computation instead of resuming it:*

```
ability Ping where
  ping : () -> {Ping} ()

bad : (() -> {Ping} a) -> a
bad prog =
  handle prog () with
    | return x     -> x
    | ping () => k -> bad prog     -- never resumes k, loops forever

bad (\() -> ping ())
```

*Landin's knot: storing a function that reads itself back:*

```
ability Cell where
  read  : () -> {Cell} (() -> {Cell} ())
  write : (() -> {Cell} ()) -> {Cell} ()

knot : () -> {Cell} ()
knot () =
  let f = \() -> (read ()) ()
  write f
  f ()           -- f reads f and calls it, forever
```

Each continuation here is resumed exactly once. The recursion comes from the stored function, not from the handler. Koka's design makes the same point: higher-order mutable state can cause divergence that a check for syntactic recursion can't see.

**POC rule.** A handler is admissible when:

1. **It's deep, and its clauses aren't recursive.** A clause can't call the handler or any function that leads back to it. The only way to continue is `k`. This rejects `Ping`.
2. **Its ability's operations are data-only.** Operation arguments and results can't contain functions, anywhere. This rejects `Cell`. It's checked **transitively, after type parameters are filled in**, not just by looking for `->` in the operation's signature, because a function can hide inside a constructor or record. So `State Nat` is fine, but `State (List (Nat -> Nat))` and `State { f : Nat -> Nat }` are rejected. For parameterised abilities like `State s`, the handler must require `IsData s`, a property of types that the compiler decides by looking through their definitions. Without that, `runState` could be used with function-valued state and reintroduce Landin's knot.
3. **Its clauses are total and pure** apart from the outer row `e`.
4. **It isn't for `Partial`** ([§5](#5-totality-and-partiality)).

**Conjecture.** An admissible handler terminates, *whether or not* it resumes `k` more than once. The argument has two parts:

1. **The computation:** under these typing and termination rules, an effectful computation corresponds to a *well-founded* tree of operations. Every path through it is finite, and data-only operations can't smuggle in recursion.
2. **The handling:** an admissible deep handler is a fold over such a tree with total clauses, so it doesn't introduce divergence of its own.

Splitting it this way avoids assuming "the computation is total" before totality has been defined for open, effectful computations, and shows that the restrictions on operations belong to part 1. This is an argument, not yet a proof. Until it's written up properly, it's a **tracked assumption** (principle 3): results that rely on a handler show it ([§3](#3-precise-guarantees)). Built-in handlers like `runState` and `runAbort` might get their own specific arguments later, so they no longer depend on the general conjecture.

**Operational semantics to pin down before milestone 7.** "Deep" isn't a complete specification. Before implementing handlers, the core rules must say:

- whether a clause runs *inside* or *outside* the handler it belongs to (i.e. what happens if a clause itself performs an operation of the ability being handled);
- how operations the handler doesn't handle are forwarded to outer handlers;
- the exact type of the continuation `k`.

Resuming more than once doesn't by itself cause divergence. Exploring both branches of a finite tree terminates.

**"At most once" is a separate concern.** Compiling handlers to JS generators ([§12](#12-javascript-extraction)) requires each continuation to be resumed at most once *at runtime*, including through closures and helper functions, so counting occurrences of `k` in the source isn't enough. This only matters when handlers are extracted to JS, which comes after the first extraction milestone. It's not part of the termination argument.

### Built-in abilities

| Ability | Purpose |
|---|---|
| `Partial` | Might not terminate ([§5](#5-totality-and-partiality)). Handled only by the runtime |
| `IO` | Console, files, etc. Handled only by the runtime, at `main`. A trusted contract that may block |
| `Abort` | Stop early. Handled into `Optional` or `Either` |
| `State s` | State, handled purely. `s` must be data-only |

---

## 9. Records

Records come in two kinds, kept separate at first.

### Row-polymorphic records

- **Structural.** `{ name : Text, age : Nat }` is a type in its own right. `type Person = …` just gives it a name.
- **Row polymorphic.** `{ name : Text | r }` accepts any record with at least a `name` field.
- **Conveniences:** update syntax `{ p | age = p.age + 1 }`, field punning `{ name, age }`, and `.age` as an accessor function.
- **No dependencies between fields.**

### Dependent records

- **Closed and ordered.** Later fields may refer to earlier ones: `{ items : List Nat, sorted : IsSorted items }`. Field order matters, and there's no row variable.
- **Updates must re-establish dependent fields.** For `s : SortedList`, `{ s | items = [2, 1] }` is a type error, because `s.sorted` proves something about the *old* `items`. An update that changes a field must also supply every later field whose type depends on it:

  ```
  { s | items = xs', sorted = proofAbout xs' }
  ```
- **Proof fields are erased** at runtime.

### Nominal types

- **Data types (`type … = | …`) are nominal**: two declarations with the same constructors are still different types.
- To keep IDs apart, use single-constructor data types instead of nominal records:

  ```
  type UserId  = UserId Nat
  type OrderId = OrderId Nat
  ```

---

## 10. Numbers

- `Nat` and `Int` are arbitrary-precision integers.
- **Division and remainder need a non-zero divisor.** `/` and `%` take an implicit proof `[auto ok : d != 0]`. For literal divisors (`n / 2`) or divisors matched as `Succ _`, the compiler finds it automatically. For unknown divisors there are two routes:
  - establish the fact with a branch (`if h : d != 0 then n / d else …`), or
  - use `divideChecked : Nat -> Nat -> Optional Nat` (and `remainderChecked`).

  The laws of `/` and `%` (e.g. `a % b < b` when `b != 0`) are part of the standard library, since proofs like `gcd`'s termination depend on them.
- **`Nat` subtraction stops at zero** (`3 - 5 = 0`), documented prominently, with `subtractChecked : Nat -> Nat -> Optional Nat` as the alternative. Code that needs negative results should use `Int`.
- **`Int` division truncates toward zero**, and the remainder has the sign of the dividend: `(-7) / 3 = -2` and `(-7) % 3 = -1`. This matches JS `BigInt` (and Rust, C and Java), so extracted code can use the native operators directly. The defining law, `(a / b) * b + a % b = a` with `|a % b| < |b|`, is in the standard library. Floor or Euclidean division can be added later as separately named functions.
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

**Recursive groups.** A recursive function refers to itself, and mutually recursive functions refer to each other, so they can't be hashed one at a time with their dependencies first. Each group of mutually recursive definitions is hashed as a unit, with members referring to each other by their index within the group. This follows Unison's cycle hashing.

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

Every key also includes the compiler version.

The elaboration key must use dependencies' full hashes, bodies included, not just their signatures. If `bound : Nat` changes from `3` to `4`, its signature is the same, but elaborating something of type `Vec Nat bound`, or deciding an `auto` proof involving `bound`, can give a different result. Tracking exactly which definitions elaboration looked inside would allow finer-grained keys, but whole-declaration hashes are simpler and always correct. Adding or changing a decision procedure can also change what `auto` finds, so that's part of the key too.

In the POC only the core-hash layers exist, so **elaboration always re-runs**. What's skipped is kernel re-checking, test runs and code generation. That's still the expensive part for proofs and tests.

**Inconclusive results are never cached** as rejections or failures. A larger budget always retries.

### Cache trust

A content hash identifies an object, but doesn't prove it was checked. The policy:

- The **local** cache (`.stitchwort/cache/`, or IndexedDB in the playground) is trusted. A cached kernel success counts as "checked" ([§3](#3-precise-guarantees)).
- `stitchwort check --no-cache` re-checks everything from scratch.
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
2. **Concrete boundary types with codecs.** Every input and output type is fully concrete (no type parameters such as `identity : [a : Type] -> a -> a`), and has a supported encoder and decoder: `Nat`, `Int`, `Bool`, `Text`, `List`, `Optional`, records and data types built from these. No functions, no `Float`. Polymorphic helpers are fine *inside* the library, just not at the boundary.
3. **Decidable preconditions.** Every erased proof argument of the exported function has a registered decision procedure ([§6](#6-proofs-universes-and-erasure)), which becomes a runtime check.
4. **Assumption-free.** The exported function, everything it depends on, *and the decision procedures used by its validators* are assumption-free ([§3](#3-precise-guarantees)). Otherwise an assumed proof hidden inside a decision procedure could let invalid input through as validated, and an assumed falsehood can make extracted code wrong or non-terminating even though the assumption itself is erased. (Rocq's extraction documentation warns about exactly this.) For example, this is refused:

   ```
   assume impossible : False

   export
   bogus : Nat -> Nat
   bogus n = absurd impossible
   ```

   An explicit experimental flag (`--allow-assumptions`) could permit assumptions later. It would emit a manifest listing them and make the guarantee explicitly conditional.

Host-provided abilities, exporting handlers, and functions as arguments come later.

### The contract

Each exported function is wrapped like this:

1. **Decode** every input into a fresh internal representation that the wrapper owns, reading each property exactly once. After this, the original JS objects are never read again, so mutating them (even through another reference) can't affect the result. TypeScript's `readonly` doesn't prevent mutation at runtime.
2. **Validate** the decoded value: its shape, and any decidable preconditions (e.g. `pct <= 100`). Invalid input throws a `StitchwortInputError` saying what was wrong.
3. **Compute** with the extracted Stitchwort code.
4. **Encode** the result back into JS values. Encoding is lossless, so it can't fail.

**The guarantee** ([§3](#3-precise-guarantees)): if decoding and validation succeed, the function returns the encoding of the Stitchwort result for the decoded inputs. The trusted parts are the code generator, the **encoders and decoders**, the JS engine, and enough memory and stack.

The guarantee starts *after* decoding succeeds. It makes no promise that decoding an arbitrary hostile JS object terminates or succeeds: a getter can loop or throw, and a structure can be cyclic. Decoder tests cover cyclic inputs and getter-backed properties, so these fail cleanly where possible.

### Boundary representations

| Stitchwort | TypeScript at the boundary |
|---|---|
| `Nat` | `bigint` (decoding rejects negative values) |
| `Int` | `bigint` |
| `Bool` | `boolean` |
| `Text` | `string` |
| `List a` | `readonly A[]` (copied on decode; `readonly` is only a hint to TS callers) |
| `{ name : Text, age : Nat }` | `{ readonly name: string; readonly age: bigint }` |
| `Optional a` | `{ tag: "None" } \| { tag: "Some"; value: A }` |
| sum type `Square … \| Rect …` | `{ tag: "Square"; side: bigint } \| { tag: "Rect"; … }` (exported constructors must name their fields) |
| proof arguments and fields | omitted |
| functions, abilities, `Float`, type parameters | not exportable yet |

Notes:

- **Integers are `bigint`** for now. With `number`, an input that passes validation could produce an output too large to represent exactly: `addTwo 9007199254740991` would give `9007199254740993`, which a JS `number` can't hold. Plain-`number` options (via bounded types) can come later. `Int` division and remainder are defined to match `BigInt`'s ([§10](#10-numbers)).
- **`Optional` is tagged.** Mapping it to `A | null` would make `None` and `Some None` both `null` for `Optional (Optional Nat)`. A `null`-based encoding can be added later as an optimisation where the payload can never itself be `null`.
- **`Text`**: if `Text` is defined as a sequence of Unicode characters (scalar values), decoding must reject JS strings containing unpaired surrogates, which JS allows. To be decided along with `Text`'s definition.

### Code generation

1. **Erase** types, proofs and proof fields.
2. **Lower** to a small untyped IR: functions, constructors, `case`.
3. **Generate JS**, with tail calls turned into loops.
4. **Wrap** each `export` with the decode → validate → compute → encode steps.
5. **Emit** `.d.ts` from the Stitchwort types.

### Caveats

- **Stack depth.** JS engines generally don't optimise tail calls. Tail recursion becomes loops. Deep non-tail recursion can still overflow the stack, and the guarantee doesn't cover that.
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
| **Numbered universes** in the kernel | `Type : Type` allows paradoxes that break both proofs and termination. |
| **`Prop` elimination rules** | Runtime results can't depend on erased proofs. |
| **Strict positivity check** on data types | Without it, `type Bad = MkBad (Bad -> Void)` lets you prove anything. |
| **Exhaustiveness checking** of pattern matches | A missing case is a hidden crash. |
| **Conservative termination checking** | Rejecting too much is safe. It can be relaxed later without breaking anything. |
| **Checking never runs effects** | Principle 2. |
| **Tracked assumptions** | `stitchwort assumptions <name>` lists every `assume`, foreign function, proof hole and conjecture a definition depends on. |
| **A "must reject" test suite** | Readable example programs that must fail to type-check. |

### The "must reject" suite

Each rejected example is paired with a nearby example that must be **accepted**, so a check can't pass by rejecting everything.

| Must be rejected | Because | Paired accepted example |
|---|---|---|
| Non-positive data type (`MkBad (Bad -> Void)`) | Positivity check | A positive recursive type (`List`) |
| Girard / Hurkens paradox | Universe levels | A function quantifying over `Type 0` values |
| A total function calling a `Partial` one | Ability checking | The same function declared `{Partial}` |
| A missing pattern-match case | Exhaustiveness | The complete match |
| Matching on `p ∨ q` to produce data | `Prop` elimination | Matching on `p ∧ q` to produce data |
| Extracting the witness of `∃ x, p x` as data | `Prop` elimination | Using the witness inside another proof |
| `reveal : HiddenType -> Type` ([§6](#6-proofs-universes-and-erasure)) | `Prop` elimination: a type field isn't a proof | Transport along `a = b` |
| `loggedProof : () -> {IO} True` treated as erasable | Effectful arrows are never in `Prop` | Erasing the `True` it returns |
| `n / d` with nothing known about `d` | No evidence for `d != 0` | `if h : d != 0 then n / d else 0` |
| `Ping`: a handler restarting its computation ([§8](#8-abilities-and-handlers)) | Handler clauses can't recurse | A handler that only resumes `k` |
| Landin's knot through `Cell` ([§8](#8-abilities-and-handlers)) | Operations must be data-only | `State Nat` |
| `runState` with `State (List (Nat -> Nat))` | `IsData` checked transitively | `runState` with `State (List Nat)` |
| A user handler for `Partial` | Only the runtime handles `Partial` | Running `Partial` code from `main` |
| Updating `items` of a `SortedList` without a new proof | Dependent record updates | Supplying `items` and a new `sorted` proof |
| Exporting `bogus` (depends on `assume impossible : False`) | Exports must be assumption-free | Exporting an assumption-free function |
| Exporting `identity : [a : Type] -> a -> a` | No codec for an unknown type | Exporting `identity` specialised to `Nat` |

**A rejection only counts if it's for the right reason.** Every diagnostic has a stable error code (e.g. `E-POSITIVITY`), and each "must reject" example declares the code it expects. A crash, a timeout, a syntax error in the example, or an unrelated error (like an unknown name) is a test failure, not a pass.

### Known gaps

| Gap | Status |
|---|---|
| **Handler termination** | A conjecture ([§8](#8-abilities-and-handlers)), shown as a tracked assumption until written up properly. |
| **Extractor and encoders/decoders** | Trusted, not verified. Rocq's extraction has the same caveat. |
| **Local cache** | Trusted ([§11](#11-content-hashing-and-caching)). `--no-cache` re-checks everything. |

---

## 14. Implementation

**Current state:** milestones 1–4 are implemented, and milestone 5 in part: tests, declaration hashes and a test-result cache, but not yet caching kernel checks or generated JS, nor resource budgets. The elaborator and kernel are separate, as principle 4 requires. [`docs/core.md`](docs/core.md) gives the core rules as implemented, including where the implementation still differs from this document. [`docs/syntax.md`](docs/syntax.md) describes the implemented syntax.

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
| 2 | **Data types, pattern matching, totality.** `Nat`, `List`, structural recursion, positivity and exhaustiveness checks, `Prop` elimination, `rfl`/`cong` | `appendLength` checks. Non-terminating functions, non-positive types, `∨`-elimination into data and `HiddenType` are rejected, each for the right reason |
| 3 | **Implicit arguments and `auto`.** Unification, implicitly bound type variables, `[a := …]`, `Decidable`, local hypotheses, `/` with non-zero proofs | Write `map f xs` instead of `map [a := Nat] [b := Nat] f xs`. `get [10, 20, 30] 5` is a compile-time error. `if h : d != 0 then n / d else 0` checks |
| 4 | **JS extraction, first-order subset.** Erasure, codegen, `bigint`, tagged encodings, the exportability check, decode/validate wrappers, `.d.ts`, differential tests | Prove a function, extract it, call it from a TS file, and see its results agree with the reference evaluator. Invalid input is rejected at the boundary |
| 5 | **Hashing and caching.** Declaration hashes, recursive groups, nominal identity, kernel/test/JS caches | `stitchwort test` shows `cached` vs `ran` as you edit |
| 6 | **Browser playground.** Compiler as WASM, editor, run/test/extract buttons, resource budgets | A link you can send to people |
| 7 | **Abilities.** First, written operational semantics for handlers ([§8](#8-abilities-and-handlers)). Then deep handlers with the admissibility rules, `IsData`, `State`, `Abort`, `IO`, `Partial` (runtime only) | Effectful code tested through pure handlers, with its assumptions shown. `Ping`, `Cell` and function-valued state are rejected |
| 8 | **Records.** Row-polymorphic records, closed dependent records with checked updates | The record examples from [§4](#4-language-tour) |

**Later:** universe polymorphism, generic `withFuel`, host-provided abilities and handlers in JS, property tests, fixed-size numbers, the source-level elaboration cache, `number` representations at the JS boundary.

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
5. **`Text`** (milestone 4). Unicode scalar values or something else, and what that means for JS decoding.
6. **Handler admissibility** (milestone 7). Write up the two-part conjecture in [§8](#8-abilities-and-handlers) properly. Is "data-only operations" too restrictive in practice?
7. **Handler operational semantics** (milestone 7). The points listed in [§8](#8-abilities-and-handlers).
8. **Effects and dependency.** The precise typing rules for sequencing effectful code when its results are used as type indices.
9. **Runtime "at most once" for continuations.** How to check it, including through closures, for when handlers are extracted to JS.
10. **Generic `withFuel`.** What representation of partial computation makes it sound ([§5](#5-totality-and-partiality))?
11. **`Float`.** Its semantics, and whether it can ever be exported.

### Syntax

12. **Implicitly bound variables.** Only lowercase *type* variables in signatures are bound automatically. Value-level indices never are, so a misspelt index name is an error rather than a silent new parameter. Is that the right line?

### Naming

13. **CLI name.** `stitchwort` is long. `stitch` clashes with an existing program-synthesis tool called Stitch. Maybe `sw`, `wort`, or something else?

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
- **Effect judgment (`t : A ! ε`):** "evaluating `t` produces an `A` and may perform the abilities in `ε`". Separate from any abilities mentioned inside `A`.
- **`IsData`:** a property of types meaning "contains no functions, however deeply nested". Required for state handlers.
- **Parameter / index / field:** in a declaration like `type Vec (a : Type) : Nat -> Type`, `a` is a parameter (fixed across all constructors), the `Nat` is an index (can differ between constructors), and constructor arguments are fields.
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
- **Universe:** the "type of types". `Type 0 : Type 1 : …`. Allowing `Type : Type` permits paradoxes (Girard's).
- **Row polymorphism:** functions that work on any record (or ability set) containing *at least* certain fields.
- **De Bruijn indices:** naming variables by position rather than by name, so renaming doesn't change a term's hash.
