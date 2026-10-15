# Stitchwort: text, `IO` and `main` — design for review

**Status:** draft 1, 15 October 2026. Nothing here is implemented. This document stands alone; references like "DESIGN.md §16" point to the full design document for anyone who has it.

## Background

Stitchwort is a small, strict, pure, dependently typed language, built for fun and to explore ideas. It's implemented in Rust, with a small trusted kernel that re-checks everything the elaborator produces. It extracts to JavaScript, and a playground runs the compiler as WebAssembly. Its main goal is that totality is a real guarantee: a function whose type doesn't mention `Partial` terminates, including everything it calls.

What exists today that matters here:

- **Numbers.** `Nat` *means* `Zero | Succ Nat`, so proofs work by ordinary induction. It's *stored* as one arbitrary-precision value, and a short list of prelude functions (`add`, `mul`, `leq`, …) have native implementations, used when their arguments are literals. Those natives are trusted, listed in the design document, and tested against their definitions on many inputs.
- **Abilities.** Algebraic effects in Unison's style: `a -> {State s | e} b`, direct-style code, deep handlers. They're implemented by translating effectful code into an inductive tree of operations (`Comp`) before the kernel sees it. The kernel's existing positivity and structural-recursion checks then show that handlers terminate, with no extra assumption. The type checker never performs an operation, because an operation is just a node in that tree.
- **JavaScript extraction.** Exported functions get runtime-validated encoders and decoders at the boundary (`Nat` ↔ `bigint`, `List` ↔ arrays, data types ↔ tagged objects). Invalid input throws `StitchwortInputError`.
- **Not yet:** text of any kind, `IO`, a way to run a program, and `Partial` (an open proposal).

This document proposes text, an `IO` ability and `main`: enough to write programs that run, rather than only functions that are tested, proved or extracted.

## Part 1: text

### What other languages do

A short survey shaped the proposal. The design space has four separate axes:

1. what proofs see;
2. what runs;
3. what a "character" is;
4. what is trusted.

| Language | What proofs see | What runs | Character | Trust |
|---|---|---|---|---|
| Lean 4 (until 4.24) | `String` as a structure over `List Char` | UTF-8 byte array | Unicode scalar value | Native operations trusted |
| Lean 4 (4.25, Nov 2025) | `ByteArray` with a proof `IsValidUtf8`; the list view still available | The same | Unicode scalar value | Small: the validity check. The stated reason for the change: to bring "the data model of strings much closer to the actual data representation at runtime" |
| Rocq, classic `string` | An inductive list of 8-bit `ascii` | The same, slowly | Byte | None |
| Rocq, `PrimString` | Opaque, described by `PrimStringAxioms` (round-trip with lists, length, concatenation…) | Native, with a maximum length | Byte | Axioms |
| Agda | Opaque built-in | Native | Unicode | Round-trip lemmas are `trustMe`; decidable equality's "no" case is a postulate |
| Idris 2 | Opaque built-in | Native | Unicode | The head-and-tail view needs `believe_me`, which doesn't reduce in the type checker, so string equalities generally can't be proved by computation |
| Haskell | `String = [Char]`, a linked list of boxed characters | The same | Unicode code point | (not a prover) Widely considered too slow, so real code uses `Text`. `text` 2.0 moved from UTF-16 to UTF-8; one user reported memory halving, and noted that random access becomes linear |
| Swift | `Character` is a grapheme cluster | UTF-8 | Grapheme | (not a prover) Right for user interfaces, but no constant-time indexing, and boundaries depend on the Unicode version |

The pattern: provers that need to reason about strings give them a simple inductive meaning (Rocq classic, Lean until 4.25) or a bytes-plus-validity model (Lean 4.25). Opaque built-ins are fast but push every fact about strings into assumptions (Agda, Rocq `PrimString`) or out of reach (Idris).

The trade-offs, summarised:

| | List of characters | Opaque built-in plus assumptions | Bytes plus validity proof |
|---|---|---|---|
| **Proofs** | Induction and proof by computation, for free | Facts are assumed, or can't be computed | Good for bytes and positions; character-level proofs go through UTF-8 decoding |
| **Trusted base** | Nothing new | Grows with every assumed fact | Small |
| **Speed, run naively** | Slow and large (Haskell's `String`) | Fast | Fast |
| **Model matches what runs?** | No: fast operations need trusted native implementations | Yes | Yes |
| **Work to build** | Low | Low, but every assumption has to be written and trusted | High |

### Proposal

**`Char` is a Unicode scalar value**: a code point from 0 to 0x10FFFF, excluding the surrogates 0xD800–0xDFFF. Not bytes, which aren't Unicode, and not grapheme clusters, which depend on the Unicode version. That would break content-hash caching and proof by computation whenever the tables changed.

```
-- In the prelude.
IsScalar : Nat -> Bool
IsScalar n = leq n 1114111 && not (leq 55296 n && leq n 57343)

type Char : Type =
  | MkChar (code : Nat) (valid : IsScalar code = True)
```

The proof field is erased at runtime. Two `Char`s with the same code are equal, because proofs of `b = True` for a `Bool` `b` are unique (`Bool` has decidable equality).

**`Text` means a list of `Char`s**, wrapped in its own type, so it can cross the JavaScript boundary as a string rather than as an array:

```
type Text : Type =
  | MkText (chars : List Char)
```

**Literals.**
- `'a'` is a `Char`, and `"héllo"` is a `Text`.
- Escapes are `\n`, `\t`, `\\`, `\"`, `\'` and `\u{1F600}`.
- The elaborator turns a literal into constructors, proving each `valid` field by computation.
- An escape that isn't a scalar value (`\u{D800}`) is a compile-time error.

**Operations, in the prelude, defined on the list:**
- joining: `++` (`append`);
- `length` (in characters) and `isEmpty`;
- `==`, through a decision procedure for equality, so `if h : a = b` works too, and ordering;
- `toList` and `fromList`;
- `natToText` and `textToNat` (the latter returning `Maybe Nat`);
- `split`, `join` and `trim`, as library functions.

**No indexing by character position.** Lean leaves it out as "a performance trap". Code that needs positions converts to a list.

**Speed, staged as for `Nat`:**
1. **First, plain lists.** Every proof works from day one, with nothing new trusted. Text is slow for long strings, which a toy language can live with for a while.
2. **Later, compact text.** A text value is stored as one native string in the evaluator, and is the same as its list of characters in the same way `3` is the same as `Succ (Succ (Succ Zero))`. Common operations (`append`, `length`, equality, `natToText`) get native implementations, used when their arguments are literal text. Each is trusted, listed in the design document, and tested against its list definition. No axioms are needed, because the meaning stays the inductive definition, unlike Rocq's `PrimString` and Agda.

**Considered and not chosen:** Lean 4.25's bytes plus validity proof. It's the better long-term design for serious text processing, but it needs a substantial library (UTF-8 validity, character-boundary positions, slices) before simple programs can be written. If Stitchwort ever needs it, the list meaning stays available as a view, as it does in Lean.

### The JavaScript boundary

- `Text` encodes as a JS string. That always succeeds, since every scalar value is representable in UTF-16.
- A JS string decodes to `Text` one code point at a time.
- **A lone surrogate can't be represented as a `Char`**, so a string containing one is refused with `StitchwortInputError`, the same as any other invalid input. (JavaScript strings may contain lone surrogates. WTF-8 exists to carry them losslessly, but its own specification says to convert at system boundaries, which is what this does.)
- `Char` on its own encodes as a one-code-point JS string, and decodes only from one.

## Part 2: `IO` and `main`

### The ability

`IO` is an ordinary ability declared in the prelude, starting small:

```
ability IO where
  print    : Text -> {IO} ()          -- writes a line to standard output
  readLine : () -> {IO} (Maybe Text)  -- Nothing at end of input
```

Because operations are just nodes in a `Comp` tree, **the type checker never performs `IO`** (DESIGN.md principle 2). Elaborating or checking a program that uses `IO` reads no input and writes no output.

### `main` and `stitchwort run`

A program is a file with `main : () -> {IO} ()`, whose row is exactly `{IO}`. Any other ability must be handled inside `main`. `stitchwort run file.sw`:

1. checks the file as usual;
2. evaluates `main ()` to a `Comp` value;
3. loops: on `Done _`, it exits; on `Call op rest`, it performs `op` for real (prints, or reads a line), applies `rest` to the result, and continues.

The loop is iterative, so a long run of operations doesn't grow the Rust stack. The evaluation *between* operations is the reference evaluator, the same one the type checker uses.

### What the guarantee says

DESIGN.md §3 already states it: for host operations, "the guarantee covers the computation between them, not the operations themselves". Here, every step between two operations terminates. Reading may block (a trusted contract).

**A consequence worth stating:** without `Partial`, every program performs a *finite* tree of operations, so there's no unbounded interactive loop (a REPL, a server). A program can read until end of input only if it recurses on something finite. This follows directly from totality, and is one of the motivations for the `Partial` proposal. A bounded loop with explicit fuel (`repl : Nat -> {IO} ()`) works today.

### Handling `IO` in tests

DESIGN.md says only the runtime handles `IO`. **This proposal relaxes that to allow ordinary handlers for `IO`.** A handler is a fold over a finite tree, so a pure handler for `IO` is as sound as any other. It's what makes effectful code testable:

```
-- Runs a program against scripted input, collecting its output.
simulate : List Text -> (() -> {IO | e} a) -> {e} Pair (List Text) a

test "greets" =
  outputOf (simulate ["Ada"] greet) == ["What's your name?", "Hello, Ada"]
```

What stays special is that only `stitchwort run` performs `IO` *for real*. Tests stay pure `Bool`s, as now, and keep their content-hash caching. A test that performs real `IO` couldn't be cached.

### Extraction

For now, exported functions remain pure. A pure export may use `IO` internally only if it handles it, for example with `simulate`. Exporting functions that perform `IO`, with the host supplying the operations, is DESIGN.md's later "effects from the host" item, and is out of scope here.

### The playground

The playground gets a "Run" button. It runs `main` with no input, so `readLine` gives `Nothing`, and shows printed lines in an output pane.

## Build order

1. `Char` and `Text` in the prelude, literals and escapes in the lexer, and the list-defined operations. Tests: literals, escapes, refused escapes, operations against expected values, and equality decided by computation.
2. JavaScript encoders and decoders for `Text` and `Char`. Tests: round trips, lone surrogates refused, non-BMP characters (emoji) round-tripping, and the differential tests (generated JS against the reference evaluator) extended to text.
3. The `IO` ability, `main`, and `stitchwort run` with its loop. Tests: scripted standard input, against expected standard output.
4. `simulate` in the prelude, and a test example using it.
5. The playground's Run button.
6. Later, when it's needed: compact text with native operations, tested against the list definitions.

## Questions for the reviewer

1. **Lists now, compact later, never axioms.** Is starting with `Text` as a plain list of characters, and adding a compact representation with tested native operations later, a sound plan? Or is there a reason to go straight to Lean 4.25's bytes plus validity proof?
2. **`Char` with a proof field.** Is a `Nat` with an erased proof that it's a scalar value the right encoding? Or should `Char` be a primitive type like the compact `Nat`, with literals checked by the kernel?
3. **Relaxing "only the runtime handles `IO`".** Is there a soundness or design reason to keep `IO` unhandleable by user code, given that handlers are ordinary folds over finite trees? (The concern behind the original rule was `Partial`, where a user handler could hide non-termination; that doesn't apply to `IO`.)
4. **`main`'s row.** Should `main` be allowed other abilities that the runtime also provides (say `Random`, or exceptions as `Abort`), or should it be exactly `{IO}` until there's a reason?
5. **Finite programs.** Is it acceptable that, until `Partial` exists, programs can't loop without bound? Or does that argue for prioritising `Partial`?

## Sources

- Lean: [Strings in the reference manual](https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/), [4.25.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/)
- Rocq: [`PrimString`](https://docs.rocq-prover.org/v8.20/stdlib/Coq.Strings.PrimString.html), [`PrimStringAxioms`](https://docs.rocq-prover.org/v8.20/stdlib/Coq.Strings.PrimStringAxioms.html), [classic `String`](https://rocq-prover.org/stdlib/Stdlib.Strings.String.html)
- Agda: [standard library `Data.String`](https://www.cse.chalmers.se/~nad/listings/lib/Data.String.html)
- Idris 2: [`Data.String` source](https://idris-lang.org/Idris2/base/source/Data.String.html), [`Builtin` source](https://www.idris-lang.org/Idris2/prelude/source/Builtin.html)
- Haskell: [`text` 2.0 changelog](https://hackage.haskell.org/package/text-2.0/changelog), [Channable: "So long surrogates"](https://www.channable.com/tech/so-long-surrogatesa)
- Swift: [SE-0363 discussion](https://forums.swift.org/t/se-0363-unicode-for-string-processing/58520/9)
- [The WTF-8 encoding](https://wtf-8.codeberg.page/)
