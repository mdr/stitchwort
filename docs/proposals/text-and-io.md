# Stitchwort: text, `IO` and `main`

**Status:** draft 2, 15 October 2026. Accepted after review; nothing is implemented yet. [Acceptance criteria](#acceptance-criteria) lists what the first milestone must show.

## Changes since draft 1

Draft 1 was reviewed. The review accepted the representation and the five proposals, and asked for a precise contract for what text means, which every evaluator, codec and optimisation must preserve. In response:

- **The contract for text** is stated: exact scalar sequences, with equality, length and ordering defined on them, and no normalisation anywhere.
- **Two kinds of optimisation are separated.** Compact text in *generated JavaScript* comes before compact text in the *checking evaluator*. "No axioms" is corrected to "no new logical axioms; native reductions are extra trusted implementations".
- **`Char`** gets conversion functions and a *checked* extensionality lemma, `charExt`, which its equality is built on. Kernel tests reject malformed `MkChar` terms.
- **Traversal** is through `uncons` and a fold, not only through conversion to a list.
- **`trim`, `textToNat` and `split`** have exact specifications instead of host behaviour.
- **The JavaScript boundary** states both round-trip laws, and what decoding a `Char` requires.
- **The real `IO` interpreter** has a contract for input decoding, line endings, end of input and errors. The simulator comes first, as the runner's reference.
- **Corrections:**
  - programs perform a *well-founded*, not finite, tree of operations;
  - an iterative runner doesn't make the whole evaluator stack-safe;
  - the survey overstated the alternatives' weaknesses, and the reason given for excluding graphemes was too strong;
  - the WTF-8 justification for strict decoding was a misreading.

## Background

Stitchwort is a small, strict, pure, dependently typed language, built for fun and to explore ideas. It's implemented in Rust, with a small trusted kernel that re-checks everything the elaborator produces. It extracts to JavaScript, and a playground runs the compiler as WebAssembly. Its main goal is that totality is a real guarantee: a function whose type doesn't mention `Partial` terminates, including everything it calls.

What exists today that matters here:

- **Numbers.** `Nat` *means* `Zero | Succ Nat`, so proofs work by ordinary induction. It's *stored* as one arbitrary-precision value. A short list of prelude functions have native implementations used during evaluation; they're trusted, listed in the design document, and tested against their definitions with the natives switched off.
- **Abilities.** Algebraic effects in Unison's style: `a -> {State s | e} b`, direct-style code, deep handlers. Effectful code is translated into an inductive tree of operations (`Comp`) before the kernel sees it, so the kernel's positivity and structural-recursion checks show that handlers terminate. The type checker never performs an operation, because an operation is just a node in that tree.
- **JavaScript extraction.** Exported functions get runtime-validated encoders and decoders at the boundary. Invalid input throws `StitchwortInputError`.

## Part 1: text

### What other languages do

The design space has four separate axes:

1. what proofs see;
2. what runs;
3. what a "character" is;
4. what's trusted.

| Language | What proofs see | What runs | Character |
|---|---|---|---|
| Lean 4 (until 4.24) | A structure over `List Char` | UTF-8 byte array | Unicode scalar value |
| Lean 4 (4.25, Nov 2025) | `ByteArray` with a proof `IsValidUtf8`; the list view is still available | The same | Unicode scalar value |
| Rocq, classic `string` | An inductive list of 8-bit `ascii` | The same | Byte |
| Rocq, `PrimString` | Opaque, specified by axioms in `PrimStringAxioms` | Native, with a maximum length | Byte |
| Agda | Opaque built-in; round-trip lemmas are `trustMe` | Native | Unicode |
| Idris 2 | Opaque built-in; the head-and-tail view uses `believe_me` | Native | Unicode |
| Haskell | `String = [Char]`; real code uses `Text` (UTF-8 since `text` 2.0) | List, or array | Code point |
| Swift | `Character` is a grapheme cluster | UTF-8 | Grapheme |

Each approach is workable:
- **Opaque types with axiomatised specifications** let further facts be *derived* from those axioms.
- **Lean's 4.25 change** moved the model closer to what runs, in the release notes' words "much closer to the actual data representation at runtime". That alone doesn't make its trusted implementation small.

The case for Stitchwort's choice is simpler: **a list of characters reuses machinery we already have** (lists, induction, decision procedures, extraction), and gives every operation a straightforward definition.

### The contract

**Text is an arbitrary sequence of Unicode scalar values.**
- Equality compares that sequence exactly.
- Length counts scalar values.
- Ordering is lexicographic by scalar numeric value.
- None of these operations normalises text or interprets it by locale.

Specification tests:

```
length "\u{E9}"        == 1
length "e\u{301}"      == 2
"\u{E9}" == "e\u{301}"     -- False: canonically equivalent, but different sequences
length "\u{1F600}"     == 1
"\u{10000}" < "\u{E000}"   -- False (JavaScript's own comparison says true)
```

Normalisation, if it's ever added, is a separately named operation, never part of equality, decoding or literals. Silently normalising `append` would break `length (a ++ b) = length a + length b`, since normalised strings aren't closed under concatenation.

**Scalar values give the core a simple, stable meaning.** Grapheme segmentation and other operations defined by versioned Unicode tables belong in libraries, with their algorithms and tables as explicit dependencies. When those change, the affected definitions get new content hashes and are rechecked. That's ordinary cache invalidation. The real risk would be *untracked* host behaviour, such as the evaluator and the generated JavaScript using different Unicode data.

### `Char`

A Unicode scalar value: a code point from 0 to 0x10FFFF, excluding the surrogates 0xD800–0xDFFF. Reserved, private-use and noncharacter code points, and NUL, are all included, as in Rust's `char`.

```
IsScalar : Nat -> Bool
IsScalar n = leq n 1114111 && not (leq 55296 n && leq n 57343)

type Char : Type =
  | MkChar (code : Nat) (valid : IsScalar code = True)

charToNat   : Char -> Nat
charFromNat : Nat -> Maybe Char

-- Checked, not assumed: proofs of `b = True` for a `Bool` are unique
-- (Bool's equality is decidable).
theorem charExt : (x y : Char) -> charToNat x = charToNat y -> x = y
```

- **Equality is built on `charExt`.** Its decision procedure compares codes, and in the `Yes` case builds the proof that the two `Char`s are equal from `charExt`. Comparing codes gives the right `Bool`; proving the dependent constructor values equal is a separate step.
- **Literals.** The elaborator proves `valid` for a literal by computation, and the kernel re-checks it, so `Char` doesn't need to be a primitive type for malformed literals to be rejected.
- **Propositional versus definitional equality.** That proofs are unique is a theorem. It doesn't let the evaluator discard or replace proof terms during conversion, because the kernel has no definitional proof irrelevance. A compact `Char` representation, if one is ever needed, will need separate treatment of its proof field.

### `Text` and its operations

```
type Text : Type =
  | MkText (chars : List Char)
```

`Text` wraps the list in its own type so it can cross the JavaScript boundary as a string rather than an array.

**Literals:**
- `'a'` is a `Char`, and `"héllo"` is a `Text`.
- Escapes are `\n`, `\t`, `\\`, `\"`, `\'` and `\u{…}`, with 1–6 hex digits.
- An escape that isn't a scalar value (`\u{D800}`, `\u{110000}`) is a compile-time error.

**Operations, defined on the list:**
- `append` (written `++`), `length` and `isEmpty`;
- `==` and `if h : a = b`, through a decision procedure built on `charExt`;
- `compare`, lexicographic by scalar value;
- `toList` and `fromList`, with round-trip lemmas proved: `toList (fromList cs) = cs` and `fromList (toList t) = t`. Proofs that go through these lemmas, rather than relying on the constructor, will survive a later change of representation;
- **traversal** with `uncons : Text -> Maybe (Pair Char Text)` and a fold. There's no indexing by character position: code that needs positions converts to a list;
- `natToText` and `textToNat`, `trim`, and `split` and `join`, as specified next.

**Exact specifications, not host behaviour:**
- **Whitespace** for `trim` is a fixed, small set: space, `\t`, `\n`, `\r`, and U+000B, U+000C. It isn't Rust's or ECMAScript's notion of whitespace, which differ from each other. A Unicode `White_Space` version, with its table pinned, can be a separate library function.
- **`textToNat`** accepts a non-empty sequence of ASCII digits `0`–`9`, consuming all of the input. Leading zeros are allowed; signs, whitespace and separators aren't. Otherwise it returns `Nothing`. The law is `textToNat (natToText n) = Just n`. The reverse doesn't hold, because `"007"` reads as 7.
- **`split`** takes a `Char` separator and keeps empty fields: splitting `"a,,b"` on `,` gives `["a", "", "b"]`, and splitting `""` gives `[""]`. The law is `join c (split c t) = t`. Splitting on a `Char` rather than a `Text` sidesteps the empty-separator question, and makes the structural recursion obvious.

### Making it fast, in stages

1. **Plain lists.** Everything above, with nothing new trusted. Text is slow for long strings, which a toy language can live with for a while.
2. **Compact text in generated JavaScript.** Extracted code represents `Text` as a JS string and implements selected operations natively. This adds to the *extraction* correctness obligation, which is already trusted, but not to proof checking. The JS implementations must use scalar semantics, not code units. In particular:
   - `length` counts code points of well-formed strings, not `.length`;
   - ordering compares scalars, not UTF-16 units;
   - `uncons` and `split` never cut a surrogate pair, so not `slice(1)` or `split("")`.
3. **Compact text in the checking evaluator**, only if type checking needs it. Native reductions there join the trusted base: no new logical axioms, but extra trusted implementations of existing definitions, which a wrong answer could make unsound. Requirements:
   - a mode that switches text natives off, with differential tests against that independent path, never against expected results computed by the same natives;
   - compact values must still behave as `MkText` and its list in pattern matching, conversion and quoting.

A later move to Lean-style bytes with a validity proof would preserve the API through the list view, but not necessarily proofs that relied on the `MkText` constructor or its reductions. For a toy project that's acceptable; the round-trip lemmas give a more representation-independent route meanwhile.

### The JavaScript boundary

**`Text`:**
- Encodes to a JS string.
- Decoding requires a *well-formed* string (no lone surrogates) and yields its scalars in order.
- A malformed string is refused with `StitchwortInputError`, never repaired. That's our own policy, following from the `Text` invariant and the round-trip laws.
- A lossy conversion that replaces lone surrogates could be added later, under its own name. It must never pass through the strict decoder.

**Round-trip laws:**

```
decodeText (encodeText t) = t
encodeText (decodeText s) = s        -- whenever decoding s succeeds, as the same JS string
```

**`Char`** decodes only from a well-formed string containing exactly one scalar.
- A lone surrogate is refused, even though JavaScript's code-point iteration yields it as one element.
- A supplementary scalar (like 😀) is accepted, even though its JS `.length` is 2.

**Encoding** succeeds for every value, subject only to the host's limits on string size.

**Test cases:**
- a valid surrogate pair;
- a lone high surrogate, a lone low surrogate, and malformed surrogates inside otherwise valid text;
- the empty string, and multiple scalars passed as a `Char`;
- embedded NUL and noncharacters (accepted, not truncated).

## Part 2: `IO` and `main`

### The ability

```
ability IO where
  print    : Text -> {IO} ()          -- writes the text, then a line ending
  readLine : () -> {IO} (Maybe Text)  -- Nothing only at end of input
```

**Prelude code can construct and interpret `IO` requests. Only an explicitly invoked host interpreter performs real console operations.** The type checker may evaluate `IO` handlers written in Stitchwort, such as the simulator below; it never invokes the real interpreter. `print` isn't a special case in the shared evaluator.

### The simulator, first

```
-- Runs a program against scripted input lines. Records each `print`
-- payload, in order, and the result.
simulate : List Text -> (() -> {IO | e} a) -> {e} Pair (List Text) a
```

- **It records operation payloads.** `print "a\nb"` is one entry containing a newline, not two display lines.
- **The real interpreter's output is those payloads, each followed by a line ending.** That rule is what tests compare against.
- **It's built with or before the real runner**, which is tested against it.

This relaxes DESIGN.md's "only the runtime handles `IO`": user handlers for `IO` are allowed. A handler is an ordinary checked fold over a well-founded tree, and interpreting `IO` requests as data isn't performing real `IO`. (The rule was motivated by `Partial`, where a user handler could hide non-termination; that doesn't apply here.)

### `main` and `stitchwort run`

- **The type of `main`.** A program's `main` is `() -> {IO} ()`. Every other ability must be handled inside it. A pure `main : () -> ()` is accepted too, without a dummy `print`, through the existing mechanism that passes a function with fewer abilities where more are allowed.
- **The runner.** `stitchwort run file.sw` checks the file, evaluates `main ()`, then loops:
  - on `Done _`, it exits successfully;
  - on `Call op rest`, it performs `op`, applies `rest` to the result, and continues.

  It evaluates only as far as the next `Done` or `Call`, and doesn't normalise continuations under their lambdas.

**The interpreter's contract:**

| | Behaviour |
|---|---|
| **Input encoding** | UTF-8. Malformed input is a runtime `IO` error |
| **Line endings** | A trailing LF, and a CR immediately before it, are removed; everything else is kept. This isn't done with `trim`, which would remove the user's own content |
| **Empty line** | `Just ""` |
| **End of input** | `Nothing` when nothing remains. A final line without a line ending is returned once, then `Nothing` |
| **Output** | UTF-8; each `print` writes its payload, then LF |
| **Flushing** | Output is flushed before every read |
| **Errors** | A read error, write error or flush error stops the program with a message and a non-zero exit code. A read error is never reported as `Nothing`, and a failed write never as success. Recoverable errors, through `Result`-returning operations, can come later |

This is deliberately not Rust's `read_line` behaviour (which keeps the delimiter), so the runtime implements it explicitly.

**Stack safety.** The runner's loop doesn't grow the stack. That doesn't make the evaluator stack-safe: evaluating a continuation, traversing a long text, or deeply nested `bind`s can still recurse deeply. Stress tests cover these. The playground keeps evaluation and output budgets, because totality doesn't make printing a huge amount of text responsive.

### What the guarantee says

**Checked total computations have a well-founded continuation structure.** Every execution performs finitely many operation requests, assuming each host request returns. There's no bound on the number that holds whatever the responses are: a program can read a line and print once per character in it.

So a genuinely unbounded interactive loop (a REPL, a server) isn't available in the total fragment, and won't be until `Partial` exists. Bounded interaction is enough for this milestone. A host can also drive repeated calls to a total step function without claiming that its own driver is total. This doesn't make `Partial` more urgent.

### Extraction and the playground

- **Exports stay pure.** A pure export may use `IO` internally only if it handles it, for example with `simulate`. Host-provided `IO` for exports is a later milestone.
- **The playground gets a Run button.** It runs `main` with no input (`readLine` gives `Nothing`), within budgets, and shows the printed lines.

## Build order

1. **`Char`:**
   - the prelude definitions, with `charExt` proved and equality built on it;
   - character literals and escapes;
   - kernel tests that refuse malformed `MkChar` terms.
2. **`Text`:**
   - the prelude definitions and operations, the round-trip lemmas, and string literals;
   - specification tests for the contract and for `trim`, `textToNat` and `split`.
3. **The JavaScript encoders and decoders** for `Text` and `Char`, the boundary tests, and the differential tests extended to text, including the cross-runtime counterexamples.
4. **The `IO` ability and `simulate`.**
5. **`main` and `stitchwort run`**, tested against `simulate` and against real standard input and output.
6. **The playground's Run button.**
7. **Later, and separately justified:** compact text in generated JS, then possibly in the checking evaluator.

## Acceptance criteria

| Area | Evidence |
|---|---|
| `Char` | Boundary values (0, 0xD7FF, 0xD800, 0xDFFF, 0xE000, 0x10FFFF, 0x110000); malformed constructor applications refused by the kernel; `charExt` checked; decidable equality built on it |
| The contract | Exact scalar equality; no implicit normalisation; scalar length; scalar ordering, including `"\u{10000}" < "\u{E000}"` being false |
| Library operations | Whitespace set, number grammar and `split` edge cases as specified; the round-trip laws for `toList`/`fromList`, `textToNat`/`natToText` and `split`/`join` |
| The JS boundary | Both round-trip laws; surrogate rejection (lone high, lone low, embedded); supplementary scalars; NUL and noncharacters; `Char` decoding of empty strings and multiple scalars |
| `IO` | Empty line versus end of input; a final line without a line ending; CRLF; invalid UTF-8; write failures; the simulator and the runner agreeing |
| Robustness | Stress tests for long texts and deeply nested `bind`s; playground budgets |
| Compact text, when it comes | Differential tests against the natives-off path, including pattern matching and proof fields that don't reduce to `rfl` |

## Sources

- Lean: [Strings in the reference manual](https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/), [4.25.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/)
- Rocq: [`PrimString`](https://docs.rocq-prover.org/v8.20/stdlib/Coq.Strings.PrimString.html), [`PrimStringAxioms`](https://docs.rocq-prover.org/v8.20/stdlib/Coq.Strings.PrimStringAxioms.html), [classic `String`](https://rocq-prover.org/stdlib/Stdlib.Strings.String.html)
- Agda: [standard library `Data.String`](https://www.cse.chalmers.se/~nad/listings/lib/Data.String.html)
- Idris 2: [`Data.String` source](https://idris-lang.org/Idris2/base/source/Data.String.html)
- Haskell: [`text` 2.0 changelog](https://hackage.haskell.org/package/text-2.0/changelog), [Channable: "So long surrogates"](https://www.channable.com/tech/so-long-surrogatesa)
- Swift: [SE-0363 discussion](https://forums.swift.org/t/se-0363-unicode-for-string-processing/58520/9)
- [The WTF-8 encoding](https://wtf-8.codeberg.page/)
