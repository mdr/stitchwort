# Stitchwort: text, `IO` and `main`

**Status:** draft 2, 15 October 2026. Accepted after review. Build steps 1 to 6 are implemented: `Char`, `Text`, the JavaScript boundary, the `IO` ability and `simulate`, `main` and `stitchwort run`, and the playground's Run button; see [As built](#as-built). Step 7 (compact text) has its first stage built: in generated JavaScript a `Text` is a string and the prelude's text operations are native, so they handle millions of characters ([compact text, as built](compact-text.md#as-built-stage-1)); the checking evaluator's stages are later. [Acceptance criteria](#acceptance-criteria) lists what the first milestone must show.

## As built

Where steps 1 and 2 differ from, or add to, the design below:

- **Names are prefixed.** The prelude has no modules and its names can't be redefined, so the text operations are `textLength`, `textIsEmpty`, `textToList`, `textFromList`, `textUncons`, `textFold`, `textCompare`, `textLess`, `textTrim`, `textSplit`, `textJoin`, `natToText` and `textToNat`. `Char`'s are `isScalar`, `charToNat` and `charFromNat`.
- **`++` is chosen by type:** `textAppend` for texts, `append` for lists. It binds more loosely than `+` and groups to the right.
- **New prelude types:** `Maybe`, `Pair` (with `fst` and `snd`) and `Ordering` (`Less`, `Equal`, `Greater`). Examples that defined their own `Maybe` or `Pair` now use these.
- **`\r` is also an escape**, for line-ending tests. Values print as literals (`'a'`, `"h\u{301}"`), with invisible and combining characters escaped.
- **`charExt` needs uniqueness of proofs of `b = True`.** The kernel has `J` but not axiom K, so this is proved by Hedberg's argument (`uniqueBoolEq`): a function that picks a canonical proof from `decEqBool` ignores which proof it's given, and every proof can be recovered from the canonical one.
- **Proved, for every input:** `textToList (textFromList cs) = cs`, `textFromList (textToList t) = t`, `textLength (a ++ b) = textLength a + textLength b`, and `textJoin s (textSplit s t) = t`.
- **Tested, not proved:** `textToNat (natToText n) = Just n`, for 0 to 100 and some larger numbers up to 2^64. A proof would need lemmas about `/` and `%`.
- **Long texts overflowed the stack** when this was built: the evaluator used the Rust stack, and a release build stopped between 3,000 and 6,000 characters. Since the evaluator became an abstract machine (the stack-safe evaluation work), a release build splits a 100,000-character text and takes the length of a 200,000-character one; at a million characters it stops cleanly with `E-RESOURCE` (measured during step 3 with `stitchwort eval`). Generated JavaScript has its own limits; see step 3 below.

Where step 3 differs from, or adds to, the design below:

- **The codecs are as proposed.** In the generated JavaScript, `Text` is `{ tag: "MkText", chars: <list> }` with each character `{ tag: "MkChar", code: <bigint> }` (the proof field is erased). At the boundary both are strings, and `string` in the TypeScript declarations. Decoding walks the UTF-16 code units, joining each surrogate pair into one scalar value, and refuses any other surrogate with `StitchwortInputError` (``t: a lone surrogate (U+D83D) at index 2; text must be a well-formed string``); nothing is repaired. A `Char` must decode to exactly one scalar value (``c: expected exactly one character, but the string has 2``). Encoding joins `String.fromCodePoint` of each character.
- **Data types with parameters can cross the boundary now**, so `Maybe Text`, `Pair Char Text` (what `textUncons` returns) and `List (Maybe Nat)` work, as well as `Text` inside a user's data type. Each such type gets one generic codec, which takes its parameters' codecs (`dec_Maybe(dec_Text)`), and a generic TypeScript alias (`Maybe<string>`). (Since replaced by descriptions of the types, `data(info$Maybe, [TEXT])`, which one loop decodes; see DESIGN.md §12.) A parameter must be a type: `Decidable p`, whose parameter is a proposition, still can't cross.
- **Fixed on the way:** a field called `x`, `path` or `inside` hid the decoder's own variables, so decoding failed with a `ReferenceError`. Decoded fields are now `$`-prefixed locals. (A field called `tag` still clashes with the constructor tag; see below. Both were later fixed by construction: see [Names](../../DESIGN.md#names) in DESIGN.md §12.)
- **Tested** in `crates/cli/tests/extract.rs`, with the exports in `examples/extract/text.sw`:
  - **every boundary case listed below:** a valid surrogate pair; lone high and low surrogates at the start, middle and end, a pair the wrong way round, two highs then a low, and a low after a valid pair, each refused as `Text` and as `Char` with its index; the same inside a list, `Maybe`, `Pair` and a user's type, with the path to it (`ts[1]`, `arg0.value`, `p.snd`, `arg0.tags[0]`); the empty string, two scalars and a base letter with a combining accent as `Char`; non-strings (`97n`, an array, a `String` object, `null`); NUL and noncharacters (U+FDD0, U+FDEF, U+FFFE, U+FFFF, U+1FFFE, U+10FFFF), accepted and not truncated;
  - **`encodeText (decodeText s) = s`:** 5,000 random strings of code units, about a third of them surrogates. Each is decoded exactly when JavaScript's own `isWellFormed` says it's well-formed, and then comes back as the same string, with `textLength` equal to its number of code points;
  - **`decodeText (encodeText t) = t`:** a text of about 1,100 scalar values (the edges of every range, and every 997th one) is encoded and decoded again, and each one round-trips as a `Char` with the right code;
  - **differential tests:** the reference evaluator and the generated JavaScript agree on 55 `-- run:` cases and 100 random inputs per export, built from awkward characters (NUL, a combining accent, U+D7FF, U+E000, noncharacters, U+10000, an emoji, U+10FFFF, U+00A0, U+2028). The `-- run:` cases include the cross-runtime counterexamples, each a place where the obvious JavaScript gives a different answer: `.length` of an emoji is 2, but `textLength` is 1; JavaScript's `<` puts `"\u{10000}"` before `"\u{E000}"`, but `textCompare` doesn't; `trim()` also removes U+00A0, U+2028 and U+FEFF; `Number` or `parseInt` accepts each of `""`, `" 12"`, `"+5"`, `"12abc"`, `"0x10"` and `"1e3"`, which `textToNat` refuses; `slice(1)` and `split("")` would cut an emoji in half (`textUncons`, and a user's `reverse`); and `"\u{E9}"` and `"e\u{301}"` are different texts, though `localeCompare` calls them equal.
- **Long texts in generated JavaScript.** JS engines don't eliminate tail calls, and nearly every text operation recurses once per character, so a long enough text overflows the JS stack. Measured in Node 22.23 with its default stack (about 1 MB), by bisection to within 1%, the longest text each operation handled:

  | Operation (input) | Before | After step 3 |
  |---|---|---|
  | decoding and encoding only | over 4 million | over a million (not tried further) |
  | `textLength` | 8,128 | 8,128 |
  | `a ++ b` (`a` long) | 9,152 | 8,128 |
  | `a ++ b` (`b` long) | over 4 million | over a million |
  | `textSplit` (no separators; all separators) | 6,112; 5,504 | 6,112; 5,504 |
  | `textJoin` (that many one-character texts) | 6,848 | 6,848 |
  | `textTrim` (no spaces; leading spaces) | 9,152; 3,056 | over a million |
  | `textToNat` (digits) | 2,544 | 3,056 |
  | `natToText` (digits of the result) | 5,888 | over 65,536 (not tried further) |
  | `==`; `textCompare` | 6,112; 5,504 | 6,112; 6,112 |
  | `textFold` | 6,848 | 6,848 |
  | `reverseOnto` (a user's `reverse`) | 9,152 | over a million |
  | a user's count, recursing in one branch of an `if` | 3,056 | 6,112 |
  | a user's count with an accumulator | 5,504 | over a million |

  The numbers move by tens of percent with the JIT's state (`textLength`, measured on its own in a fresh process, reached 11,008), and other engines' stacks differ (not measured). So the documented limit is **a few thousand characters**, and a test checks that each operation exported by `examples/extract/text.sw` handles 1,000.
- **What was done about it** is the simplest sound step, leaving the real fix to compact text (step 7):
  - **Running out of stack is a clean error.** Each export catches the engine's stack overflow (a `RangeError` in V8 and JavaScriptCore, an `InternalError` in SpiderMonkey) and throws a new `StitchwortResourceError`, declared in the `.d.ts`, whose `cause` is the engine's error. A `BigInt` or string too large for the engine is the same kind of error. Pure generated code has no state to corrupt, so the module carries on working; a test overflows `textLength`, `textSplit`, a user's recursion and the decoder of a nested tree (since then, `leaves` on it: the decoder no longer recurses), each a million deep, then calls them again normally. Input errors stay `StitchwortInputError`.
  - **A function's tail calls to itself are loops**, as DESIGN.md §12 always said they would be. A call to the function being defined, with all its arguments, in tail position (including either branch of an `if`, which is written out as a JS `if`) becomes another turn of a loop. Each turn has its own `const` copies of the parameters, so closures made in one turn keep its values, and the parameters themselves aren't assigned, so a partial application can be called again; `examples/extract/loops.sw` tests both, and fails if either is broken. This made `textTrim`, `reverseOnto`, `natToText` and a user's accumulator loops unlimited, and halved the stack use of recursion in one branch of an `if`.
  - **Why not more.** `length`, `append`, `textSplit`, `textJoin`, `==`, `textCompare` and `textFold` aren't tail-recursive, and their definitions are what the proofs are about, so rewriting them would mean re-proving their laws. Making all generated code stack-safe (a trampoline, or continuation-passing) would slow every call and enlarge the trusted code generator. Compact text in generated JS (step 7) replaces exactly these operations with native string code.
- **Left for later:**
  - compact text in generated JS (step 7), which removes the limit for the prelude's operations. Since built: the limits in the table above are gone for every prelude text operation (over 4 million characters each), though a user's own recursion over text still has them ([compact text, as built](compact-text.md#as-built-stage-1));
  - tail calls between different functions, and through helpers (`textToNat`'s `readDigits` recurses through `maybeThen`), aren't loops; nor are the branches of `if h : P`;
  - decoding and encoding a user's recursive data type recurse too, so a deeply nested input is a `StitchwortResourceError` (lists and texts are decoded and encoded with loops). Since fixed: decoding and encoding keep their own stack (DESIGN.md §12);
  - a field called `tag` clashes with the constructor tag in the boundary representation (found during step 3). Since fixed: it's `$tag` ([Names](../../DESIGN.md#names));
  - the limits in browsers, and the `InternalError` branch for SpiderMonkey, aren't tested.

Where step 4 differs from, or adds to, the design below:

- **`IO` is an ordinary ability, declared in the prelude** exactly as proposed. Nothing in the elaborator or the evaluator treats it, `print` or `readLine` specially; abilities in the prelude needed no change.
- **`simulate` is an ordinary handler.** Its `handle` builds a function waiting for the remaining input and the payloads printed so far, like `runState` in `examples/accept/abilities.sw`. `readLine` takes the next line, or gives `Nothing` once they're used up (and keeps giving it); `print` adds its payload as one entry, whatever it contains. The payloads are collected in reverse and turned round at the end, so a long run doesn't build a deep chain of pending pairs. A new prelude helper, `nextLine`, gives the first scripted line, if there is one.
- **`IO` always comes first in a row.** Rows are kept in the order abilities were declared, and the prelude is declared before any file, so `{IO, State Nat}` and `{State Nat, IO}` are the same type. The test cache shows it: in `examples/accept/io.sw`, the tests that differ only in row order have the same hash.
- **Tested** in `examples/accept/io.sw`: payloads in order, one entry per payload even with a line feed, an empty line versus end of input, end of input repeated, interleaved reading and printing, `IO` with `State` and `Abort` with the handlers nested either way round, a program without `IO`, and 5,000 prints. A small simulated run is also proved by `rfl`. In a debug build, 100,000 prints run in about 14 seconds without overflowing the stack.
- **Exports can use it.** `examples/extract/io.sw` exports pure functions that run `IO` code through `simulate`, and the generated JavaScript agrees with the reference evaluator.

Where step 5 differs from, or adds to, the design below:

- **`stitchwort run file.sw`** checks the file as `check` does (without running its tests), finds `main`, and runs it against standard input and output. The runner is in the driver (`crates/driver/src/run.rs`), so the playground can use it too.
- **Checking `main`.** The runner checks `(\u -> main ()) : () -> {IO} ()`. Calling a pure function from `{IO}` code is allowed, so a pure `main : () -> ()` passes; any other type, including a row with an unhandled ability or a result other than `()`, is `E-MAIN-TYPE`, pointing at `main`. A file without `main` is `E-NO-MAIN`. A plain annotation `(main : () -> {IO} ())` wouldn't do: it doesn't accept the pure `main`.
- **The loop** is as proposed. Each step, from one operation to the next, is one operation with its own resource limits (the same limits as a test). So a long-running interactive program doesn't run out just by running long, but a single step that does too much stops it with `E-RESOURCE`, pointing at `main`.
- **Errors.** A read error, input that isn't UTF-8 (`E-IO: line 2 of standard input isn't valid UTF-8`), and a write or flush error each stop the program with `E-IO`. What was printed before an error is flushed, as far as possible. Every failure (a file that doesn't check, a missing or ill-typed `main`, running out of resources, an `E-IO` error) exits with code 1; success is 0. Clap's own usage errors exit with 2.
- **A final line ending in a lone CR** (no LF) keeps its CR: only a CR immediately before the removed LF goes.
- **Output is buffered** and flushed before every read and at the end, so a pipe that closes early (`stitchwort run … | head -1`) is a write error, reported with exit code 1.
- **Tested** in `crates/driver/tests/run.rs` (in memory) and `crates/cli/tests/run.rs` (the built command, as a subprocess):
  - **the simulator and the runner agree**: six programs, including `examples/accept/adder.sw`, a pure `main` and one with `State` handled inside, each with seven scripted inputs, written with LF and CRLF endings, and with and without the final line ending. The runner's output must be `simulate`'s payloads, each followed by LF. The command is checked the same way on the example;
  - empty input, an empty line versus end of input, a final line without a line ending, CRLF, CR elsewhere in a line, NUL and non-ASCII text;
  - invalid UTF-8 (an invalid byte, a truncated sequence, an encoded surrogate, an overlong NUL), with the earlier output still printed;
  - a read error, a write error, a flush error (in memory), and a write to a closed pipe (end to end);
  - flushing before every read, both by recording the order of reads and writes, and end to end by reading the prompt from a running `stitchwort run` before giving it any input;
  - running out of resources, and that the limits are per step: 2,000 prints finish within a budget that `simulate`, running the whole program as one operation, exceeds;
  - 20,000 prints, for the loop's stack use;
  - `E-NO-MAIN`, `E-MAIN-TYPE` for five wrong types, a pure `main`, and exit codes for each error kind.
- **Not tested end to end:** running out of resources under the real command. With the command's limits, that takes a recursion two million frames deep, which needs over a gigabyte of memory. The driver test checks the error and where it points; the command reports it the same way as `E-IO`, which is tested end to end.
- **The example** is `examples/accept/adder.sw`: it asks for a name, then adds up numbers, one per line, until an empty line or the end of input. Its tests run the same `main` through `simulate`.

Where step 6 differs from, or adds to, the design below:

- **Input is scripted, not empty.** The playground has no terminal, so the Run tab has a box of input lines: `readLine` gets them one at a time, then `Nothing`. They go through the same runner as `stitchwort run` (`Session::run_main`, reading the box's text as its input), so the interpreter's contract holds unchanged; an empty box gives the proposal's "no input".
- **The interface** is `run(source, input, max_output)` in `crates/web`, returning JSON like the playground's other functions: `{"ok": true, "output": …}`, or `{"ok": false, "errors": …}` with the output printed before the error if `main` had started. Check errors, `E-NO-MAIN`, `E-MAIN-TYPE` and `E-RESOURCE` are rendered as in the Check tab.
- **Budgets.** Each step between operations has a test's resource limits, as in `stitchwort run`. Output is capped at 256 KB: a program that prints more is stopped with a new error, `E-OUTPUT`, and the output up to the cap is shown. A run is stopped after 15 seconds, or by the Stop button; then its output is lost, because the page only gets the output when the run returns. A program that reads past the end of its input a billion times, printing nothing, is what the timeout is for. (Since then: the output streams to the page a line at a time, through `run_streaming`, so a stopped run keeps what it printed; and reading past the end of the input more than 10,000 times stops a run with `E-INPUT`, which bounds how many operations a run performs, since printing is bounded by the output cap and reading lines by the input.)
- **The compiler runs in a Web Worker** (`web/playground-worker.js`), as `web/stress.html` does. The page compiles the WebAssembly once and gives the module to each worker it starts, so a fresh worker is quick. A worker is discarded, and the next request starts a new one, after it crashes (a trap, or the JavaScript engine's stack overflowing: a `RangeError` leaves the instance's state broken), times out (60 seconds for checking, testing, evaluating and extracting; 15 for a run), is stopped, or is superseded by a newer request (editing while a slow check runs). Running uses a second worker, so the editor keeps checking during a run. If the host doesn't allow workers, the page falls back to running the compiler in the page, where nothing can be stopped and a crash needs a reload.
- **The example** in the playground ("Input and output: `main`") is `adder.sw` with its scripted input filled in.
- **Tested** in `crates/web`: scripted input (including an empty line versus end of input, and no input), a pure `main`, `E-NO-MAIN`, `E-MAIN-TYPE`, a check error, the output cap (exactly at it, one byte over, and a cut through a character), and `E-RESOURCE` with the output before it. Every playground example must check and pass its tests (except the deliberate failure), and the `main` example must print what's expected for its input. The page itself was tried by hand in headless Chrome, not by an automated test: the existing tabs, Run, `E-NO-MAIN`, the output cap, Stop, the timeout, recovery after a crash, and the fallback when workers can't start.

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
- **The playground gets a Run button.** It runs `main` with no input (`readLine` gives `Nothing`), within budgets, and shows the printed lines. (As built, it takes scripted input lines; see [As built](#as-built).)

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
   Design: [compact text](compact-text.md). The generated-JS stage (option A there) is built; the checking evaluator's stages await a decision.

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
