# Proposal: compact text

**Status:** draft 2, 15 October 2026. Revised after external review; see [Changes since draft 1](#changes-since-draft-1). Option A (stage 1) is approved and built; see [As built (stage 1)](#as-built-stage-1). B1 and B2 (stages 2 and 3) await a further decision. This is step 7 of [the text proposal](text-and-io.md#making-it-fast-in-stages), "compact text in generated JS, then possibly in the checking evaluator".

## Summary

`Text` is defined as a list of characters, and the proofs about it are proofs about that list. This note proposes keeping that definition as the **specification**, and storing text compactly underneath it, in stages:

1. **Generated JavaScript first (option A).** Extracted code stores a `Text` as a JS string, and the prelude's text operations get native JS implementations. The kernel doesn't change, and nothing new is trusted by proof checking; the extractor, which is already trusted, grows. This removes today's limit of a few thousand characters in generated code.
2. **Then the checking evaluator, in two halves (option B).** First a compact *representation* with no native operations (B1): a text literal becomes one term, and a `List Char` can be stored as a range of a character array. Its meaning is fixed by one rule, *expansion* into ordinary constructors, and every operation on it must commute with that expansion. Later, and only where measurements justify it, a short list of native operations (B2), starting with ones that produce plain data (`textLength`, `textCompare`, `natToText`). A native that produces a proof, such as `decEqText`, comes only after a test shows its *whole* result, proof included, agrees with the definition's.

A primitive string type in the kernel, as Rocq's `PrimString` does it (option C), is not recommended: it would replace the existing proofs about `MkText` with axioms, and Stitchwort's exports must be free of axioms.

The rest of the note is written for a reviewer who knows dependent types and compilers but not this codebase.

## As built (stage 1)

Option A is implemented in `crates/js/src/lib.rs`, as designed below. The kernel and the checking evaluator are unchanged. Where the build differs from, or adds to, the design:

- **Native** (`TextNative`, `text_native_js`): 14 definitions, checked against the prelude's definitions, which are the specification: `textToList`, `textFromList`, `textAppend`, `textLength`, `textIsEmpty`, `decEqText`, `textCompare`, `textUncons`, `textFold`, `textTrim`, `textSplit`, `textJoin`, `natToText` and `textToNat`. `textFold` walks the string backwards, so it needs no array; `textToNat` checks for ASCII digits with a loop rather than a regular expression; `textSplit` is `t.split(separator)` turned into a list in a loop.
- **Not native, and why:**
  - `textLess` is `isLess (textCompare a b)`: not recursive, and its `textCompare` is native, so compiling the definition is as good. `decTextFrom` is `decEqText`'s proof plumbing, unused once `decEqText` is native.
  - The list helpers behind the natives (`foldChars`, `compareChars`, `isSpaceCode`, `isSpace`, `dropSpaces`, `digitChar`, `natDigits`, `maybeThen`, `digitValue`, `readDigits`, `splitCons`, `splitChars`, `joinChars`, `joinPair`, `textsOf`, `charListsOf`, `splitTexts`) work on lists, not `Text`. They're only emitted when user code calls them directly, and then keep their per-element stack use where they recurse.
  - `isScalar`, `charToNat` and `charFromNat` are about `Char`, which is unchanged.
- **Binding.** `TEXT_NATIVES` pins each native to the content hash of the prelude definition it replaces. A definition with a different hash is compiled as written instead, which still works (through the bridges below), only slower; and the test `text_natives_are_bound_to_the_prelude` fails, printing the new hashes, so each changed definition gets re-checked against its native. The hashes don't cover field names (`code`, `head`, `value`, `fst`), which the runtime already relied on.
- **Bridges.** `charsOfText` and `textOfChars` in the runtime convert between a string and its `List Char`, in loops. Matching `MkText cs` emits `charsOfText` only if the branch's generated code mentions `cs`, so `isText (MkText _) = True` converts nothing. A text literal is a JS string literal, found by walking the literal's characters in a loop.
- **The boundary.** Decoding a `Text` runs the same strict check (`wellFormed`) and returns the string; encoding returns it. `Char` is unchanged.
- **Turning it off.** `stitchwort_js::generate_with` with `Options { native_text: false }` generates the list-based code, exactly as before. It's for the differential tests, not exposed in the CLI.
- **The guarantee**, as stated under option A: the natives and the bridges don't use JS call-stack space proportional to a text's length. No helper spreads arguments.

**Tested** in `crates/cli/tests/extract.rs`:

- **Against the definitions, two ways.** The `-- run:` cases (67 in `text.sw`, up from 55) and 100 random inputs per export are checked against the reference evaluator for the generated code with natives *and* for the list-based code. A property-style test, `text_natives_agree_with_the_list_definitions`, runs every export of `examples/extract/text.sw` both ways on every text of up to four characters over a seven-character alphabet (including U+E000, an emoji and a neighbouring emoji), every pair of texts of up to two, 3,000 random texts and 3,000 random pairs of up to 24 characters built from 27 awkward characters (NUL, the six whitespace characters and their look-alikes U+00A0, U+2028 and U+FEFF, a combining accent, U+D7FF, U+E000, noncharacters, U+10000, two emoji, U+10FFFF, digits), most pairs differing by one edit so they share a prefix, and the cross-runtime counterexamples for `textToNat` (`" 12"`, `"+5"`, `"0x10"`, `"1e3"`, Arabic-Indic digits, `"12\n"`); about 220,000 comparisons in all. Deliberately breaking `textCompare` (comparing code units), `textLength` (an off-by-one in the pair test) or `textTrim` (also trimming U+00A0) each made it fail.
- **First-class uses and user matches:** `mapList textLength ts`, `mapList MkText ls`, `mapList (textAppend "pre") ts`, a user's match on `textSplit`'s result, a user's `MkText (Cons c cs)` match on `textTrim`'s result, and an unused `MkText` field (whose generated code is checked to convert nothing), in `examples/extract/text.sw`.
- **The whole export path at a million characters** (`long_inputs_are_loops_or_resource_errors`): every native; one long split field and 500,001 short ones, joined again; a million one-character joins; a long `List Char` returned and passed in; `MkText` matched and built by user code on long texts. A user's function that recurses once per character still throws `StitchwortResourceError`, and the module works afterwards.
- **Binding:** `text_natives_are_bound_to_the_prelude`. **Representation switch:** `native_text_is_only_used_when_asked_for`.

**Measured**, in Node 22.23.3 on an arm64 Mac, by bisection to within 1% with the default stack, capped at 4,194,304 characters (scratch script, not in the repository):

| Operation (input) | Longest before | Longest after |
|---|---|---|
| `textLength` | 8,128 | over 4,194,304 |
| `textSplit` (no separators; all separators) | 6,112; 5,504 | over 4,194,304 |
| `textJoin` (that many one-character texts) | 6,112 | over 4,194,304 |
| `textToNat` (digits) | 2,544 | over 4,194,304 |
| `==`; `textCompare` (equal texts) | 6,112; 6,112 | over 4,194,304 |
| `textFold` | 7,872 | over 4,194,304 |
| `a ++ b` (`a` long) | 9,152 | over 4,194,304 |
| `textToList`, `textFromList`, `textTrim` | over 4,194,304 | over 4,194,304 |

Median of five runs, on a million characters (`"abcd,😀x "` repeated) unless stated, through the export's decode and encode:

| Operation | Before | After |
|---|---|---|
| `textLength` | stack overflow | 3.5 ms |
| `textSplit` (125,000 fields) | stack overflow | 7.0 ms |
| split then join | stack overflow | 8.7 ms |
| `==` | stack overflow | 2.5 ms |
| `textCompare` | stack overflow | 5.4 ms |
| `textFold`, counting | stack overflow | 4.5 ms |
| `textToNat`, a million digits | stack overflow | 45 ms |
| `textToList` (a million `Char`s out) | 147 ms | 115 ms |
| construct only: 20,000 right-nested `++` of `"abcd,"`, encoded | 4.8 ms | 0.1 ms |
| construct then consume: `textLength` of the same | stack overflow | 0.4 ms |

Also after: splitting `"a,"` repeated 500,000 times into 500,001 fields, 25 ms; joining them again, 19 ms; `fromChars` of a million `Char`s, 98 ms; decoding and encoding a million characters alone, 1.9 ms. The numbers vary by tens of percent between runs.

**Found on the way:** a `List (List Char)` parameter was declared as `readonly readonly string[][]`, which isn't TypeScript; it's now `readonly (readonly string[])[]`.

**Left for later:** stages 2 and 3 (B1, B2); a more compact `Char`; the string-backed list variant; making user recursion over text stack-safe.

## Changes since draft 1

Draft 1 was reviewed externally. The review agreed with the order (A, then B1, then B2 selectively) and with keeping `Text`'s list definition, and asked for these changes, all adopted:

- **The obligation for a kernel native is stated exactly**: `expand(native_D(args)) ≡ D(expand(args))` under the reference rules, over the *entire* result, proofs and functions included ([What "the same meaning" must mean](#what-the-same-meaning-must-mean)). Draft 1's `No (textNeq a b rfl)` for `decEqText` doesn't obviously meet it, and the existing native `decEqNat` demonstrably doesn't (the kernel rejects `myDecEqNat 3 5 = decEqNat 3 5` by `rfl`, where `myDecEqNat` is a copy of the definition; see [Auditing `decEqNat`](#auditing-deceqnat)). B2 now starts with natives that produce plain data.
- **Each native has an explicit eligibility predicate**, covering every argument that can carry a proof (for example `textJoin`'s separator), not just "every argument is fully compact text".
- **Natives and the compact representation are bound to the exact declarations they depend on**, by content hash, with a stated policy when they don't match ([Binding to the definitions](#binding-natives-to-the-definitions-they-replace)). The note now says what the exhaustive `isScalar` test establishes, and what it doesn't.
- **B1's expansion invariant is the central rule**: matching, conversion and quotation commute with expansion. Added: the list of passes that consume terms and values and must handle the new form, termination descent only from real `Cons` cases, and unification tests (`Cons ?c ?tail ~ Chars "ab"`, metavariables solved later, rigid non-`rfl` proofs).
- **The range representation is decided** (shared start and end, rather than a suffix offset), with hashing of logical contents and a rule against retaining large buffers for small ranges.
- **Costs are split into three categories** (one compact range, a cons prefix then a compact tail, an ordinary list), and the performance claims are corrected: stored payload is not peak heap, allocation counts are measured separately, natives are not O(1) in general, and long native work is metered against the step budget.
- **No native `++` initially**, without claiming a rope is the only way to add one later.
- **The test cache key gets an automatic build fingerprint**, covering helpers, representation rules and effective modes, so natives-off runs can't reuse natives-on results; `Term::Chars`'s implicit dependencies are counted; the wording about hash collisions is fixed.
- **Testing is in three tiers** (small exhaustive differential tests against the constructor semantics, medium tests on the stack-safe machine, large stress tests with independent expectations), and the review's extra test table is included.
- **Option A** skips the list conversion for `MkText` fields that aren't used, handles first-class uses of `MkText` and the natives, states its stack-safety guarantee narrowly and tests it on the whole export path (with no unbounded argument spreading), and adds a construct-then-consume benchmark.
- **The claims about option C and the alternatives are softened**, and a variant draft 1 omitted is described: a separately proven fast function used only by extraction.

The review's answers to draft 1's seven open questions are summarised in [Review answers](#review-answers).

## Background

### Stitchwort in brief

Stitchwort is a toy language: strict, pure, total and dependently typed, written in Rust. Its main use is writing library functions, proving things about them, and calling them from a JavaScript or TypeScript application. The compiler also runs in the browser as WebAssembly (the "playground").

The parts that matter here:

- **A small kernel** re-checks everything the elaborator produces. It decides definitional equality by evaluating to values and comparing them (normalisation by evaluation). It has `J`, but no axiom K and no definitional proof irrelevance.
- **Two evaluators share the kernel's data types.** The real one (`crates/core/src/value.rs`) is an abstract machine with an explicit stack, so long lists don't overflow the Rust stack. A recursive reference evaluator (`crates/core/src/reference.rs`) exists only to test it: they share data types and the native number functions, but no evaluation code.
- **Extraction to JavaScript** (DESIGN.md §12) erases types and proofs and generates an ES module. Each export decodes its inputs, checks them, computes, and encodes the result. The extractor and the codecs are trusted, not verified.
- **Content hashing** (DESIGN.md §11). Every checked declaration has a BLAKE3 hash of its elaborated form, covering everything it refers to, transitively. Test results are cached under `<compiler version>-<test hash>`.

### `Char` and `Text` today

From `crates/elab/src/prelude.sw`:

```
isScalar : Nat -> Bool
isScalar n = if leq 55296 n then (if leq n 57343 then False else leq n 1114111) else True

type Char : Type =
  | MkChar (code : Nat) (valid : isScalar code = True)

type Text : Type =
  | MkText (chars : List Char)

textAppend : Text -> Text -> Text
textAppend a b = MkText (append (textToList a) (textToList b))

textLength : Text -> Nat
textLength t = length (textToList t)
```

- The literal `'a'` elaborates to `MkChar 97 rfl`, and the kernel checks `rfl : isScalar 97 = True` by computing. `"ab"` elaborates to `MkText (Cons (MkChar 97 rfl) (Cons (MkChar 98 rfl) Nil))`, a term nested once per character.
- The operations are `textAppend` (written `++`), `textLength`, `textIsEmpty`, `decEqText` (behind `==`), `textCompare`, `textLess`, `textUncons`, `textFold`, `textTrim`, `textSplit`, `textJoin`, `natToText`, `textToNat`, `textToList` and `textFromList`.
- **Proved, for every input:** `textToList (textFromList cs) = cs`, `textFromList (textToList t) = t`, `textLength (a ++ b) = textLength a + textLength b`, `textJoin s (textSplit s t) = t`, and `charExt` (two `Char`s with equal codes are equal, via Hedberg's argument for uniqueness of proofs of `b = True`).
- **The contract** ([text-and-io.md](text-and-io.md#the-contract)): text is a sequence of Unicode scalar values; equality is exact (no normalisation); length counts scalars; ordering is lexicographic by scalar value; `trim`'s whitespace, `textToNat`'s grammar and `split`'s handling of empty fields are fixed by the definitions, not by any host's library.

### How `Nat` was made compact: the precedent

`Nat` is `Zero | Succ Nat` in the prelude, and that's what it means. But since [native numbers](native-numbers.md) (see "Numbers" in [docs/core.md](../core.md#numbers)):

- a number is **stored** as one arbitrary-precision value: `Term::Nat` and `Value::Nat`;
- **matching** on `Value::Nat(n)` takes the `Zero` branch for 0 and otherwise the `Succ` branch with the field `Value::Nat(n - 1)`, without building a chain;
- **conversion** treats `3` and `Succ 2` as equal; a number with unknowns, `k + x`, is kept as `Value::NatAdd(k, x)`;
- eight prelude definitions (`add`, `sub`, `mul`, `leq`, `eqNat`, `divFuel`, `decEqNat`, `eqNatRefl`) have **native implementations**, used only when every argument is a number. Otherwise they unfold as defined, so proofs by induction are unaffected. A native `decEqNat` returns `Yes rfl`, or `No (natNeq m n rfl)` using a prelude lemma;
- the natives are **registered by name** while the prelude loads; registration checks each one's type and arity, and the shapes of `Nat`, `Bool` and `Decidable` (`E-BUILTIN`). `crates/driver/tests/natives.rs` compares each native with its own definition, run with natives switched off, on every small input and on random larger ones. The natives are listed as trusted in DESIGN.md §13;
- extracted JS uses `bigint` and native operators for the same definitions.

This proposal reuses that pattern for text wherever it can, and, as the review pointed out, the number natives need the same scrutiny of their proof outputs ([Auditing `decEqNat`](#auditing-deceqnat)).

## The problems, measured

**Generated JavaScript stops at a few thousand characters.** JS engines don't eliminate tail calls, and `length`, `append`, `textSplit`, `textJoin`, `==`, `textCompare` and `textFold` aren't tail-recursive. Measured in Node 22 with its default stack (text-and-io.md, step 3), the longest text each handled was about: `textLength` 8,000, `textSplit` 5,500 to 6,100, `textJoin` 6,800, `==` 6,100, `textToNat` 3,000. Past that the export throws `StitchwortResourceError`. A function's tail calls to itself already compile to loops, so `textTrim`, `natToText` and a user's accumulator loops are unlimited.

**The checking evaluator copes with length but not literals.** Since the evaluator became an abstract machine, a release build splits a 100,000-character text and takes the length of a 200,000-character one. But long *literals* stop at about 1,800 characters in a 2 MiB thread (about 75,000 in the CLI), because recursive passes walk the literal's term, which is nested once per character (TODO.md). The playground's WebAssembly build has a 128 KiB guard and handles list literals of about 200 elements; I haven't measured text literals there, but they have the same shape, so a similar limit is likely (**not verified**).

**Text is heavy.** Each character is a cons cell and a `MkChar` cell, each holding two values. From `bench/baseline.toml` (counts are deterministic):

| Benchmark | What it does | Steps | Allocations | Peak heap |
|---|---|---|---|---|
| `text-append` | `textLength (repText 20000 "abcd,")`: 20,000 right-nested `++`, 100,000 characters | 4.76 M | 1.72 M | 51.8 MB |
| `text-split-join` | `textLength (textJoin ',' (textSplit ',' big))`, 10,000 characters | 2.29 M | 0.82 M | 6.6 MB |
| `text-nat-to-text` | `natToText` on 10,000 numbers of up to 11 digits | 18.9 M | 6.74 M | 9 KB |

Peak heap includes intermediate results (the split fields, the appended copies), so it is not the size of one stored text; it works out at roughly 500 to 650 bytes per character of *input* in the first two. What one stored character costs today is two cells of two values each, which I haven't measured separately.

## Goals and non-goals

**Goals:**

1. In **generated JS**, prelude text operations work on texts of millions of characters, limited by memory rather than the stack, at speeds close to hand-written JS.
2. In the **checking evaluator** (CLI and WebAssembly), long text literals check, and text uses much less memory.
3. **Every existing proof still checks, unchanged**, and the list definitions stay the meaning of every operation.
4. **New trusted code is small, listed, and tested** against the definitions it replaces, through a path that doesn't use it.

**Non-goals:**

- Changing the contract: still scalar values, exact equality, no normalisation.
- Indexing by position, byte views, or Lean-style `ByteArray` models. These can come later.
- A compact representation for *all* lists. (The machinery below would generalise, but text is where the need is.)
- Making all generated JS stack-safe. User code that recurses once per character is still limited by the JS stack; only the prelude's operations, and the bridges between strings and lists, are lifted.

## What other systems do

| System | What proofs see | What runs | What's trusted |
|---|---|---|---|
| **Lean 4**, kernel | Until 4.24, a structure over `List Char`; since 4.25, a `ByteArray` with a proof of valid UTF-8, with the list view still available | String literals are a kernel literal form, expanded to `String.ofList [chars]` only when a projection, match or definitional-equality check needs it. No native *string* operations in the kernel (only `Nat` ones, with GMP) | The literal expansion |
| **Lean 4**, compiled code | (same) | UTF-8 byte arrays with cached size and length; operations "overridden with an efficient implementation in runtime code", mutating in place when unshared | The runtime's C implementations, which the kernel never sees |
| **Rocq `PrimString`** (8.20, Jan 2025) | An opaque primitive type, specified by axioms in terms of a list model (`to_list`, `of_list`) | A native OCaml string of bytes, at most 16,777,211 long; the manual says the reduction machines have dedicated rules for primitive operations | The primitive declarations, which the manual calls "regular axioms" and which `Print Assumptions` reports, and every reduction machine's implementation |
| **Rocq `PrimInt63`, floats, `PArray`** | Opaque primitives with specification axioms | Native, in all three reduction machines | The same. A wrong float classification allowed a proof of `False` from 8.11 until 8.15.2 |
| **Agda** | An opaque built-in `String`, with primitives `primStringToList`, `primStringFromList`, `primStringUncons`, `primStringAppend` | Native (Haskell `Text`, JS strings) | The primitives, and two postulated properties: `primStringToList` and `primStringFromList` are injective |
| **Idris 2** | A primitive `String`. The view `strM` is built from primitives with `assert_total` and `believe_me` | Native | Every `believe_me` |
| **F\*** | An abstract `string`, with `list_of_string` and `string_of_list` and their round trips stated as `val`s; further lemmas "admitted for now as we don't have a model" | Native in each backend | The admitted lemmas |
| **Unison** (not dependently typed) | n/a | A rope: a size-balanced tree of chunks of Haskell `Text` | n/a |
| **Koka** (not dependently typed) | n/a | Valid UTF-8 always; small strings (at most 7 bytes) unboxed; slices (`sslice`) as views | n/a |
| **V8** (what our generated JS runs on) | n/a | Ropes: `a + b` makes a `ConsString` (two pointers), flattened to a sequential string when read or too deep; `slice` makes a `SlicedString` (parent, offset, length), which keeps its parent alive. Very short results are copied instead | n/a |

What this says for Stitchwort:

- **Lean is the closest match**, and its kernel shows how little is needed: the literal is compact, and is expanded to the constructor form on demand. Its speed comes from compiled code with native implementations that the kernel never trusts. That is option A for the runtime and B1 for the kernel.
- **The systems surveyed that have an opaque string type pay in trusted assumptions** (Rocq, Agda, Idris, F\*). That's what these systems do, not a theorem that every opaque design must: an opaque type with a verified model might avoid it. Stitchwort's list definition gives it the round-trip lemmas and `textJoinSplit` as real proofs, which is worth keeping.
- **Rocq's float bug** is the concrete risk of native reductions in a kernel: a native that disagrees with its specification proves `False`.
- **V8 already makes `+` and `slice` cheap**, so generated code can use them directly. Its deferred flattening and slices that retain their parents are reasons to benchmark *consuming* a result, not just constructing it.

## What "the same meaning" must mean

The list definitions stay the specification. Three different notions of "the same" are easy to confuse, and each layer needs a specific one:

| Notion | Meaning | Where it's enough |
|---|---|---|
| Same erased result | the same JS value after types and proofs are erased | option A (generated JS) |
| Same mathematical value | provably equal, as `charExt` proves `MkChar 97 h = MkChar 97 rfl` | nowhere on its own |
| Same core value up to definitional equality | the kernel can't tell them apart: every conversion it accepts with one, it accepts with the other | B1 and B2 (the kernel) |

### Expansion

Every compact value stands for exactly one ordinary value, its **expansion**, built only from constructors:

```
expand(Chars [c₀, …, cₙ₋₁]) = Cons (MkChar c₀ rfl) (Cons … (Cons (MkChar cₙ₋₁ rfl) Nil))
expand(MkText x)            = MkText (expand x)         -- and so on, structurally
```

A compact representation is correct when **every operation commutes with expansion**:

- **matching** a compact value takes the branch, and binds the fields, that matching its expansion would;
- **conversion**: `convCompact(v, w) = convReference(expand(v), expand(w))`, whenever both finish within their resource limits;
- **quotation**: `expand(quote(v)) = quote(expand(v))`, so a quoted compact value means what its expansion would.

### The obligation for a native

For a native implementation of a definition `D`:

```
expand(native_D(args))  ≡reference  D(expand(args))
```

where `≡reference` is definitional equality under the original reduction rules, with that native switched off. It covers the **entire result**: constructors, data fields, proof fields, and functions inside it. Comparing only an erased projection, such as `toBool (decEqText a b)`, misses exactly the part that matters to the kernel.

This matters most for natives that return proofs. Draft 1 proposed a native `decEqText` returning `No (textNeq a b rfl)`. That is a well-typed refutation, but "it proves the right proposition" is weaker than "it's definitionally the refutation the definition computes". A `No`'s payload is a function from an equality proof to `Void`; even for closed texts, comparing two such functions means comparing their bodies under a bound proof variable, and two different refutation terms generally aren't convertible.

**Consequences:**

- A native whose result contains a proof can only return the proof the definition would compute (or one shown convertible to it), and that has to be tested by comparing whole results, not answers.
- B2 starts with natives that return plain data, whose results have no proof fields to get wrong: `textLength`, `textCompare`, `natToText`. `decEqText` comes only after a whole-result native-on/off test passes for both `Yes` and `No`.
- Option A is not affected: generated JS erases proofs, so the same erased result is enough there.

### Auditing `decEqNat`

The existing native `decEqNat` returns `No (natNeq m n rfl)`, and the definition computes a different refutation. Checked on this branch, with `myDecEqNat` an exact copy of the prelude's definition (so with natives off, both sides would unfold to the same term):

```
theorem sameNo : myDecEqNat 3 5 = decEqNat 3 5
sameNo = rfl
-- E-REFL: `No (\p -> J (\y -> \q -> IsZero y) Trivial (J … p))` and `No (natNeq 3 5 rfl)` aren't equal
```

The same theorem with `3 3` is accepted (`Yes rfl` on both sides). So the native changes which conversions the kernel accepts: it doesn't prove anything false (both payloads are valid refutations, and rejecting a conversion can't make the kernel unsound), but a program that checks with natives off can fail with them on. It's a precedent to audit, not a justification. The fix options are to make the native return the definition's own `No` term (built by the native for the specific numbers, which is O(min(m, n)) in size), to return the `No` only when the payload is never compared (not decidable locally), or to accept and document the difference. This note recommends the first, tested by the whole-result comparison above; it's listed as follow-up work, separate from text.

**Since fixed** by changing the definition instead, so that it computes `No (natNeq m n rfl)` itself; the number natives now have whole-result tests ([native numbers, as built](native-numbers.md#as-built-what-a-native-must-compute)).

### Eligibility: when a native may fire

A native may only fire when the arguments' expansions are what the native assumes. Each native gets an explicit **eligibility predicate** over all its arguments, including every one that can carry a proof:

- a `Text` argument is eligible when it's `MkText` of a list whose every element is `MkChar c rfl` with `c` a literal, ending in `Nil` or a compact range;
- a `Char` argument (`textJoin`'s and `textSplit`'s separator) is eligible when it's `MkChar c rfl` with `c` a literal. `textJoin (MkChar 44 h) ["a", "b"]`, with `h` a proof variable, is **not** eligible: a compact `"a,b"` would silently replace `h` with `rfl`;
- a `List Text` argument (`textJoin`'s) is eligible when its spine is concrete and every element is an eligible text;
- a `Nat` argument (`natToText`'s) is eligible when it's a `Value::Nat` literal;
- a function argument (`textFold`'s) is never inspected, so it's always eligible, but `textFold` isn't a candidate anyway.

Otherwise the definition unfolds as usual. Checking eligibility of a cons-cell prefix is itself a traversal (see [Costs](#costs-three-categories)).

### Same results in generated JS

The fourth requirement, unchanged: generated JS gives the same results, after encoding, as the reference evaluator, which is what the existing differential tests check.

The **round-trip lemmas** are what make this robust: code that goes through `textToList`/`textFromList` and their lemmas, rather than `MkText`'s structure, doesn't depend on the representation at all. But compact text must also support code that matches on `MkText` directly, because the prelude's own proofs do (`textJoinSplit` matches `MkText cs`).

## Binding natives to the definitions they replace

A native replaces a *particular* definition. Registration today checks shapes: that `isScalar : Nat -> Bool`, say. A shape check can't establish what a function returns. If a same-typed `isScalar n = False` could be registered, a compact character's expansion `MkChar c rfl` would claim `rfl : False = True`.

What prevents that today is that the prelude is fixed: it's compiled into the binary, loaded first, and its names can't be redefined (the elaborator refuses a second declaration with a prelude name). So its relevant definitions are part of the trusted implementation, alongside the natives. This note makes that binding explicit, and checked:

- **Each native, and each representation rule, names the declarations it depends on**: for text natives, the definition it replaces; for B1's representation, `List`, `Nil`, `Cons`, `Char`, `MkChar`, `Text`, `MkText` and `isScalar`.
- **Each is pinned to their content hashes** (DESIGN.md §11), which cover everything a declaration refers to, transitively. So a change to `length` changes `textLength`'s hash too.
- **Policy when they don't match:**
  - *function natives* (A's JS natives, B2's kernel natives): the native isn't used, and the definition is compiled or unfolded as written. That's always sound, only slower. A test fails while any native is unbound, saying which, so a deliberate prelude change also makes someone re-check the native and update its pin;
  - *the compact representation* (B1): literals need it to mean anything, so a mismatch is an `E-BUILTIN` error when the prelude loads, rather than a silent fallback. (Falling back to cons-cell literals would also be sound; the error is chosen so a mismatch can't go unnoticed in a release.)

**What the exhaustive `isScalar` test establishes.** Draft 1 proposed testing `isScalar c = True` for every code point up to 0x10FFFF against Rust's `char::from_u32`. That's excellent regression coverage of the forward property B1 needs: every value a Rust `char` (or a well-formed JS string) can hold yields a valid `rfl`. It does *not* establish `isScalar`'s behaviour on all naturals, which are unbounded; the hash binding is what fixes the definition. The test is kept, together with **rejection tests**: `MkChar 55296 rfl` (U+D800), `MkChar 57343 rfl` (U+DFFF) and `MkChar 1114112 rfl` must be rejected, and so must `MkChar (2^32 + 97) rfl` and `MkChar (2^64 + 97) rfl`, which would be accepted by an implementation that truncated to a machine integer somewhere.

## The options

### A. Compact text in generated JavaScript only

**The kernel and the checking evaluator don't change.** Generated code represents a `Text` as a well-formed JS string, and prelude text operations as native JS.

**Representation:**

| Stitchwort | Generated JS before | Under option A |
|---|---|---|
| `Text` | `{ tag: "MkText", chars: <cons list> }` | a well-formed string |
| `Char` | `{ tag: "MkChar", code: <bigint> }` | unchanged (see [`Char`](#char)) |
| `List Char` | cons cells | unchanged |

**Native operations.** Each replaces a prelude definition in generated code, as `native_js` already does for numbers (`crates/js/src/lib.rs`), and is bound to that definition's content hash ([Binding](#binding-natives-to-the-definitions-they-replace)). All work on scalar values, never on UTF-16 code units. The prelude's definitions are the specification; this table is the plan, and [As built (stage 1)](#as-built-stage-1) records what was actually made native:

| Definition | Native JS, in outline | Note |
|---|---|---|
| `textAppend` | `a + b` | V8 makes a rope; both inputs are well-formed, so the result is |
| `textLength` | count code units, skipping the second unit of each pair | not `.length` |
| `textIsEmpty` | `t === ""` | |
| `decEqText` | `a === b ? Yes : No` | well-formed UTF-16 is a bijection on scalar sequences, so code-unit equality is scalar equality. Proofs are erased, so the payload question above doesn't arise |
| `textCompare` | find the first differing code unit `i`, then compare `codePointAt(i)` | JS `<` would put U+10000 before U+E000 |
| `textUncons` | `codePointAt(0)`, then `slice(1 or 2)` | never cuts a pair |
| `textFold` | collect the code points, then apply `f` from the last to the first in a loop | the definition is a right fold, and strict, so `f` is applied innermost first; pure, so only the result matters |
| `textTrim` | loops over the six whitespace code points | not `.trim()`, which also removes U+00A0, U+2028, U+FEFF |
| `textSplit` | `t.split(sepString)` | a separator is a whole scalar, and in a well-formed string a match can't start inside a pair. `"".split(",")` is `[""]` and `"a,,b"` gives `["a", "", "b"]`, as specified |
| `textJoin` | collect the list into an array, `join(sep)` | |
| `natToText` | `n.toString()` on the `bigint` | decimal, no leading zeros, `"0"` for 0 |
| `textToNat` | `/^[0-9]+$/.test(t) ? Just(BigInt(t)) : Nothing` | `BigInt` alone accepts `" 12"`, `"0x10"` and `""` |
| `textToList`, `textFromList` | loops building or reading a cons list | O(n) now, not O(1) |

A sketch of the two subtle ones:

```js
const textLength = (t) => {
  let k = 0;
  for (let i = 0; i < t.length; i++, k++) {
    const u = t.charCodeAt(i);
    if (u >= 0xd800 && u <= 0xdbff) i++; // a pair is one scalar
  }
  return BigInt(k);
};

const textCompare = (a) => (b) => {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    if (a.charCodeAt(i) !== b.charCodeAt(i)) {
      // At the first difference, codePointAt gives the whole scalar, or (if
      // the high halves matched) the two low halves, which order correctly.
      return a.codePointAt(i) < b.codePointAt(i) ? LESS : GREATER;
    }
  }
  return a.length === b.length ? EQUAL : a.length < b.length ? LESS : GREATER;
};
```

(The reviewer checked this `textCompare` in Node 22.16 against an independent comparator over scalar arrays, on 24,649 pairs of short strings with BMP boundaries, supplementary characters, shared high surrogates and adjacent low surrogates, and found agreement; and checked the `textToNat` pattern on trailing line terminators and the listed invalid forms. That's evidence for the sketches, not verification of the implementation, which the differential tests below must cover.)

**Code that isn't native.** User code (and any prelude code not in the table) can still match on `MkText cs` or build `MkText cs`. The generator compiles:

- **matching** `MkText cs` against a string to `const cs = $textToList(t)`, a loop that builds the cons list, **only if `cs` is used**. `isText (MkText _) = True` converts nothing;
- **constructing** `MkText cs` to `$textFromList(cs)`, a loop that joins the code points;
- **a text literal** to a JS string literal.

Both bridges are loops. They are O(n) where they used to be O(1), so code that repeatedly unwraps and rewraps a text becomes quadratic. The prelude's operations don't, because they're native. The review accepted this for now: document the cost, and defer the string-backed-list variant below until a workload justifies it.

**First-class uses.** `MkText` and the natives must also work as values: `map textLength texts`, `map MkText lists`, `textAppend "prefix"` partially applied. Natives are curried JS functions, like the number natives, so passing or partially applying one needs nothing special; a first-class `MkText` is eta-expanded by the elaborator into a lambda whose body is the constructor, which goes through `$textFromList`. Tests cover each.

**The boundary gets simpler.** Decoding a `Text` keeps today's strict check (no lone surrogates, `StitchwortInputError` with the index) and then returns the string itself, instead of building a list. Encoding returns the string. Both round-trip laws become trivial for well-formed strings. `Text` inside lists, `Maybe` and users' types works the same way, through the same generic codecs.

**Stack safety, stated narrowly.** The guarantee is: *the native implementations and their representation bridges don't use JS call-stack space proportional to text length.* That's not "everything a native calls is stack-safe": `textFold` calls a user's function, which may recurse. It covers the whole export path that the natives and bridges are responsible for: producing a million short `Text`s from `textSplit` and putting them in the internal list, `textToList` on a long text, and encoding a long `List Char` at the boundary. Helpers must avoid unbounded argument spreading too: `String.fromCodePoint(...codes)` with a million codes throws a `RangeError` in V8, so code points are converted in bounded chunks or one at a time. (Measured in Node 22.23: spreading 100,000 codes works; 1,000,000 throws `RangeError: Maximum call stack size exceeded`.)

**Trust.** Proof checking is unaffected: the kernel never sees these implementations. The extractor, already trusted (DESIGN.md §13, "Known gaps"), gains about 15 short functions. A wrong one gives a wrong answer in JS, not a false theorem.

**Gain:** the stack limit goes away for every prelude text operation, and they become fast (see [Expected performance](#expected-performance)). Exports that take or return text skip building and walking lists.

**Cost:** nothing for the checker or the playground's checking; their limits stay.

#### A variant: a string-backed list in JS

To avoid the O(n) conversion when user code matches `MkText cs`, `cs` could be a lazy list object backed by the string and an offset, with `tag`, `head` and `tail` as getters. That makes walking a text's characters O(1) per step, as option B does in the checker. But every list operation in generated code would then see two shapes of cons cell, which V8 handles more slowly at polymorphic sites (**not measured**). Left out unless measurements of real code show the conversion matters.

#### A variant: separately proven fast functions, used only by extraction

Instead of trusted native JS, each slow definition could get a companion written in Stitchwort, tail-recursive or accumulator-based, with a proof that the two are equal (`textLengthFast t = textLength t`). The extractor would compile calls to the original as calls to the companion. The original definitions, and every proof about them, stay unchanged; only the substitution rule ("use the companion of a definition proven equal to it") is trusted, and that rule is small and generic.

This doesn't give compact storage on its own (the companion still walks a cons list), so it doesn't remove the O(n) conversion at the boundary or the memory cost, and the companions would still be slower than `===` or `split`. It also doesn't help the kernel, where the exact-conversion obligation applies anyway. It's a reasonable way to make *user* functions stack-safe later; for the prelude's text operations, native JS gives more for less. So the recommendation doesn't change, but draft 1's claim that optimising an implementation "would change the definitions the proofs are about" was too strong.

### B. Compact text in the checking evaluator

This is the same idea as `Value::Nat`, and has two halves that can be built and reviewed separately.

#### B1. A compact representation, with no native operations

**New term and value forms**, at the *list* level, not the `Text` level, both a shared range of an array:

```rust
// crates/core/src/term.rs
/// `chars[start..end]` as a `List Char`: its expansion is
/// `Cons (MkChar c rfl) (Cons … Nil)`, one cell per character.
Term::Chars(Rc<[char]>, usize, usize),

// crates/core/src/value.rs
/// The same, as a value.
Value::Chars(Rc<[char]>, usize, usize),
```

- **Literals.** `"ab"` elaborates to `MkText (Chars "ab")`: one term, however long. That removes the literal depth limit in the CLI and in WebAssembly. `MkText` stays an ordinary constructor, so matching on `MkText cs` needs nothing new: `cs` is just a compact list.
- **Matching** a `Value::Chars(s, i, j)` in a case on `List`: if `i = j`, take the `Nil` branch; otherwise take `Cons`, with head `MkChar s[i] rfl` and tail `Value::Chars(s, i + 1, j)`. That's exactly what matching its expansion does, in O(1), sharing the array, like matching `Value::Nat(n)` gives `Succ (Value::Nat(n - 1))`. So every list function, the prelude's and users', walks a compact text without ever building it.
- **Lists can be mixed.** `append` on a compact left side walks it and conses each element onto the right side, which can itself be compact. So `"ab" ++ big` is two cons cells in front of a shared `Value::Chars`, exactly the sharing lists have today. Values of the form "some cons cells, then a compact tail" are normal, as `Value::NatAdd` (`k + x`) is for numbers.
- **Conversion.** Two compact ranges are equal if their characters are equal (one slice comparison). A compact range against `Nil` or `Cons` is expanded one step and compared structurally, in the same loop, so it stays stack-safe. Against `Cons (MkChar c h) rest`, the head is compared as `MkChar s[i] rfl`, so `h` must be convertible with `rfl`: a rigid proof variable is not.
- **Quoting** a value back to a term gives `Term::Chars` for a compact tail, sharing the range. Error messages and the printer already print `MkText` of literal characters as a string literal (`pretty.rs`, `text_literal`); that would learn the new term.
- **When a list becomes compact.** Only literals (and, in B2, results of natives whose eligibility has been checked) are compact. A list built from `Cons` cells stays cons cells. Compacting lists as they're built would need to check every proof field is `rfl`, and buys little; the review agreed to leave it out of B1.
- **Registration and binding**, as above: `List`, `Char`, `Text`, their constructors and `isScalar` are registered while the prelude loads, their shapes checked and their hashes pinned.

**No new positivity or termination principle.** `Chars` is a closed inhabitant of an existing type: no new recursive type, no new recursion rule. But passes must still handle it deliberately:

- **structural termination**: descent comes only from the existing `Cons` case of a pattern match. Matching a `Value::Chars` produces a `Cons` with a smaller tail, the same as its expansion; the termination checker, which works on terms, never treats a range or an offset as "smaller" on its own;
- **the audit list.** Every pass that consumes terms or values must handle `Term::Chars` or `Value::Chars` deliberately (most treat it as a closed constant): substitution and shifting; scope checking; `subterms()` and anything built on it (reachability, dependency collection); content hashing; erasure and JS extraction; quotation; pretty printing; the machine and the reference evaluator; conversion; the elaborator's unifier (including the occurs check, pruning and metavariable zonking); the nesting guards; the termination checker; and any `match` on `Term` or `Value` with a catch-all arm, which is where a forgotten case would hide. Adding the variant without a catch-all where possible makes the compiler find most of these.

**Unification tests.** Beyond solving `?c` in `MkText (Cons ?c Nil) ~ "a"`:

- `Cons ?c ?tail ~ Chars "ab"` solves `?c := MkChar 97 rfl` and `?tail := Chars "b"`, consistently;
- a character or proof metavariable that's blocked at first and solved later (`Cons (MkChar ?n ?p) Nil ~ "a"`, where `?n` is solved by another constraint before `?p`) gives the same result as with cons cells;
- `Cons (MkChar 97 h) Nil ~ "a"`, with `h` a rigid proof variable, fails, as it does against the expansion.

**The range representation.** Draft 1 had a suffix offset in the value and none in the term, so quoting a value whose offset isn't 0 would have had to copy the remaining array, and B2's `textSplit` couldn't represent `"ab"` from `"ab,cd"` without copying. With a start and an end in both:

- **quotation** shares the range;
- **splitting** gives ranges of the input;
- **hashing** covers the *logical contents* (a tag, the length, then the code points of `s[start..end]`), never the backing buffer's identity or the offsets, so equal ranges of different buffers hash the same;
- **bounds** are checked when a range is made (`start ≤ end ≤ len`), in one constructor function;
- **memory retention**: a short range keeps a long buffer alive. A range quoted into a checked declaration, or produced by a native, is copied into its own buffer when it's shorter than half the buffer (amortised: the copy is at most the size of the range); an empty range is `Nil`, which releases the buffer entirely. A test checks that keeping only a one-character suffix of a million-character literal doesn't keep the literal alive.

**Representation choice.** `Rc<[char]>` costs 4 bytes per character of *payload*, makes the length of one range O(1), and makes matching one index step. UTF-8 (`Rc<str>` with byte offsets) would be 1 to 4 bytes, with matching still O(1) (decode one scalar), but length O(n). The review agreed to start with `[char]`.

**Trust.** No new *operations*, but the representation's rules (matching, conversion, quoting, the literal's type) are kernel code, and a bug in them is a soundness bug. That's comparable to what `Value::Nat` added: a few hundred lines, by analogy with `native.rs` (an estimate).

**Gain:** long literals; the stored size of literal text. **Not a gain:** steps. `textLength` of a compact text still takes one step per character, since it runs `length`'s definition. And walking a compact range *allocates* a `MkChar` value and a range value per step, where walking an existing cons list allocates nothing, so total allocations may rise for some programs: they're measured separately from retained size.

#### B2. Native operations in the evaluator, only if measurements justify them

A short list of prelude definitions get native implementations, used only when the native's eligibility predicate holds for all its arguments ([Eligibility](#eligibility-when-a-native-may-fire)). Otherwise they unfold as defined. Each must meet the [whole-result obligation](#the-obligation-for-a-native). In order:

| Definition | Native result | Why |
|---|---|---|
| `textLength` | a `Value::Nat` | n steps become one native call (O(1) for one range; O(p) for p cons cells in front) |
| `textCompare` | `Less`, `Equal` or `Greater` | no proof fields in the result |
| `natToText` | a compact text | the most expensive of the three benchmarks (18.9 M steps for 10,000 numbers) |
| `textToNat` | `Maybe` of a number | |
| `textSplit`, `textJoin` | lists of compact texts; a compact text | the split-join benchmark. The separator must be `MkChar c rfl` |
| `decEqText`, last | `Yes rfl`, or the definition's own `No` term | only after a native-on/off comparison of complete results, `No` payloads included, passes. Until then `==` on texts unfolds |

Deliberately **not** native at first:

- `textAppend`. A flat copy of both operands is O(a + b) per call, so a right-nested loop like the benchmark's `repText` (`t ++ repText n t`) becomes quadratic: about 10⁹ characters copied for 100,000 characters (an estimate), against today's linear cost. B1's mixed lists already make `++` cost the length of the left side, with the right side shared, which is what lists do now. A native `++` doesn't *have* to flatten: it could walk a compact left side quickly while producing an ordinary cons prefix that shares the right side, keeping today's asymptotics (though that may not be worth its trusted code), and a rope is another option. The rule: **don't optimise append by flattening away sharing unless workload measurements justify the trade-off.**
- `textFold` and `textUncons`. They take apart one character at a time anyway, which B1 already makes cheap.

**Metering.** A native call that compares two million-character texts, or parses a million-digit number, does real work proportional to its input. It's charged against the step budget in proportion to that work (one step per character examined, or per digit), so a budget still bounds the time a check can take, and `E-RESOURCE` still fires on runaway programs.

**Trust.** Each native joins the trusted base, as the number natives did. A `decEqText` that said `Yes` for `"a"` and `"b"` would let the kernel accept `"a" = "b"`.

### C. A primitive kernel type, Rocq-style

`Text` becomes an opaque primitive type, with operations implemented natively and specified by axioms over a list model (Rocq's `of_to_list`, `length_spec`, `cat_spec` and so on).

- **Gain:** the fastest kernel evaluation, and a representation that can't be confused with lists.
- **Cost:**
  - **Existing proofs break.** `MkText` disappears as a constructor, so `textJoinSplit`, `textFromToList` and everything that matches on `MkText` must be redone against the specification. That alone conflicts with keeping the public constructor and the existing proof terms, and is reason enough not to choose it.
  - **As Rocq does it, the specification is axioms**, and DESIGN.md §12 requires every export, and everything it depends on, to be *assumption-free*. Either every text export would be refused, or the axioms would be exempted from the rule. (Rocq's documentation is evidence about Rocq's design; a different opaque design might avoid axioms, but this note hasn't found one that keeps `MkText`.)
  - **The most trusted code of the three:** every operation, in every evaluator, plus their agreement with the specification.
  - Rocq's float classification bug shows what that trust costs when it fails.

### Also considered

- **Rewriting the prelude's text operations to be tail-recursive.** That changes the definitions the proofs are about, so the laws would need re-proving, and it helps generated JS only. Text-and-io.md (step 3) already rejected it. (The variant that keeps the definitions and adds proven companions is [described under A](#a-variant-separately-proven-fast-functions-used-only-by-extraction).)
- **Making all generated JS stack-safe** with a trampoline or continuation-passing. It slows every call and enlarges the trusted generator; also rejected there.

### Comparison

| | A: JS only | B1: compact representation | B2: + natives | C: primitive type |
|---|---|---|---|---|
| Generated JS limit | removed for prelude operations | unchanged | unchanged | removed |
| Long literals (CLI, WebAssembly) | unchanged | fixed | fixed | fixed |
| Checker: stored size of literal text | unchanged | 4 bytes per character of payload | same | same |
| Checker steps for `textLength` etc. | unchanged | unchanged | one native call, whose work is O(1) to O(n) by [cost category](#costs-three-categories), metered | one call |
| Existing proofs | unchanged | unchanged | unchanged | redone against the specification |
| New trusted code, kernel | none | representation rules | + about 6 natives | type, operations, specification |
| New trusted code, extractor | about 15 natives and two bridges | none | none | operations |
| Exports stay assumption-free | yes | yes | yes | no, as Rocq does it |

## Details that apply to every option

### `Char`

**Leave it as `MkChar code valid` everywhere, for now.** In generated JS it stays `{ tag: "MkChar", code: <bigint> }`, and natives that produce characters (`textUncons`, `textToList`) build those objects. In the evaluator, a compact list hands out `MkChar c rfl` values as it's matched.

A more compact `Char`, a JS `number` holding the code point, would make `textToList` and `textUncons` cheaper. But `charToNat` returns a `Nat`, which is a `bigint` in JS, so each use would convert. It's a separate, smaller decision, and doesn't block anything here. In the evaluator, a `Value::Char(c)` would save an allocation per character matched, but the proof field makes it subtle (it must stand for `MkChar c rfl` exactly), so B1 doesn't include it.

### Literals

- **JS:** a text literal becomes a JS string literal, with lone surrogates impossible (the elaborator refuses them).
- **Evaluator (B1):** `"…"` becomes `MkText (Term::Chars …)`. `'a'` stays `MkChar 97 rfl`.
- A list literal of characters (`['a', 'b']`) stays cons cells. It means the same as `Term::Chars`, and conversion treats them as equal.

### `==` and `++`

- `a == b` on texts elaborates to `toBool (decEqText a b)`. In JS (A) that's `a === b`. In the evaluator it's ordinary evaluation (B1), and stays so in B2 until `decEqText`'s whole-result test passes.
- `a ++ b` on texts elaborates to `textAppend a b`. In JS (A) it's `a + b`. In the evaluator (B1) it shares the right side, with no native.

### Pattern matching on a natively built `Text`

- **JS (A):** a native returns a string, and matching `MkText cs` on it converts to a cons list in a loop, if `cs` is used. Prelude code that matches `MkText` (`textIsEmpty`, `textUncons`, `textToNat`) is native, so this only happens in user code.
- **Evaluator (B):** a native returns `MkText (Value::Chars …)`, and matching is the O(1) rule above. This is the same mechanism as a literal.

### Costs: three categories

"Compact" is a property of a representation, "eligible" is a property of a value's proof fields, and "cheap" is about cost. They differ for lists with cons cells in front:

| Representation | Example | Cost to find its length, or to check eligibility |
|---|---|---|
| One `Value::Chars` range | a literal; a native's result | O(1) for the length; nothing to check |
| p ordinary cons cells, then a compact tail | `"ab" ++ big` in B1 | O(p) |
| An ordinary list of n characters | built by user code from `Cons` | O(n) |

So a native can't check the proof fields of a cons prefix and then be described as O(1). This matters for `repText`: B1's ordinary append rebuilds the left sides as cons cells, so a final native `textLength` still walks a long spine. Likewise, native equality and lexicographic comparison may examine a long common prefix: one evaluator transition, but not constant time, which is why they're [metered](#b2-native-operations-in-the-evaluator-only-if-measurements-justify-them).

### Hashing and caches

- **A new term form needs its own hash tag.** `Term::Chars` hashes as a tag, the length and the code points of its range (not the buffer or offsets), as `Term::Nat` hashes as `"nat"` and its bytes. The serialisation is injective and distinct from every other form's, so the new form adds no structural ambiguity before hashing; as for every form, two different meanings share a hash only if BLAKE3 has a collision. A compact literal and the same characters written as cons cells *will* hash differently, as `3` and `Succ 2` already do. That only costs a cache miss.
- **Dependencies.** `Term::Chars` mentions no declaration, but its meaning depends on `List`, `Cons`, `Nil`, `Char`, `MkChar` and `isScalar`. A declaration containing one must count those as dependencies (for hashing, reachability and extraction), as if it had been written as its expansion.
- **The elaborator must be deterministic** about which form it produces for the same source, or the same program would get a new hash each time (a miss, not a wrong result). It is for literals; quoting must be too.
- **The test cache key gets an automatic build fingerprint.** Test results are cached under the compiler's *version number* (docs/core.md), not its code, and draft 1 proposed a hand-bumped "natives version" on top. That has the same weakness as the version number, which is already the known failure mode. Instead, the build computes a fingerprint (a hash of the sources of `crates/core`, `crates/elab` including the prelude, and the driver's evaluation code, generated by a build script), and the key includes it together with the **effective modes** (natives on or off, compact representation on or off). Invalidating too much is preferred over a fine-grained dependency system for Rust code. A natives-off run therefore never reuses a natives-on result; differential tests also bypass the cache entirely. DESIGN.md §11 already says a hash covers "the identities of any primitives it uses". The generated-JS cache key already has "representation options".

### Stack safety

- **JS (A):** the guarantee [stated above](#a-compact-text-in-generated-javascript-only), tested on the whole export path. User recursion over text still uses the stack; that limit is documented and stays.
- **Evaluator (B):** matching and conversion on compact lists are one step at a time inside the existing machine and conversion loops. A long literal no longer makes a deeply nested term, which is what limits literals today.

### The JavaScript boundary

Strict decoding stays exactly as built: a lone surrogate is refused with `StitchwortInputError` and its index; a `Char` must be exactly one scalar. Under A, a decoded `Text` *is* the input string (strings are immutable, so the "decode into fresh values" rule of DESIGN.md §12 holds trivially), and encoding is the identity. Option B doesn't touch the boundary.

## Soundness and testing

**The danger** is a native, or a representation rule, that disagrees with the list definition. In generated JS that's a wrong answer. In the kernel it's a false theorem (a `decEqText` that says `Yes` for `"a"` and `"b"` lets `rfl` prove `"a" = "b"`), or a changed set of accepted conversions (as `decEqNat`'s `No` shows).

**How to prevent it:**

1. **Keep the native lists short and written down.** DESIGN.md §13 lists them, as it does the number natives. Natives fire only when their eligibility predicates hold, and are bound to the declarations they replace by hash.
2. **A switch that turns text natives off,** in the evaluator (as `disable_natives` does for numbers) and in the extractor (an option to emit the list-based code). The differential tests compare against that independent path, never against expected answers computed by the natives themselves.
3. **An independent oracle for B1.** The machine and the reference evaluator both get the representation rules, written independently. But two evaluators implementing the same new rule can share a mistaken specification, so B1's tests also expand every compact value into ordinary constructors and compare against the *existing* constructor semantics, which tests the central justification directly.

### Three tiers

| Tier | Inputs | Oracle | Establishes |
|---|---|---|---|
| **Small, comprehensive** | every short text over a small alphabet of awkward characters (NUL, U+D7FF, U+E000, U+FFFF, U+10000, U+10FFFF, a combining accent, an emoji, U+00A0, U+2028), and random ones up to a few dozen characters | the old path: constructors only, text natives off, compared as complete core values (including `No` payloads), not printed text or Booleans | semantic agreement |
| **Medium** | thousands to tens of thousands of characters | the stack-safe machine with text natives off (the recursive reference evaluator isn't safe at this depth) | agreement past the reference's depth |
| **Large** | a million characters and more | independently computed expectations (iterative code in the test), laws (`textJoin s (textSplit s t) = t`, lengths add), and smaller checked instances | scalability, not semantics |

The old list-based JS can't be the oracle at large sizes: its inability to handle them is the motivation.

### Extra tests, by area

| Area | Test |
|---|---|
| Proof preservation | `textJoin` with a separator carrying an abstract proof (`MkChar 44 h`), which must not fire the native; native-on/off comparison of complete `Yes` and `No` values |
| Compact representation | empty ranges, nonzero starts, ranges ending before the buffer does, mixed cons/compact tails, quotation of suffixes, retention of a small suffix, wrong-type rejection |
| Open terms | character and proof metavariables before and after solving; rigid proof variables that stay non-canonical |
| Extraction | first-class constructors and natives (`map textLength texts`, `map MkText lists`, partial `textAppend "prefix"`), unused `MkText` fields, native results immediately consumed by ordinary user pattern matches |
| End-to-end scaling | many short split results, one very long result, long `List Char` outputs, conversion failures and resource reporting |
| Registration and caches | a same-typed but changed builtin definition (the native must not fire); a changed native helper (the fingerprint changes); a natives-off run after natives-on results were cached |

### Must-reject examples

DESIGN.md §13's "must reject" examples, each paired with an accepted neighbour:

- proving `"a" = "b"` by `rfl` must be rejected; proving `"ab" = "a" ++ "b"` by `rfl` must be accepted;
- proving `textLess "\u{10000}" "\u{E000}" = True` by `rfl` must be rejected; the same with `False` must be accepted;
- `MkChar 55296 rfl` (U+D800), `MkChar 1114112 rfl`, and `MkChar (2^64 + 97) rfl` must still be rejected with a compact literal nearby.

**`isScalar` against Rust's `char`**, for all 1,114,112 code points, as regression coverage of the forward property ([Binding](#binding-natives-to-the-definitions-they-replace) says what it does and doesn't establish).

**Proofs of the natives?** Not proposed. The natives are Rust and JS, outside the language. Mutation testing (`cargo mutants`) of the new code is the practical check that the tests bite.

## Expected performance

All of these are **estimates**, except where marked measured.

**Generated JS (A).** Measured, for comparison: in Node 22.23 on an arm64 Mac, with plain JS on a 1,000,000-character string, counting scalars in a loop took about 1.5 ms; `split(",")` 4.4 ms; split then join 8.5 ms; `===` against a fresh copy 0.2 ms; 20,000 right-nested `"abcd," + t` 0.07 ms (V8's ropes, construction only: flattening is deferred to the first read, so a construct-then-consume benchmark is needed to see the whole cost). Building today's cons-of-`MkChar` list for the same string took about 21 ms, before any operation runs on it. So A should take prelude text operations from failing past a few thousand characters to working on millions, at a few milliseconds each (estimate). User code that recurses per character is unchanged.

**Evaluator, B1.** Three things are measured separately, because they move differently:

- **stored payload** of literal text: 4 bytes per character in the array, against two cells per character today (not measured separately; the benchmarks' 500 to 650 bytes per input character is peak heap *including intermediates*, so it doesn't support a "100 times smaller" claim for whole programs);
- **peak live heap** of the benchmarks: should fall where literals dominate, and change little where intermediate cons lists do (`text-append` rebuilds its cons prefixes);
- **total allocations**: may *rise* for programs that walk compact text, since each step allocates a `MkChar` and a range value, where walking existing cons cells allocates nothing.

Literal length is no longer limited by recursion depth. Steps hardly change.

**Evaluator, B2.** `textLength` and `textCompare` on single ranges become one call each, charged in proportion to the characters examined. `text-split-join` should fall from 2.3 M steps to roughly the program's own steps plus the metered native work. `text-nat-to-text` should fall from 18.9 M steps to around a hundred thousand plus metering. `text-append` mostly stays (no native `++`), apart from its final `textLength`, which still walks the cons prefixes.

## Recommendation

1. **Build option A first.** It fixes the problem users of the main use case hit (exports that fail on a few thousand characters), it touches no proof checking, and the differential tests that would check it largely exist. Keep `Char` as it is.
2. **Then B1,** when long literals or memory matter, particularly in the playground, once the expansion invariant, the audit list and the binding policy above are agreed. Keep canonical literals distinct from lists containing arbitrary proofs, and use shared ranges.
3. **B2 only where a benchmark shows the need,** starting with data-producing natives (`textLength`, `textCompare`, `natToText`), with eligibility predicates, metering, the build fingerprint and the natives-off tests in the same change. `decEqText` only after its whole-result test passes.
4. **Audit `decEqNat`** against the same obligation, separately.
5. **Not option C.**

## Review answers

The review's answers to draft 1's open questions:

1. **Is agreement with the list definition the right criterion?** Yes, under the reference conversion rules, including proof payloads. Canonical (`rfl`) input proofs alone are insufficient.
2. **Is O(n) conversion when matching `MkText` acceptable?** Yes initially; document it, skip it for unused fields, defer the string-backed list.
3. **Is `List Char` the right level?** Yes. Specify the expansion invariant and audit every term and value consumer.
4. **`Rc<[char]>` or UTF-8?** `Rc<[char]>` first; consider shared ranges (adopted).
5. **Native `textAppend`?** Not initially; a rope isn't the only possible future optimisation.
6. **Hand-bumped natives version or hash?** An automatically generated build fingerprint, covering supporting code and effective modes.
7. **Compact lists as they're built?** Not in B1.

## What I couldn't verify

- The **text literal limit in the playground** (WebAssembly, 128 KiB guard) wasn't measured; it's inferred from the measured limit for list literals.
- **V8's thresholds** for when `+` makes a `ConsString` and `slice` a `SlicedString`, rather than copying: V8's documentation says very short results are copied, but gives no current number.
- **How Rocq's VM and native compilers reduce `PrimString`** operations: the reference manual says the reduction machines have dedicated rules for primitives in general.
- **Lean's compiled string operations** are described from the reference manual ("overridden with an efficient implementation in runtime code"). I didn't read the runtime's C source.
- **The cost of polymorphic property access in V8** for the string-backed list variant.
- The **trusted code size** estimates for B1 and B2 are by analogy with `native.rs`, not from a prototype.
- That `sameNo` above is **accepted with natives off** is reasoned (both sides then unfold the same definition on the same arguments), not run: there's no switch for it in the CLI.

## Sources

- Lean: [Strings, in the reference manual](https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/); [4.25.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/) (`String` redefined as valid UTF-8 byte arrays); the kernel's [`type_checker.cpp`](https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp) (`string_lit_to_constructor`, `try_string_lit_expansion`, and native `Nat` operations only).
- Rocq: [primitive objects, in the reference manual (8.20)](https://docs.rocq-prover.org/v8.20/refman/language/core/primitive.html) ("These primitive declarations are regular axioms"); [`PrimStringAxioms` (9.0)](https://rocq-prover.org/doc/v9.0/corelib/Corelib.Strings.PrimStringAxioms.html); [kernel `Pstring` module](https://ocaml.org/p/rocq-runtime/9.1.0/src/rocq-runtime.kernel/pstring.ml.html) (`max_length_int = 16777211`); [releases](https://rocq-prover.org/releases) (primitive strings in 8.20.0); the `SFClassify` proof of `False`, fixed in 8.15.2 ([coq/coq#16096](https://github.com/coq/coq/issues/16096), [#16101](https://github.com/coq/coq/pull/16101)), as listed in the 8.15 changelog.
- Agda: [`Agda.Builtin.String`](https://www.cs.cmu.edu/~runmingl/afat/Agda.Builtin.String.html) (a rendered copy); [`Agda.Builtin.String.Properties`](https://github.com/agda/agda/blob/master/src/data/lib/prim/Agda/Builtin/String/Properties.agda) (`primStringToListInjective`, `primStringFromListInjective`).
- Idris 2: [`Data.String` source](https://idris-lang.org/Idris2/base/source/Data.String.html) (`strM` with `assert_total` and `believe_me`).
- F\*: [`FStar.String.fsti`](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.String.fsti) ("Some lemmas (admitted for now as we don't have a model)").
- Unison: [`Unison.Util.Rope`](https://github.com/unisonweb/unison/blob/trunk/lib/unison-util-rope/src/Unison/Util/Rope.hs) and `Unison.Util.Text` (`newtype Text = Text (R.Rope Chunk)`).
- Koka: [`kklib/include/kklib/string.h`](https://github.com/koka-lang/koka/blob/master/kklib/include/kklib/string.h) (valid UTF-8; small, normal and raw strings); [`std/core/sslice`](https://github.com/koka-lang/koka/blob/master/lib/std/core/sslice.kk).
- V8: [Strings in V8](https://chromium.googlesource.com/v8/v8.git/+/main/docs/objects/strings.md) (`ConsString`, `SlicedString`, flattening).
- The external review of draft 1 (15 October 2026), not in the repository.
- This repository: [text-and-io.md](text-and-io.md) (the contract, and step 3's measurements), [native-numbers.md](native-numbers.md), [docs/core.md](../core.md) ("Numbers", "Tests and content hashes"), DESIGN.md §11 to §13, `bench/baseline.toml`.
