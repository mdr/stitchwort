# Proposal: compact text

**Status:** draft 1, 15 October 2026. **Awaiting external review.** This is design only; nothing here is implemented. It is step 7 of [the text proposal](text-and-io.md#making-it-fast-in-stages), "compact text in generated JS, then possibly in the checking evaluator".

## Summary

`Text` is defined as a list of characters, and the proofs about it are proofs about that list. This note proposes keeping that definition as the **specification**, and storing text compactly underneath it, in two independent stages:

1. **Generated JavaScript first (option A).** Extracted code stores a `Text` as a JS string, and about 15 prelude text operations get native JS implementations. The kernel doesn't change, and nothing new is trusted by proof checking; the extractor, which is already trusted, grows. This removes today's limit of a few thousand characters in generated code.
2. **Then the checking evaluator, in two halves (option B).** First a compact *representation* with no native operations: a text literal becomes one term, and a `List Char` can be stored as a slice of a character array, which pattern matching takes apart one element at a time, the way a compact number is taken apart into `Succ n`. Later, and only where measurements justify it, a short list of native operations, each tested against its own definition with natives switched off.

A primitive string type in the kernel, as Rocq's `PrimString` does it (option C), is not recommended: it would replace proofs with axioms, and Stitchwort's exports must be free of axioms.

The rest of the note is written for a reviewer who knows dependent types and compilers but not this codebase.

## Background

### Stitchwort in brief

Stitchwort is a toy language: strict, pure, total and dependently typed, written in Rust. Its main use is writing library functions, proving things about them, and calling them from a JavaScript or TypeScript application. The compiler also runs in the browser as WebAssembly (the "playground").

The parts that matter here:

- **A small kernel** re-checks everything the elaborator produces. It decides definitional equality by evaluating to values and comparing them (normalisation by evaluation). It has `J`, but no axiom K and no definitional proof irrelevance.
- **Two evaluators share the kernel's data types.** The real one (`crates/core/src/value.rs`) is an abstract machine with an explicit stack, so long lists don't overflow the Rust stack. A recursive reference evaluator (`crates/core/src/reference.rs`) exists only to test it: they share data types and the native number functions, but no evaluation code.
- **Extraction to JavaScript** (DESIGN.md §12) erases types and proofs and generates an ES module. Each export decodes its inputs, checks them, computes, and encodes the result. The extractor and the codecs are trusted, not verified.
- **Content hashing** (DESIGN.md §11). Every checked declaration has a BLAKE3 hash of its elaborated form. Test results are cached under `<compiler version>-<test hash>`.

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
- eight prelude definitions (`add`, `sub`, `mul`, `leq`, `eqNat`, `divFuel`, `decEqNat`, `eqNatRefl`) have **native implementations**, used only when every argument is a number. Otherwise they unfold as defined, so proofs by induction are unaffected. A native `decEqNat` returns `Yes rfl`, or `No (natNeq m n rfl)` using a prelude lemma, so even its proof part is an ordinary term;
- the natives are **registered by name** while the prelude loads; registration checks each one's type and arity, and the shapes of `Nat`, `Bool` and `Decidable` (`E-BUILTIN`). `crates/driver/tests/natives.rs` compares each native with its own definition, run with natives switched off, on every small input and on random larger ones. The natives are listed as trusted in DESIGN.md §13;
- extracted JS uses `bigint` and native operators for the same definitions.

This proposal reuses that pattern for text wherever it can.

## The problems, measured

**Generated JavaScript stops at a few thousand characters.** JS engines don't eliminate tail calls, and `length`, `append`, `textSplit`, `textJoin`, `==`, `textCompare` and `textFold` aren't tail-recursive. Measured in Node 22 with its default stack (text-and-io.md, step 3), the longest text each handled was about: `textLength` 8,000, `textSplit` 5,500 to 6,100, `textJoin` 6,800, `==` 6,100, `textToNat` 3,000. Past that the export throws `StitchwortResourceError`. A function's tail calls to itself already compile to loops, so `textTrim`, `natToText` and a user's accumulator loops are unlimited. Rewriting the others to be tail-recursive would change the definitions the proofs are about.

**The checking evaluator copes with length but not literals.** Since the evaluator became an abstract machine, a release build splits a 100,000-character text and takes the length of a 200,000-character one. But long *literals* stop at about 1,800 characters in a 2 MiB thread (about 75,000 in the CLI), because recursive passes walk the literal's term, which is nested once per character (TODO.md). The playground's WebAssembly build has a 128 KiB guard and handles list literals of about 200 elements; I haven't measured text literals there, but they have the same shape, so a similar limit is likely (**not verified**).

**Text is heavy.** Each character is a cons cell and a `MkChar` cell, each holding two values. From `bench/baseline.toml` (counts are deterministic):

| Benchmark | What it does | Steps | Allocations | Peak heap |
|---|---|---|---|---|
| `text-append` | `textLength (repText 20000 "abcd,")`: 20,000 right-nested `++`, 100,000 characters | 4.76 M | 1.72 M | 51.8 MB |
| `text-split-join` | `textLength (textJoin ',' (textSplit ',' big))`, 10,000 characters | 2.29 M | 0.82 M | 6.6 MB |
| `text-nat-to-text` | `natToText` on 10,000 numbers of up to 11 digits | 18.9 M | 6.74 M | 9 KB |

Peak heap includes intermediate results, but it works out at roughly 500 to 650 bytes per character in the first two.

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
- Making all generated JS stack-safe. User code that recurses once per character is still limited by the JS stack; only the prelude's operations are lifted.

## What other systems do

| System | What proofs see | What runs | What's trusted |
|---|---|---|---|
| **Lean 4**, kernel | Until 4.24, a structure over `List Char`; since 4.25, a `ByteArray` with a proof of valid UTF-8, with the list view still available | String literals are a kernel literal form, expanded to `String.ofList [chars]` only when a projection, match or definitional-equality check needs it. No native *string* operations in the kernel (only `Nat` ones, with GMP) | The literal expansion |
| **Lean 4**, compiled code | (same) | UTF-8 byte arrays with cached size and length; operations "overridden with an efficient implementation in runtime code", mutating in place when unshared | The runtime's C implementations, which the kernel never sees |
| **Rocq `PrimString`** (8.20, Jan 2025) | An opaque primitive type, specified by axioms in terms of a list model (`to_list`, `of_list`) | A native OCaml string of bytes, at most 16,777,211 long; the manual says the reduction machines have dedicated rules for primitive operations | The axioms, shown by `Print Assumptions`, and every reduction machine's implementation |
| **Rocq `PrimInt63`, floats, `PArray`** | Opaque primitives with specification axioms | Native, in all three reduction machines | The same. A wrong float classification allowed a proof of `False` from 8.11 until 8.15.2 |
| **Agda** | An opaque built-in `String`, with primitives `primStringToList`, `primStringFromList`, `primStringUncons`, `primStringAppend` | Native (Haskell `Text`, JS strings) | The primitives, and two postulated properties: `primStringToList` and `primStringFromList` are injective |
| **Idris 2** | A primitive `String`. The view `strM` is built from primitives with `assert_total` and `believe_me` | Native | Every `believe_me` |
| **F\*** | An abstract `string`, with `list_of_string` and `string_of_list` and their round trips stated as `val`s; further lemmas "admitted for now as we don't have a model" | Native in each backend | The admitted lemmas |
| **Unison** (not dependently typed) | n/a | A rope: a size-balanced tree of chunks of Haskell `Text` | n/a |
| **Koka** (not dependently typed) | n/a | Valid UTF-8 always; small strings (at most 7 bytes) unboxed; slices (`sslice`) as views | n/a |
| **V8** (what our generated JS runs on) | n/a | Ropes: `a + b` makes a `ConsString` (two pointers), flattened to a sequential string when read or too deep; `slice` makes a `SlicedString` (parent, offset, length). Very short results are copied instead | n/a |

What this says for Stitchwort:

- **Lean is the closest match**, and its kernel shows how little is needed: the literal is compact, and is expanded to the constructor form on demand. Its speed comes from compiled code with native implementations that the kernel never trusts. That is option A for the runtime and the first half of option B for the kernel.
- **Every system with an opaque string type pays in trusted axioms** (Rocq, Agda, Idris, F\*). Stitchwort's list definition gives it the round-trip lemmas and `textJoinSplit` as real proofs, which is worth keeping.
- **Rocq's float bug** is the concrete risk of native reductions in a kernel: a native that disagrees with its specification proves `False`.
- **V8 already makes `+` and `slice` cheap**, so generated code can use them directly.

## What "the same meaning" must mean

The list definitions stay the specification. A compact representation is correct if nothing that can be observed changes, which means four things:

1. **Same values.** Every compact value stands for exactly one ordinary value, built from `MkText`, `Cons`, `Nil` and `MkChar c rfl`, and every operation on it gives the result that evaluating the definition would. In the kernel, "the same" means *definitionally* equal, not merely provably equal.
2. **Same definitional equalities.** The kernel must accept exactly the same conversions. A compact `"ab"` and `MkText (Cons 'a' (Cons 'b' Nil))` must be convertible, and two compact texts must be convertible exactly when their characters are equal.
3. **Same proof fields.** A compact character stands for `MkChar c rfl`, never `MkChar c h` for some other proof `h`. The kernel has no definitional proof irrelevance, so `MkChar 97 h` (with `h` a variable) and `MkChar 97 rfl` are different values, even though `charExt` proves them equal. Two consequences:
   - a list can only be stored compactly if every proof in it *is* `rfl`, not merely provably equal to it;
   - expanding a compact character produces `MkChar c rfl`, which is well-typed only if `isScalar c` computes to `True` for every scalar value `c`. Rust's `char` and JS's well-formed strings hold exactly the scalar values, so the prelude's `isScalar` must hold exactly those too. That is a fact to test exhaustively (all 1,114,112 code points), not assume.
4. **Same results in generated JS**, after encoding, as the reference evaluator gives, which is what the existing differential tests check.

The **round-trip lemmas** are what make this robust: code that goes through `textToList`/`textFromList` and their lemmas, rather than `MkText`'s structure, doesn't depend on the representation at all. But compact text must also support code that matches on `MkText` directly, because the prelude's own proofs do (`textJoinSplit` matches `MkText cs`).

## The options

### A. Compact text in generated JavaScript only

**The kernel and the checking evaluator don't change.** Generated code represents a `Text` as a well-formed JS string, and prelude text operations as native JS.

**Representation:**

| Stitchwort | Generated JS today | Under option A |
|---|---|---|
| `Text` | `{ tag: "MkText", chars: <cons list> }` | a well-formed string |
| `Char` | `{ tag: "MkChar", code: <bigint> }` | unchanged (see [`Char`](#char)) |
| `List Char` | cons cells | unchanged |

**Native operations.** Each replaces a prelude definition in generated code, as `native_js` already does for numbers (`crates/js/src/lib.rs`). All work on scalar values, never on UTF-16 code units:

| Definition | Native JS, in outline | Note |
|---|---|---|
| `textAppend` | `a + b` | V8 makes a rope; both inputs are well-formed, so the result is |
| `textLength` | count code units, skipping the second unit of each pair | not `.length` |
| `textIsEmpty` | `t === ""` | |
| `decEqText` | `a === b ? Yes : No` | well-formed UTF-16 is a bijection on scalar sequences, so code-unit equality is scalar equality |
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

**Code that isn't native.** User code (and any prelude code not in the table) can still match on `MkText cs` or build `MkText cs`. The generator compiles:

- **matching** `MkText cs` against a string to `const cs = $textToList(t)`, a loop that builds the cons list;
- **constructing** `MkText cs` to `$textFromList(cs)`, a loop that joins the code points.

Both are loops, so they don't use the stack. They are O(n) where they used to be O(1), so code that repeatedly unwraps and rewraps a text becomes quadratic. The prelude's operations don't, because they're native. [Open question 2](#open-questions-for-the-reviewer) asks whether that's acceptable.

**The boundary gets simpler.** Decoding a `Text` keeps today's strict check (no lone surrogates, `StitchwortInputError` with the index) and then returns the string itself, instead of building a list. Encoding returns the string. Both round-trip laws become trivial for well-formed strings. `Text` inside lists, `Maybe` and users' types works the same way, through the same generic codecs.

**Trust.** Proof checking is unaffected: the kernel never sees these implementations. The extractor, already trusted (DESIGN.md §13, "Known gaps"), gains about 15 short functions. A wrong one gives a wrong answer in JS, not a false theorem.

**Gain:** the stack limit goes away for every prelude text operation, and they become fast (see [Expected performance](#expected-performance)). Exports that take or return text skip building and walking lists.

**Cost:** nothing for the checker or the playground's checking; their limits stay.

#### A variant: a string-backed list in JS

To avoid the O(n) conversion when user code matches `MkText cs`, `cs` could be a lazy list object backed by the string and an offset, with `tag`, `head` and `tail` as getters. That makes walking a text's characters O(1) per step, as option B does in the checker. But every list operation in generated code would then see two shapes of cons cell, which V8 handles more slowly at polymorphic sites (**not measured**). I'd leave it out unless measurements of real code show the conversion matters.

### B. Compact text in the checking evaluator

This is the same idea as `Value::Nat`, and has two halves that can be built and reviewed separately.

#### B1. A compact representation, with no native operations

**New term and value forms**, at the *list* level, not the `Text` level:

```rust
// crates/core/src/term.rs
/// `Cons (MkChar c₀ rfl) (Cons … Nil)`: a `List Char`, stored compactly.
Term::Chars(Rc<[char]>),

// crates/core/src/value.rs
/// `chars[start..]` as a `List Char`: the same as cons cells of
/// `MkChar c rfl`, ending in `Nil`.
Value::Chars(Rc<[char]>, usize),
```

- **Literals.** `"ab"` elaborates to `MkText (Chars "ab")`: one term, however long. That removes the literal depth limit in the CLI and in WebAssembly. `MkText` stays an ordinary constructor, so matching on `MkText cs` needs nothing new: `cs` is just a compact list.
- **Matching** a `Value::Chars(s, i)` in a case on `List`: if `i` is at the end, take the `Nil` branch; otherwise take `Cons`, with head `MkChar s[i] rfl` and tail `Value::Chars(s, i + 1)`. That is O(1) and shares the array, like matching `Value::Nat(n)` gives `Succ (Value::Nat(n - 1))`. So every list function, the prelude's and users', walks a compact text without ever building it.
- **Lists can be mixed.** `append` on a compact left side walks it and conses each element onto the right side, which can itself be compact. So `"ab" ++ big` is two cons cells in front of a shared `Value::Chars`, exactly the sharing lists have today. Values of the form "some cons cells, then a compact tail" are normal, as `Value::NatAdd` (`k + x`) is for numbers.
- **Conversion.** Two compact lists are equal if their remaining characters are equal (one slice comparison). A compact list against `Nil` or `Cons` is expanded one step and compared structurally, in the same loop, so it stays stack-safe. The elaborator's unifier needs the same rule, so `MkText (Cons ?c Nil)` unifies with `"a"` and solves `?c`.
- **Quoting** a value back to a term gives `Term::Chars` for a compact tail. Error messages and the printer already print `MkText` of literal characters as a string literal (`pretty.rs`, `text_literal`); that would learn the new term.
- **When a list becomes compact.** Only literals (and, in B2, results of natives) are compact. A list built from `Cons` cells stays cons cells. Compacting lists as they're built would need to check every proof field is `rfl`, and buys little.
- **Registration**, as for `Nat`: `List`, `Char`, `Text` and `isScalar` are registered while the prelude loads, with their shapes checked (`E-BUILTIN`), and a kernel test that checks `isScalar c = True` holds for exactly the scalar values (see [What "the same meaning" must mean](#what-the-same-meaning-must-mean), point 3).

**Trust.** No new *operations*, but the representation's rules (matching, conversion, quoting, the literal's type) are kernel code, and a bug in them is a soundness bug. That's comparable to what `Value::Nat` added: a few hundred lines, by analogy with `native.rs` (an estimate).

**Representation choice.** `Rc<[char]>` costs 4 bytes per character, makes the length O(1), and makes matching one index step. UTF-8 (`Rc<str>` with a byte offset) would be 1 to 4 bytes, with matching still O(1) (decode one scalar), but length O(n). For a toy, `[char]` is simpler, and still about 100 times smaller than today. Which to use is [open question 4](#open-questions-for-the-reviewer).

**Gain:** long literals; memory. **Not a gain:** steps. `textLength` of a compact text still takes one step per character, since it runs `length`'s definition. That's what B2 is for.

#### B2. Native operations in the evaluator, only if measurements justify them

A short list of prelude definitions get native implementations, used only when every argument is fully compact text (a `MkText` of a list that is cons cells of `MkChar c rfl` with literal codes, ending in `Nil` or a compact tail). Otherwise they unfold as defined. Candidates, in order of likely benefit:

| Definition | Native result | Why |
|---|---|---|
| `textLength` | a `Value::Nat` | O(1) instead of n steps |
| `decEqText` | `Yes rfl`, or `No (textNeq a b rfl)` | `==` on texts in `-- run:` cases, tests and `rfl` proofs. `textNeq` would be a prelude lemma, as `natNeq` is for numbers. `Yes rfl` is well-typed because the two sides are then convertible |
| `textCompare` | `Less`, `Equal` or `Greater` | |
| `textSplit`, `textJoin` | lists of compact texts | the split-join benchmark |
| `natToText`, `textToNat` | compact text; `Maybe` of a number | `natToText` is the most expensive of the three benchmarks (18.9 M steps for 10,000 numbers) |

Deliberately **not** native at first:

- `textAppend`. A flat copy is O(a + b) per call, so a right-nested loop like the benchmark's `repText` (`t ++ repText n t`) becomes quadratic: about 10⁹ characters copied for 100,000 characters (an estimate), against today's linear cost. B1's mixed lists already make `++` cost the length of the left side, with the right side shared, which is what lists do now. If a native `++` is wanted later, it needs a rope (like V8's `ConsString` or Unison's `Rope`), and that's more trusted code.
- `textFold` and `textUncons`. They take apart one character at a time anyway, which B1 already makes cheap.

**Trust.** Each native joins the trusted base, as the number natives did. A wrong `decEqText` would let the kernel accept `"a" = "b"`.

### C. A primitive kernel type, Rocq-style

`Text` becomes an opaque primitive type, with operations implemented natively and specified by axioms over a list model (Rocq's `of_to_list`, `length_spec`, `cat_spec` and so on).

- **Gain:** the fastest kernel evaluation, and a representation that can't be confused with lists.
- **Cost:**
  - **Existing proofs break.** `MkText` disappears, so `textJoinSplit`, `textFromToList` and everything that matches on `MkText` must be redone through axioms.
  - **The axioms are assumptions**, and DESIGN.md §12 requires every export, and everything it depends on, to be *assumption-free*. Either every text export would be refused, or the axioms would have to be exempted from the rule, weakening it.
  - **The most trusted code of the three:** every operation, in every evaluator, plus the axioms' agreement with them.
  - Rocq's float classification bug shows what that trust costs when it fails.

### Also considered

- **Rewriting the prelude's text operations to be tail-recursive.** It changes the definitions the proofs are about, so the laws would need re-proving, and it helps generated JS only. Text-and-io.md (step 3) already rejected it.
- **Making all generated JS stack-safe** with a trampoline or continuation-passing. It slows every call and enlarges the trusted generator; also rejected there.

### Comparison

| | A: JS only | B1: compact representation | B2: + natives | C: primitive type |
|---|---|---|---|---|
| Generated JS limit | removed for prelude operations | unchanged | unchanged | removed |
| Long literals (CLI, WebAssembly) | unchanged | fixed | fixed | fixed |
| Checker memory | unchanged | about 4 bytes per character | same | same |
| Checker steps for `textLength` etc. | unchanged | unchanged | O(1) per call | O(1) |
| Existing proofs | unchanged | unchanged | unchanged | rewritten against axioms |
| New trusted code, kernel | none | representation rules | + about 6 natives | type, operations, axioms |
| New trusted code, extractor | about 15 natives | none | none | operations |
| Exports stay assumption-free | yes | yes | yes | no, without an exemption |

## Details that apply to every option

### `Char`

**Leave it as `MkChar code valid` everywhere, for now.** In generated JS it stays `{ tag: "MkChar", code: <bigint> }`, and natives that produce characters (`textUncons`, `textToList`) build those objects. In the evaluator, a compact list hands out `MkChar c rfl` values as it's matched.

A more compact `Char`, a JS `number` holding the code point, would make `textToList` and `textUncons` cheaper. But `charToNat` returns a `Nat`, which is a `bigint` in JS, so each use would convert. It's a separate, smaller decision, and doesn't block anything here. In the evaluator, a `Value::Char(c)` would save an allocation per character matched, but the proof field makes it subtle (it must stand for `MkChar c rfl` exactly), so B1 doesn't include it.

### Literals

- **JS:** a text literal becomes a JS string literal, with lone surrogates impossible (the elaborator refuses them).
- **Evaluator (B1):** `"…"` becomes `MkText (Term::Chars …)`. `'a'` stays `MkChar 97 rfl`.
- A list literal of characters (`['a', 'b']`) stays cons cells. It means the same as `Term::Chars`, and conversion treats them as equal.

### `==` and `++`

- `a == b` on texts elaborates to `toBool (decEqText a b)`. In JS (A) that's `a === b`. In the evaluator it's ordinary evaluation (B1), or a native returning `Yes rfl` or `No (textNeq a b rfl)` (B2).
- `a ++ b` on texts elaborates to `textAppend a b`. In JS (A) it's `a + b`. In the evaluator (B1) it shares the right side, with no native.

### Pattern matching on a natively built `Text`

- **JS (A):** a native returns a string, and matching `MkText cs` on it converts to a cons list in a loop. Prelude code that matches `MkText` (`textIsEmpty`, `textUncons`, `textToNat`) is native, so this only happens in user code.
- **Evaluator (B):** a native returns `MkText (Value::Chars …)`, and matching is the O(1) rule above. This is the same mechanism as a literal.

### Hashing and caches

- **A new term form needs its own hash tag.** `Term::Chars` would hash as a tag, a count and the code points, as `Term::Nat` hashes as `"nat"` and its bytes. The encoding is injective and distinct from every other form's, so two different meanings can't share a hash. A compact literal and the same characters written as cons cells *will* hash differently, as `3` and `Succ 2` already do. That only costs a cache miss.
- **The elaborator must be deterministic** about which form it produces for the same source, or the same program would get a new hash each time (a miss, not a wrong result). It is for literals; quoting must be too.
- **Native behaviour must be in the cache key.** Test results are cached under the compiler's *version number* (docs/core.md), not its code. A test's result can depend on a native, so fixing a native without changing the version would leave stale cached results. I propose a small "natives version" in the test cache key, bumped whenever a native's behaviour changes. DESIGN.md §11 already says a hash covers "the identities of any primitives it uses". The generated-JS cache key already has "representation options", which option A's switch belongs in.

### Stack safety

- **JS (A):** every native is a loop, and conversions to and from lists are loops, so prelude text operations don't use the stack. User recursion over text still does; that limit is documented and stays.
- **Evaluator (B):** matching and conversion on compact lists are one step at a time inside the existing machine and conversion loops. A long literal no longer makes a deeply nested term, which is what limits literals today.

### The JavaScript boundary

Strict decoding stays exactly as built: a lone surrogate is refused with `StitchwortInputError` and its index; a `Char` must be exactly one scalar. Under A, a decoded `Text` *is* the input string (strings are immutable, so the "decode into fresh values" rule of DESIGN.md §12 holds trivially), and encoding is the identity. Option B doesn't touch the boundary.

## Soundness and testing

**The danger** is a native, or a representation rule, that disagrees with the list definition. In generated JS that's a wrong answer. In the kernel it's a false theorem: a `decEqText` that says `Yes` for `"a"` and `"b"` lets `rfl` prove `"a" = "b"`, and from there anything.

**How to prevent it:**

1. **Keep the native lists short and written down.** DESIGN.md §13 lists them, as it does the number natives. Natives only fire on fully compact inputs whose proof fields are literally `rfl`. Otherwise the definition unfolds.
2. **A switch that turns text natives off,** in the evaluator (as `disable_natives` does for numbers) and in the extractor (an option to emit the list-based code). The differential tests compare against that independent path, never against expected answers computed by the natives themselves.
3. **Differential tests, by layer:**
   - **Evaluator natives (B2):** for each native, natives-on against natives-off on every short text over a small alphabet, plus random texts built from awkward characters (NUL, U+D7FF, U+E000, U+FFFF, U+10000, U+10FFFF, a combining accent, an emoji, U+00A0, U+2028), as `crates/driver/tests/natives.rs` does for numbers. Include the specification counterexamples from text-and-io.md (`"\u{10000}" < "\u{E000}"` is false; `" 12"`, `"+5"`, `"0x10"` and `""` aren't numbers).
   - **Representation (B1):** compact against cons cells for matching, conversion both ways, unification with metavariables inside, quoting, and printing; nested patterns (`MkText (Cons c (Cons d rest))`); a `MkChar c h` with `h` a variable (must *not* be compacted or treated as `rfl`); and the "must reject" pairs below.
   - **The reference evaluator** gets the same representation rules, written independently, and the machine-against-reference tests run over text programs.
   - **JS (A):** the existing differential tests (55 `-- run:` cases, 100 random inputs per export) already compare generated JS with the reference evaluator. They gain long inputs (a million characters), and a run of the same tests against the natives-off JS.
4. **"Must reject" examples** (DESIGN.md §13), each paired with an accepted neighbour:
   - proving `"a" = "b"` by `rfl` must be rejected; proving `"ab" = "a" ++ "b"` by `rfl` must be accepted;
   - proving `textLess "\u{10000}" "\u{E000}" = True` by `rfl` must be rejected; the same with `False` must be accepted;
   - `MkChar 55296 rfl` (U+D800) must still be rejected with a compact literal nearby.
5. **`isScalar` against Rust's `char`**, for all 1,114,112 code points, in a test, since every compact character's `rfl` relies on it.
6. **Proofs of the natives?** Not proposed. The natives are Rust and JS, outside the language. Mutation testing (`cargo mutants`) of the new code is the practical check that the tests bite.

## Expected performance

All of these are **estimates**, except where marked measured.

**Generated JS (A).** Measured, for comparison: in Node 22.23 on an arm64 Mac, with plain JS on a 1,000,000-character string, counting scalars in a loop took about 1.5 ms; `split(",")` 4.4 ms; split then join 8.5 ms; `===` against a fresh copy 0.2 ms; 20,000 right-nested `"abcd," + t` 0.07 ms (V8's ropes). Building today's cons-of-`MkChar` list for the same string took about 21 ms, before any operation runs on it. So A should take prelude text operations from failing past a few thousand characters to working on millions, at a few milliseconds each (estimate: within a small factor of the measured plain-JS figures). User code that recurses per character is unchanged.

**Evaluator, B1.** Memory for literal text drops from roughly 500 bytes per character (inferred from the benchmarks' peak heap, which includes intermediates) to 4. Literal length is no longer limited by recursion depth. Steps hardly change: functions still take one step per character, though matching a compact list should allocate less than walking cons cells (one `MkChar` and one slice value per step, versus cells already built).

**Evaluator, B2.** `textLength`, `==` and `textCompare` on compact texts become one step. `text-split-join` should fall from 2.3 M steps to a few hundred (the program's own steps). `text-nat-to-text` should fall from 18.9 M steps to around a hundred thousand (the loop's own arithmetic). `text-append` mostly stays (no native `++`), apart from its final `textLength`.

## Recommendation

1. **Build option A first.** It fixes the problem users of the main use case hit (exports that fail on a few thousand characters), it touches no proof checking, and the differential tests that would check it largely exist. Keep `Char` as it is.
2. **Then B1,** when long literals or memory matter, particularly in the playground. It adds no native operations, and the representation rules mirror `Value::Nat`'s.
3. **B2 only where a benchmark shows the need,** starting with `textLength` and `decEqText`, with the natives-off differential tests and a "natives version" in the test cache key in the same change.
4. **Not option C.**

## Open questions for the reviewer

1. **Is "the list definition is the specification, and natives must agree with it definitionally" the right correctness criterion?** In particular, is it enough that natives fire only on inputs whose proof fields are literally `rfl`, so they never have to decide anything about other proofs?
2. **In option A, is the O(n) conversion when user code matches `MkText` acceptable,** or should `List Char` in JS be a lazy string-backed list (the variant under A), at the cost of polymorphic list code?
3. **Is a compact form at the `List Char` level, rather than a `Value::Text`, sound and sufficient?** It makes matching `MkText` free and lets every list function walk compact text. Are there kernel rules (positivity, termination, erasure) that see list *values* and would need to know about it? I found none, but haven't checked every pass.
4. **`Rc<[char]>` or UTF-8** for the evaluator's compact form?
5. **Should `textAppend` ever be native in the kernel,** given that a flat copy is quadratic for right-nested appends, and a rope adds trusted code?
6. **The cache key:** is a hand-bumped "natives version" enough, or should the key include a hash of the native implementations' source?
7. **Should B1 compact `List Char` values as they're built** (for example when `textFromList` is applied to cons cells whose proofs are all `rfl`), or only literals and native results, as proposed?

## What I couldn't verify

- The **text literal limit in the playground** (WebAssembly, 128 KiB guard) wasn't measured; it's inferred from the measured limit for list literals.
- **V8's thresholds** for when `+` makes a `ConsString` and `slice` a `SlicedString`, rather than copying: V8's documentation says very short results are copied, but gives no current number.
- **How Rocq's VM and native compilers reduce `PrimString`** operations: the reference manual says the reduction machines have dedicated rules for primitives in general.
- **Lean's compiled string operations** are described from the reference manual ("overridden with an efficient implementation in runtime code"). I didn't read the runtime's C source.
- **The cost of polymorphic property access in V8** for the string-backed list variant.
- The **trusted code size** estimates for B1 and B2 are by analogy with `native.rs`, not from a prototype.

## Sources

- Lean: [Strings, in the reference manual](https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/); [4.25.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/) (`String` redefined as valid UTF-8 byte arrays); the kernel's [`type_checker.cpp`](https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp) (`string_lit_to_constructor`, `try_string_lit_expansion`, and native `Nat` operations only).
- Rocq: [primitive objects, in the reference manual (8.20)](https://docs.rocq-prover.org/v8.20/refman/language/core/primitive.html) ("These primitive declarations are regular axioms"); [`PrimStringAxioms` (9.0)](https://rocq-prover.org/doc/v9.0/corelib/Corelib.Strings.PrimStringAxioms.html); [kernel `Pstring` module](https://ocaml.org/p/rocq-runtime/9.1.0/src/rocq-runtime.kernel/pstring.ml.html) (`max_length_int = 16777211`); [releases](https://rocq-prover.org/releases) (primitive strings in 8.20.0); the `SFClassify` proof of `False`, fixed in 8.15.2 ([coq/coq#16096](https://github.com/coq/coq/issues/16096), [#16101](https://github.com/coq/coq/pull/16101)), as listed in the 8.15 changelog.
- Agda: [`Agda.Builtin.String`](https://www.cs.cmu.edu/~runmingl/afat/Agda.Builtin.String.html) (a rendered copy); [`Agda.Builtin.String.Properties`](https://github.com/agda/agda/blob/master/src/data/lib/prim/Agda/Builtin/String/Properties.agda) (`primStringToListInjective`, `primStringFromListInjective`).
- Idris 2: [`Data.String` source](https://idris-lang.org/Idris2/base/source/Data.String.html) (`strM` with `assert_total` and `believe_me`).
- F\*: [`FStar.String.fsti`](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.String.fsti) ("Some lemmas (admitted for now as we don't have a model)").
- Unison: [`Unison.Util.Rope`](https://github.com/unisonweb/unison/blob/trunk/lib/unison-util-rope/src/Unison/Util/Rope.hs) and `Unison.Util.Text` (`newtype Text = Text (R.Rope Chunk)`).
- Koka: [`kklib/include/kklib/string.h`](https://github.com/koka-lang/koka/blob/master/kklib/include/kklib/string.h) (valid UTF-8; small, normal and raw strings); [`std/core/sslice`](https://github.com/koka-lang/koka/blob/master/lib/std/core/sslice.kk).
- V8: [Strings in V8](https://chromium.googlesource.com/v8/v8.git/+/main/docs/objects/strings.md) (`ConsString`, `SlicedString`, flattening).
- This repository: [text-and-io.md](text-and-io.md) (the contract, and step 3's measurements), [native-numbers.md](native-numbers.md), [docs/core.md](../core.md) ("Numbers", "Tests and content hashes"), DESIGN.md §11 to §13, `bench/baseline.toml`.
