# How Stitchwort differs from Lean and Unison

Stitchwort is a dependently-typed language written in Rust. If you know Scala or
TypeScript, you may have met two languages it borrows from: **Lean 4** (a proof assistant
that is also a programming language) and **Unison** (code identified by hash, with
"abilities" for effects). This page says where Stitchwort does something different, and
what each language offers that the others don't.

Claims about Lean and Unison carry a source link. Claims
about Stitchwort cite a file in this repo. Facts about the web were checked on
19 October 2026 and move fast.

## 1. Termination is a guarantee about programs

**Lean.** Lean checks that every `def` terminates, because a looping function would make
its logic inconsistent. It then offers `partial def` as an escape. The reference says
"Functions marked `partial` are treated as opaque constants by the kernel and are neither
unfolded nor reduced", and that partial functions "may still be used in compiled code as
usual" ([Lean reference: recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/),
re-read 19 Oct 2026). Contrast `unsafe`: "any declaration that refers to an unsafe
definition must itself be marked unsafe" (same page). Nothing in the type of a
`partial def` says it may loop, so an ordinary function can call it:

```lean
partial def spin (n: Nat): Nat := spin n
def innocent (n: Nat): Nat := spin n + 1   -- accepted: nothing in the type says spin may loop
```

A Lean type like `Nat → Nat` therefore does not promise that the compiled program
finishes. The logic stays sound; the program can still hang
([DESIGN.md §5](../DESIGN.md#5-totality-and-partiality),
[partial.md §5.4](proposals/partial.md)).

Lean 4.17 added `partial_fixpoint`, for defining possibly non-terminating functions you
can reason about equationally (version and PR per [partial.md §5.4](proposals/partial.md);
the reference page itself states no version). It helps with proofs about partial
functions. It doesn't put partiality in the type.

**Stitchwort.** Non-termination is an ability-like marker in the type, `{Partial}`, and it
spreads to every caller:

```
def spin (n: Nat): {Partial} Nat := spin n

def innocent (n: Nat): Nat := spin n + 1             -- type error: calls spin, which uses Partial
def innocent (n: Nat): {Partial} Nat := spin n + 1   -- fine: the type says so
```

Only the runtime may discharge `Partial`, at `main`. There is no handler for it, no
override, and tests may not use it (rules 1-7 in
[DESIGN.md §5](../DESIGN.md#5-totality-and-partiality)). So a function type without
`{Partial}` does promise it returns. Stage 1 is built
([docs/proposals/partial.md](proposals/partial.md)).

The price: the termination checker is conservative and structural for now
([DESIGN.md §5, "Termination checking"](../DESIGN.md#5-totality-and-partiality)), so
some total functions need fuel or `{Partial}`.

## 2. Browser and TypeScript

**Lean 4 in a browser.** The official editor at live.lean-lang.org runs the Lean server
on a web server, not in your browser: "a web application running Lean 4 server-side"
([lean4web README](https://github.com/leanprover-community/lean4web)). WebAssembly builds
exist but are not the official path:

- An Emscripten build "which can run under Node.js" was announced in 2021, "currently
  slower than native"
  ([Zulip](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/lol.20another.20WASM.20question.html)).
  That archive has nothing newer than March 2022.
- Community builds work today, with caveats. One playground runs the Lean compiler
  "entirely in the browser via WebAssembly" from a fork of Lean
  ([cauli/lean4-wasm-in-browser](https://github.com/cauli/lean4-wasm-in-browser)).
  Another runs Lean 4.34.1 programs (merged 10 Oct 2026): single files importing only
  `Init`, about 143 MB first download, 7-15 s per run
  ([seo-rii/wasm-idle#48](https://github.com/seo-rii/wasm-idle/pull/48)).
  Neither is a Lean release.

**Lean 4 to JavaScript.** I found no official JavaScript or TypeScript backend. A 2022 Zulip answer said nobody had got Lean-to-JS/WASM working
([Zulip: Lean 4 as an application language](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Lean.204.20as.20an.20application.20language.html),
a 2022 snapshot). Third-party projects exist:
[Lean4-ts](https://github.com/lidangzzz/Lean4-ts) (a TypeScript implementation of a
subset of Lean) and [lean.js](https://github.com/leanprover/lean.js/blob/master/README.md)
(an old Emscripten port of the runtime). I found nothing that emits `.d.ts` files.

**Unison.** I found no official JavaScript or WebAssembly backend. In the Unison 1.0
discussion its creator said it "might support" compiling to the browser, pointing at a
community project ([Hacker News](https://news.ycombinator.com/item?id=46049722); a
paraphrase of the comment). A community runtime written in Rust and compiled to wasm
exists ([jaredly/unison.rs](https://github.com/jaredly/unison.rs)), and a 2019 issue
proposed a `Browser` ability and `compileToJavascript`
([unisonweb/unison#1783](https://github.com/unisonweb/unison/issues/1783)).

**Stitchwort.** The whole compiler (parser, checker, evaluator) runs in the browser as
WebAssembly: that is the playground in [web/](../web/) (built by `web/build.sh` from
`crates/web`; its cache is IndexedDB, per
[DESIGN.md §11](../DESIGN.md#cache-trust)). It also generates JavaScript with TypeScript
types:

```
$ stitchwort build --js src/pricing.sw -o dist/
  dist/pricing.js      (ES module)
  dist/pricing.d.ts    (TypeScript types)
```

```ts
export function applyDiscount(pct: bigint, price: Price): Price;   // pct <= 100 is checked at runtime
```

Each export decodes its inputs into a private copy, checks their shape and any decidable
preconditions (throwing `StitchwortInputError`), runs, and encodes the result
([DESIGN.md §12](../DESIGN.md#12-javascript-extraction), `crates/js`). The first milestone
allows only pure, concrete, assumption-free exports.

## 3. Proofs

**Lean** has a full prover: tactics (`simp`, `omega`, `grind`) and a community
library, Mathlib ([mathlib4](https://github.com/leanprover-community/mathlib4)). **Unison** has no proofs: its [README](https://github.com/unisonweb/unison)
describes a statically-typed functional language with an effect system and mentions no
proof facility.

**Stitchwort** states and proves theorems in the same language as programs, as terms,
with no tactics:

```
theorem appendLength: (xs ys: List a) -> length (xs ++ ys) = length xs + length ys
  | [],      ys => rfl
  | x :: xs, ys => Eq.cong Succ (appendLength xs ys)
```

Proofs are erased when running and extracting
([DESIGN.md §6](../DESIGN.md#6-proofs-universes-and-erasure)).
[docs/comparisons/aoc-day01.md](comparisons/aoc-day01.md) proves one Advent of Code
theorem in Stitchwort, Lean 4, Agda and Idris 2. Its findings:

- All four fully check. Lean was quickest to write, and its proof about half the size
  (5,000 characters against 11,500), almost all of the saving from `omega`, `simp` and `grind`.
- Those tactics couldn't reason about `/` and `%` with a variable divisor, so Lean's
  proof splits into the same cases and uses the same library lemmas.
- Lean and Agda check closed `Nat` arithmetic fast; Stitchwort's checker was slow on `% 100`.
- Stitchwort's biggest gaps: a `calc` for equality chains, more `/` and `%` lemmas, and
  native arithmetic in the checker.

## 4. Content hashing

**Unison's** core idea is code "identified by a hash of their implementation rather than
by name", kept "as its AST in a database" ([Unison README](https://github.com/unisonweb/unison)).
You write in `.u` scratch files and the `ucm` tool adds them to the codebase ("`update`
adds everything in the most recently typechecked file to the namespace";
[Unison docs](https://www.unison-lang.org/docs/)). Names are labels on hashes.

**Stitchwort** also hashes each definition by content (type, body and its dependencies'
hashes, but no names; [DESIGN.md §11](../DESIGN.md#11-content-hashing-and-caching)), with
Unison-style cycle hashing for mutually recursive groups. But the hash is a cache key, not
the identity of your code. Your code is ordinary text files in git. Test and proof results
are cached by hash, so unchanged ones aren't re-run:

```
$ stitchwort test
  ✓ reverse twice          cached
  ✓ tick twice             ran (3ms)     ← tick's hash changed
```

Consequences: renaming is free for the cache, but there is no code database and no
sharing by hash. Nominal types include their module and name in the hash, because there
is no stored unique ID. Only the POC cache layers are built, and elaboration always
re-runs.

## 5. Abilities and effects

**Unison** has abilities, its algebraic effects: "an ability is a pairing of some kind of
effect with a handler which responds to that effect"
([Unison docs: abilities](https://www.unison-lang.org/docs/fundamentals/abilities/)). That
page doesn't say whether abilities track non-termination, and the
[partial.md survey](proposals/partial.md) read the docs the same way ("absence of
evidence, not a positive statement").

**Stitchwort** follows Unison's design: direct style, no `do`
([DESIGN.md §8](../DESIGN.md#8-abilities-and-handlers)).

```
ability State s where
  get: () -> {State s} s
  put: s -> {State s} ()

def tick(): {State Nat} Nat :=
  let n := get()
  put (n + 1)
  n
```

A plain arrow `a -> b` means pure and total, and `def main(): {IO} () := …` performs
real I/O only at the runtime's entry. Handlers are deep: a handler is a fold over the
operations a computation performs. Where Stitchwort departs from Unison: effects are
represented as data the kernel understands
([docs/proposals/abilities.md](proposals/abilities.md)), handlers are trusted to
terminate only under rules the checker enforces, and `Partial` is a marker no handler
can remove. The checker never runs effectful code
([DESIGN.md §6](../DESIGN.md#effects-and-dependent-types)).

## 6. What Lean and Unison offer that Stitchwort doesn't yet

- **Ecosystem.** Lean has Mathlib and a large community. Unison has a code
  host (Unison Share; [docs](https://www.unison-lang.org/docs/)) and a 1.0 release
  ([HN thread](https://news.ycombinator.com/item?id=46049722)). Stitchwort has a small
  prelude and the Advent of Code files in [aoc/](../aoc/).
- **Tactics and automation.** Lean's `simp`, `omega` and `grind` halved the AoC proof
  ([aoc-day01.md](comparisons/aoc-day01.md)). Stitchwort has `auto` for decidable facts only.
- **Tooling.** Unison has `ucm` and a local web UI ([README](https://github.com/unisonweb/unison)).
  Stitchwort has a CLI, the playground, and a VS Code syntax-highlighting extension in [editors/](../editors/).
- **Distributed computing.** Unison can be used "in conjunction with" Unison Cloud "for
  building distributed systems" ([README](https://github.com/unisonweb/unison)).
  Stitchwort has nothing like it.

## Summary

| | Lean 4 | Unison | Stitchwort |
|---|---|---|---|
| Non-termination in types | No: `partial def` is invisible | Not mentioned in the abilities docs | `{Partial}`, propagates, no escape hatch |
| Proofs | Tactics and Mathlib | None | Terms in the same language, no tactics |
| Code identity | Names and files | Hash, in a codebase database | Names in text files; hash only for caching |
| Effects | Not covered here | Abilities and handlers | Abilities and handlers, effects as data |
| In a browser | Official editor is server-side; WASM only via community forks | Community experiments only | Whole compiler in WASM (playground) |
| Export to JS/TS | None official found | None official found | `build --js` with `.d.ts` and checked codecs |

In one paragraph: Stitchwort takes Lean's idea that proofs are programs, plus Unison's
abilities and hashing, and makes a function's type an honest promise that it returns,
can be proved about, and can be called from TypeScript, while running anywhere a browser
does.
