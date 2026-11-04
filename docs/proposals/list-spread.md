# Building lists with `[x, ..xs]` (SW-1214)

**Status:** design note, 4 November 2026. Not built. Matt chose the
direction (D2309: a `..` spread in list expressions, the same as list
patterns' rest, rather than an infix cons). The decisions are D2320 to
D2324 (§8).

In short: `[a, b, ..xs]` in an expression means `Cons a (Cons b xs)`, the
same as the pattern `[a, b, ..xs]` already matches. `..` comes last and
only once, as in patterns. Goals print a `Cons` chain that ends in
something other than `[]` the same way. There is no `::` or `:`. Nothing
changes in the kernel: the spread is another way to write `Cons`.

## 1. The problem

A list pattern can take a list apart with a rest, `[x, y, ..rest]`
(docs/syntax.md, "List patterns"; `examples/accept/list-rest-patterns.sw`),
but an expression can't put one back together that way. syntax.md says so:
"list expressions have no `..` spread (use `++` or `Cons`)". So building a
list from a few elements in front of another list is written with nested
`Cons`, and every level adds a bracket:

```
-- aoc/src/Aoc/Year2024/Day24/Day24.sw:230
Faulty fixes (Cons carry (Cons (Z bit) (bitOutputs gates bit carry)))

-- aoc/src/Aoc/Year2024/Day02/Day02.sw:49, after matching `Cons level (Cons next rest)`
else (Cons level rest).chain ok || (Cons next rest).chain ok

-- aoc/src/Aoc/Year2021/Day01/Proofs/Proofs.sw:14
increases (Cons a (Cons b rest)) = Bool.toNat (a < b) + increases (Cons b rest)

-- aoc/src/Aoc/Year2021/Day16/Proofs/Sound.sw:175
let here: Cons v1 (Cons v2 (Cons v3 (Cons t1 (Cons t2 (Cons t3 (Cons False fields)))))) = encode packet ++ following :=
```

With the spread these are:

```
Faulty fixes [carry, Z bit, ..bitOutputs gates bit carry]
else [level, ..rest].chain ok || [next, ..rest].chain ok
increases [a, b, ..rest] = Bool.toNat (a < b) + increases [b, ..rest]
let here: [v1, v2, v3, t1, t2, t3, False, ..fields] = encode packet ++ following :=
```

The last is the clearest case: the same proof writes `[t1, t2, t3]` two lines
earlier, because the list ends there, and has to switch to seven nested
`Cons` when it doesn't. A pattern in the same file could already be written
`[v1, v2, v3, t1, t2, t3, ..rest6]`; the expression that rebuilds it can't.

The other workaround, `[x] ++ xs`, isn't used anywhere: it's longer, and in a
proof it is an `append` that has to compute before it is a `Cons`.

**How often.** By grep over `aoc/src`, `games`, `crates/elab/src/std` and
`examples/accept` (lines not in arm heads, so patterns are left out;
approximate):

| | lines |
|---|---|
| `Cons` used in an expression | 1,177 lines, 1,602 uses |
| of which in `aoc` proofs and specs | 417 lines (`aoc` programs: 32) |
| of which in the library | 599 lines, mostly theorem statements |
| `Cons x` given one argument, as a function (`xs.map (Cons h)`) | 122 uses: these stay |
| two or more nested `Cons` on one line | 58 lines |
| `xs ++ [y]`, adding at the end | 88 lines, almost all proofs |
| `[x] ++ xs` | 0 |

So it is mostly a proof-writing problem: statements about `f (Cons x xs)`,
which is how a lemma about one step of a recursion is stated. Programs build
lists with `Cons` less often (32 lines in `aoc`), and most of those are one
`Cons` (`Cons secret (secrets count next)`), where the spread saves little.
The gain is largest for chains of two or more, and in making expressions and
patterns read alike.

## 2. The proposal

**`[e₁, …, eₙ, ..tail]` in an expression is `Cons e₁ (… (Cons eₙ tail))`**,
with `List`'s own `Cons` (by identity, as list patterns and literals use
it: a user's own `Cons` doesn't change it).

- `tail` is any expression, up to the `]`: `[x, ..f y z]` is
  `Cons x (f y z)`, and `[x, ..ys ++ zs]` is `Cons x (ys ++ zs)`.
- `..` is last and appears once, as in patterns.
- `[..xs]` is `xs`, as the pattern `[..p]` is `p`. It is allowed, for the
  symmetry, with no warning; nobody needs to write it, and the formatter
  leaves it alone.
- The elements and the tail are evaluated left to right, the tail last, as
  the arguments of `Cons e₁ (…)` are.
- The type is `List a` where every element is an `a` and the tail is a
  `List a`.

**Only last, for good (D2321).** `[..xs, y]` and `[..xs, ..ys]` could mean
`xs ++ [y]` and `xs ++ ys`, as in JavaScript and Python. The proposal is not
to allow them, now or later:

- **The cost is hidden.** `[x, ..xs]` is one constructor, whatever `xs` is.
  `[..xs, y]` would copy all of `xs`. The two look equally cheap; `++` at
  least says that work is done. Gleam refuses `[..xs, y]` for this reason,
  with an error that explains it.
- **It doesn't compute in proofs.** `[x, ..xs]` is a constructor, so
  `f [x, ..xs]` steps by `f`'s `Cons` equation and `rfl` sees through it.
  `[..xs, y]` with an unknown `xs` is a stuck `append`. A form that looks the
  same as the constructor but behaves differently in a goal is a trap.
- **It has no pattern.** `[..init, last]` can't be a pattern, since it isn't
  a constructor form, so the symmetry that motivates the spread would break
  at the first step.
- **The snoc lemmas are written against `++` anyway.** The 88 `xs ++ [y]`
  lines are almost all proofs (`scoreSnoc: score (moves ++ [way]) = …`),
  where the library's lemmas about `append` are what applies. Writing
  `[..moves, way]` would mean either printing `append` in that form (which
  hides the stuck call) or two spellings of one term in the same goal.

The error for a spread anywhere but last says what to write instead (§4.6).

**Printing (D2322).** Goals, hovers and messages print a closed `Cons`
chain as `[1, 2, 3]` already (`list_literal` in `crates/core/src/pretty.rs`),
and an open one as `Cons a (Cons b xs)`. The proposal is to print an open
chain as `[a, b, ..xs]`, including a single `Cons x xs` as `[x, ..xs]`:

- A goal then reads as the source the user would write, and the nested form
  is where goals get hard to read (the Day 16 proof's goals are seven
  `Cons` deep).
- Printing `[x, ..xs]` also names `List`'s `Cons` unambiguously, where
  `Cons x xs` could be read as a user's own `Cons`.
- `Cons x` with one argument, and `Cons` alone, still print as they are.
- The cost: a proof whose arms match `| Cons x xs =>` sees goals about
  `[x, ..xs]`. Both spellings mean the same term, so copying either back
  into the source works. About 32 snapshot files show an open `Cons` chain
  today and would change.

The alternative is to keep printing `Cons` and let the spread be input only;
that's the smaller change, but leaves goals in the form the spread was meant
to replace.

**What isn't changing.** Patterns (they already have the rest). Existing
code: nothing is rewritten (D2324). `Cons` stays an ordinary constructor,
usable as a function.

## 3. The alternatives

**An infix cons: `x :: xs` (OCaml, F#, Scala, Elm, Lean, Idris) or
`x : xs` (Haskell), for building and matching.** Not proposed:

- **`:` is taken.** `(x: Nat)`, `(e: T)` and `let x: T :=` use `:` for type
  annotations, and `(x : xs)` would be ambiguous with an annotation. Haskell
  can use `:` only because its annotations are `::`. That leaves `::`.
- **`::` gives two spellings of one pattern.** List patterns already have
  `[x, ..rest]`; adding `x :: rest` means two forms in patterns, and style
  arguments about which to use, or a breaking change to remove the one that
  exists. The spread extends what's there instead.
- **A new operator with a precedence to learn.** `x :: f y ++ zs` needs a
  rule (right associative, below application, relative to `++`, `|>`, `==`).
  The spread needs none: everything after `..` up to `]` is the tail.
- **It doesn't chain any better.** `a :: b :: xs` is no shorter than
  `[a, b, ..xs]`, and needs the reader to know `::` is right associative.
- What `::` is better at: a one-element prepend in a pipeline or a section,
  `xs |> (x ::)`. Stitchwort writes that `Cons x`, which already works.

**Leave it as it is** (`Cons`, `++`). Costs nothing, but expressions and
patterns stay different, and long chains stay hard to read, in goals too.

**Prior art.**

- **Gleam:** `[x, ..xs]` both to build and to match, `..` only last;
  `[..xs, y]` is refused with an error explaining that appending copies the
  list. This proposal is Gleam's design.
- **Erlang, Prolog:** `[H | T]`, also one form for both, also only at the
  end. (`|` is or-patterns and arms in Stitchwort, so not that spelling.)
- **JavaScript** `[x, ...xs]` and **Python** `[x, *xs]` (PEP 448) build
  arrays, with spreads anywhere and any number of them; those are arrays,
  where each spread is a copy in any position. Python's patterns
  `[x, *rest]` (PEP 634) allow one star at any position, matching by length.
- **Rust** has slice patterns, `[first, .., last]` and `[x, rest @ ..]`,
  with the rest anywhere since slices have a known length; no spread in
  array expressions. Its `..base` in struct updates is the other use of the
  same token.
- **Elm, Haskell, OCaml, F#, Scala, Lean, Idris, Agda:** an infix cons
  (`::`, `:`, `∷`) for both. Lean and Idris have `[a, b]` literals with no
  rest form.

## 4. Interactions

### 4.1 The parser and the syntax tree

`list_expr` (`crates/syntax/src/parser.rs`) learns the `..` item the
pattern parser already has: after `..`, one expression, then `]`.
`Expr::List(Vec<Expr>, Span)` becomes `Expr::List(Vec<Expr>, Option<Box<Expr>>, Span)`.
Changing the arity is deliberate: each of the 29 places that match
`Expr::List` (walkers in `nav.rs`, `no_effect.rs`, `autobind.rs`,
`numbers.rs`, `queue.rs`, `effects.rs`, `module.rs`, `lib.rs`, …) stops
compiling until it handles the tail, so no walker silently skips it.
Desugaring to `Cons` applications in the parser, as list patterns do, would
be smaller but worse: errors and hovers would talk about a `Cons` the user
didn't write, and the formatter would have to tell the two apart.

`..` is already a token (`Tok::DotDot`, used by list and record patterns and
`import X (..)`), and expressions don't use it, so nothing else changes
meaning. Lists that aren't expressions, the fact lists of `simp [h₁, h₂]`
and `omega [..]` (parsed through `list_expr`), refuse a spread with an
`E-PARSE` that says it's a list of facts.

### 4.2 The elaborator's list-literal path

`check` on `Expr::List` against `List a` (`crates/elab/src/check.rs`, the
arm that builds the `Cons` chain) checks the items against `a` as now, then
the tail against `List a`, and starts the chain from the tail's term instead
of `Nil`. Long literals are cut into chunks joined by `append` (SW-62); the
tail goes at the end of the last chunk, so the term is the same as the
hand-written `Cons` chain whenever it is short enough to be one.

Against a type that isn't `List`, the literal falls back to inferring as
now (`fallback_named`), and `infer` makes a fresh element type as now.

### 4.3 Type inference

The element type comes from the expected type if there is one, else from
the items and the tail. A number literal item waits while the element type
is unknown (postponement.md, K4), so the tail can say it:
`let ys := [1, ..xs]` with `xs: List Int` makes `1` an `Int`. Dot notation
on a literal (`[x, ..xs].chain ok`) already looks in `List` whatever the
items (`dot.rs`), and the spread doesn't change that.

### 4.4 Abilities

`effects.rs` sequences effectful list items left to right. The tail is one
more part, run last: in a `{IO}` function, `[header, ..readRest()]`
runs `readRest()` after `header` is computed.

### 4.5 Hashing and the kernel

None. The elaborated term is the `Cons` chain that writing `Cons` gives,
so kernel terms, their hashes, the proof-check cache and generated code are
the same for both spellings. Changing `Cons a b` to `[a, ..b]` in a file is
an edit to its text like any other. The kernel and the trusted base don't
change.

### 4.6 Error messages

- `[..xs, y]`, `[x, ..xs, y]` or `[..xs, ..ys]`: `E-PARSE` at the item
  after the spread: "a `..` tail must be the last item" (the pattern
  parser's words), with a note: "`[x, ..xs]` puts `x` in front of `xs`; to
  add at the end, write `xs ++ [y]` (it copies `xs`)", and for two spreads,
  "to join two lists, write `xs ++ ys`".
- `[x, ..]` with nothing after `..`: "a list after `..`". (In a pattern,
  `.._` is the way to ignore the rest; an expression has no such form.)
- A tail that isn't a list, `[x, ..y]` with `y: Nat` (probably meaning
  `[x, y]`): `E-TYPE-MISMATCH` at `y`, with a note: "after `..` comes the
  rest of the list, a `List Nat`; to add `y` as one more element, write
  `[x, y]`".
- An element that is a list where the tail was meant, `[x, xs]`, is already
  a mismatch at `xs`; the note can suggest `..xs` when `xs` has the list's
  type, the mirror of the one above.
- `x :: xs` and `x : xs` today give the parser's general errors. Since
  people from other languages will try them, a note on `::` saying "write
  `[x, ..xs]`" is worth adding (patterns and expressions both).

### 4.7 The formatter

`stitchwort fmt` works on tokens and checks that its output parses to the
same tree (formatter.md §4), so the new tree shape needs nothing beyond the
parser. Spacing: `..` touches what follows it (`spacing.rs`, "`..base`: the
spread touches its name", already in place for patterns); a multi-line list
breaks after commas as now, with `..tail` as its last line and no trailing
comma after it (D1012 already drops trailing commas). One golden test.

The formatter doesn't rewrite `Cons a b` into the spread: it never changes
the tree.

### 4.8 Goal and term printing

`crates/core/src/pretty.rs`: `list_literal` returns the items and, where
the chain ends in something other than `Nil`, the tail; the printer shows
`[a, b, ..t]` (D2322). The tail is printed at the lowest precedence, since
the `]` closes it. The closed form and the special form for a list of characters
(`char_list`) are unchanged. The LSP's hovers and goal view and the
elaborator's messages go through the same printer.

### 4.9 Text and other literals

None of the other literals is a list. `Text` is its own type with
`"${…}"` to build it (compact-text.md), so there is no text spread; a
`List Char` literal (`['a', ..cs]`) is a list like any other. `Vec`, `Map`
and `Set` have no bracket literal (`VCons 4 (VCons 5 VNil)`,
`Map.fromList [...]`); a `Vec` literal with the same spread would be a
separate proposal.

## 5. Implementation

One lane, Sonnet, about 2 hours:

1. Parser and tree: `..` in `list_expr`, the `Expr::List` arity, every match
   site; the `simp`/`omega` fact lists refuse it. Parser unit tests.
2. Elaborator: the tail in `check`'s list arm, `effects.rs`'s sequencing,
   the walkers. The error notes of §4.6.
3. Printer (if D2322 is yes): `list_literal` with a tail; the snapshot
   changes (about 32 files), reviewed as a batch.
4. Formatter: a golden test for the spacing and line breaks.
5. Docs and examples: syntax.md's "List patterns" paragraph (the sentence
   saying there's no spread goes), a line in docs/guide chapter 4 and 10;
   `examples/accept/list-spread.sw` (building, `rfl` through it, effects,
   the inferred element type), `examples/reject/list-spread-not-last.sw`,
   `examples/reject/list-spread-tail-not-list.sw`.

**Risk: low.** It is syntax that elaborates to terms that already exist; the
kernel doesn't change. The likely bug is a walker that ignores the tail
(name resolution, go-to-definition, the effect check), which the arity
change makes the compiler point at. Printing is the one visible change to
existing output.

## 6. What isn't proposed

- A spread anywhere but last, or more than one (D2321).
- An infix cons, `::` or `:` (D2323).
- Rewriting existing code (D2324).
- A spread for `Vec`, or in tuples and records (records have
  `{ base | field = e }`).

## 7. Open points decided here

These are details, decided in this note rather than asked:

- `[..xs]` is allowed and means `xs`, without a warning (as `[..p]` in
  patterns).
- No trailing comma after the tail, as patterns.
- The tail is the whole expression up to `]`, so it never needs brackets.

## 8. Decisions

| ID | Question | Recommendation |
|---|---|---|
| D2320 | **The spread.** Building a list from a few elements in front of another list needs nested `Cons` (`Cons a (Cons b xs)`), unlike patterns, which have `[a, b, ..xs]`. Allow `[a, b, ..xs]` in expressions too, meaning that `Cons` chain, with `..` last and once and any expression after it? | [Yes] |
| D2321 | **Only at the end.** `[..xs, y]` and `[..xs, ..ys]` could mean `xs ++ [y]` and `xs ++ ys`, as in JavaScript and Python. Refuse them, now and later, with an error that suggests `++`, because appending copies the list, doesn't compute in proofs the way `Cons` does, and has no matching pattern? | [Yes, last only, as Gleam] |
| D2322 | **Printing.** Goals and messages print an open list as `Cons a (Cons b xs)`. Print it as `[a, b, ..xs]` instead (a single `Cons x xs` as `[x, ..xs]`), so goals read as source would be written? About 32 snapshot files change. | [Yes] |
| D2323 | **No infix cons.** Not add `x :: xs` (or `x : xs`, which clashes with type annotations) for building or matching, so each list shape has one spelling? A note on `::` errors points to `[x, ..xs]`. | [Yes, none] |
| D2324 | **Existing code.** Leave the 1,177 lines that build lists with `Cons` as they are (no sweep, no formatter rewrite), use the spread in new code and in the docs, and rewrite old code only when it's being edited anyway? | [Yes; a later lint for long chains if they keep appearing] |
