# Chained comparisons, `low <= x <= high` (SW-1339)

**Status:** design note, 5 November 2026, for Matt's decisions (§11). No
implementation yet. Background: Matt (D2385), after Python: `entry.low <=
times <= entry.high` should mean `entry.low <= times ∧ times <= entry.high`.

Claims about Stitchwort are **[checked]** when I read or ran the thing named
(on `main` at `2d532706f`), **[estimate]** when they are my reading of what
will happen. Claims about other languages are from memory, **unverified**,
unless marked otherwise.

## 1. In short

- **The problem.** "Is `x` between `low` and `high`?" is written `low <= x ∧
  x <= high` today: `x` twice, and the reader has to check that the two
  `x`s are the same and that the bounds face the right way. The code base
  has 66 such lines outside the examples (§9).
- **The change.** `a <= b <= c` means `a <= b ∧ b <= c`, as in Python and
  in mathematics. It chains `<` and `<=` together, or `>` and `>=`
  together, any number of times: `0 <= i < n`, `hi >= x > lo`. Nothing else
  chains: not `=`, `==`, `!=`, `in`, and not a mix of directions
  (`a < b > c`); those get an error that says what to write.
- **What it does.** A chain is exactly the conjunction written out: the
  same term, the same hash, the same goals, and the same facts for `if`,
  guards, `auto` and `omega`. In a `Bool` it is the `&&` form, so the right
  comparison is tested only if the left one holds. Where the middle performs
  operations (`0 < nat() <= 9` in a parser) it runs once.
- **Nothing breaks.** Every chain is a parse error today (§2), so no
  program changes meaning.
- **Size.** About 3 hours on Sonnet for the language part, then an optional
  sweep of the sites (§10).

## 2. What happens today

Comparisons are parsed by `cmp_expr` (crates/syntax/src/parser.rs:3772-3809)
**[checked]**: one left operand, at most one of `=`, `!=`, `==`, `<`, `<=`,
`>`, `>=`, one right operand, and then it returns. Its comment says "not
associative". `>` and `>=` are stored flipped, as `<` and `<=` with the
operands swapped (parser.rs:3790-3792), so goals show `<` and `<=`.
`in`/`!in` are a separate path (`membership`, parser.rs:3813), also not
associative. The Unicode spellings `≤`, `≥`, `≠`, `∈` and `∧` are the same
tokens as `<=`, `>=`, `!=`, `in` and `&&` (crates/syntax/src/lexer.rs:1035-1064)
**[checked]**, so everything here applies to both spellings.

So a second comparison operator is left over, and the declaration ends
there. Run on today's binary **[checked]**:

```
def t (a b c: Nat): Bool := a <= b <= c
-- E-PARSE: expected the end of the declaration, but found `<=`
def t (a b c: Nat): Bool := a == b == c        -- the same, at the second `==`
def t (a b: Nat) (c: Bool): Bool := a <= b == c -- the same, at `==`
def t (a b c: Nat): Bool := (a <= b) <= c
-- E-TYPE-MISMATCH: `<=` works on `Nat` and `Int` … this is `Prop`
```

The parser's own tests pin this down: `a > b > c` is asserted to be an
error (parser.rs:6579-6580), and so is `a in b in c` (parser.rs:7850-7851)
**[checked]**. No `.sw` file in aoc/, games/, the standard library or
examples/ can contain a chain, since none would parse; the first test would
be updated, the second kept.

The one place chains already exist is `calc`: its steps `_ <= b`, `_ < c`
chain, `=` goes with either direction, and mixing `<`/`<=` with `>`/`>=` is
`E-CALC-RELATION`, "a `calc` chain goes one way" (parser.rs:3104-3128)
**[checked]**. `!=` and `==` steps are refused there with "other relations
can't be chained" (parser.rs:3079-3086). This note's rule for which chains
are allowed is the same one, minus `=` (§5).

## 3. What a chain means

### 3.1 In a proposition and in a `Bool`

`a <= b` is always elaborated as a proposition, decided where a `Bool` is
wanted; `&&` is `And` where a proposition is expected and the short-circuit
`Bool` `if a then b else False` otherwise (crates/elab/src/numbers.rs:1238,
docs/syntax.md operator table, `a && b` and `if c then a else b` rows)
**[checked]**. So a chain needs no separate Prop and Bool readings: it is
`a <= b && b <= c` (`∧` and `&&` are one token), and that already means:

- in a statement or a type: `a ≤ b ∧ b ≤ c`, an `And` (constructor `Both`);
- where a `Bool` is expected: `a <= b && b <= c`, with `b <= c` tested only
  if `a <= b` holds;
- in an `if` or a guard: the decided proposition, so the branch knows
  `a ≤ b ∧ b ≤ c`.

A longer chain is right-nested like `&&`: `a < b < c < d` is `a < b ∧ (b < c
∧ c < d)`.

### 3.2 Inside a longer conjunction

`lo <= x <= hi ∧ p` could be either:

- (a) **the chain as one conjunct**: `(lo ≤ x ∧ x ≤ hi) ∧ p`, as if
  bracketed; or
- (b) **spliced in**: `lo ≤ x ∧ (x ≤ hi ∧ p)`, the tree today's hand-written
  `lo ≤ x ∧ x ≤ hi ∧ p` gives (`logic_chain`, parser.rs:3673-3705, groups
  `&&` to the right **[checked]**).

(a) is what the text says: the chain is one fact, "x is in range", and
`h.left` is that fact, `h.left.left` its lower bound. (b) keeps the exact
term of the hand-written line, so a site can be rewritten with no proof
changed; under (a), a site such as games/rogue/src/Rogue/Level.sw:21 (four
comparisons in one `∧` chain) changes shape, and proofs that take its
hypothesis apart with `.right.left` would change with it. Since migration
cost doesn't count, I recommend (a) (§11, C3). `omega` and `auto` don't care
either way: they take conjunctions apart however they nest (below).

### 3.3 What proofs, `auto`, guards and `omega` see

Because the chain is the conjunction, everything that handles `∧` today
handles it, with no new code **[checked]** for each of these, by reading:

- **`if`.** `if lo <= x <= hi then … else …`: the `then` branch knows
  `lo ≤ x ∧ x ≤ hi`, and `auto` uses each part
  (examples/accept/auto-conjunction.sw, lines 1-3: "The branch of an `if p
  && q` knows `p ∧ q`, and `auto` uses each part").
- **`if h:`.** `if h: lo <= x <= hi` names it: `h.left: lo ≤ x`, `h.right: x
  ≤ hi`.
- **Pattern guards.** `| n if 3 <= n <= 9 => n` is the guard `3 <= n && n <=
  9`. Its generated equation takes `(3 <= n && n <= 9) = True` today
  (examples/accept/pattern-guard-equations.sw, `between`); SW-1318 is
  changing conjunction guards to state `P ∧ Q`, and a chain gets whatever
  that lands as.
- **`omega`.** Takes `And` facts apart (crates/elab/src/omega.rs:31,
  `And.left`/`right`), so a chained hypothesis is two linear facts.
- **Tests.** `test "range" := 0 <= f 3 <= 9`: a failing `&&` test shows the
  first false operand with its two sides (docs/syntax.md, "If the test is a
  comparison … or an operand of `&&`"); the chain shows `f 3 <= 9` as such.
  The test explainer (crates/elab/src/probe.rs:35) needs the chain to look
  like `&&` to it, which it does under §6's representation.
- **Equations and `rewrite`.** The term is the conjunction, so lemmas stated
  either way (`Nat.betweenYes`, std/Nat/Arith.sw:311) match it.

## 4. The middle is evaluated once

### 4.1 Pure code

In pure code "once" can't be observed, except as time. Two ways to build
the term:

- (a) **Use the middle's term twice**: `And (Le a m) (Le m c)`. This is
  exactly the hand-written conjunction, so terms, hashes, goals and
  equations match it. At run time `m` is computed twice when both sides are
  tested, as it is in the hand-written form.
- (b) **Bind it**: `let %m := m; a <= %m ∧ %m <= c`, a transparent `Let`
  (docs/core.md, `Let(x, A, v, b)`). Computed once. The kernel ζ-reduces it
  while checking, and quoting never produces a `Let` (docs/core.md §"let")
  **[checked]**, so goals would still read `a ≤ m ∧ m ≤ c` **[estimate]**;
  but the stored term and its hash differ from the hand-written one, and a
  spec stated with a chain and a proof stated with `∧` would differ by a `Let`
  until something evaluates it.

Almost every site in §9 has a variable or a field as its middle (`times`,
`probe.x`, `code`, `byte`), where (a) and (b) cost the same. I recommend
(a): one rule, "a chain is the conjunction", with the docs saying to `let`
an expensive middle, as one would for the hand-written form (C4). A variant
of (b) only for a middle that isn't a name, field or literal is possible,
but then the term depends on the middle's form.

### 4.2 Effectful code

Here duplication would be wrong: `0 < nat() <= 9` must read one number. A
condition that performs must be a `Bool` (docs/syntax.md, `if` row), and the
effects pass already lowers a performing `a && b` by running `a` first and
binding it (crates/elab/src/effects.rs:2811-2850, `%left`) **[checked]**.
For a chain whose operands may perform, the pass binds each performing
operand once, left to right, and keeps the short circuit:

```
a <= b <= c      -- b performs, maybe a too
==>
let %a := a      -- only if a performs
let %m := b
%a <= %m && %m <= c      -- c runs only if the first test holds
```

and recursively for `a < b < c < d`. This is a rewrite of the chain before
the existing `&&` lowering, not a new lowering **[estimate]**. In the empty
row the result computes to what the pure chain does, as the `&&` lowering's
comment promises for `&&`. The alternative is to refuse a performing operand
in a chain (`E-ABILITY`, "bind it with `let` first") and add this later; the
rewrite is small enough that I recommend doing it in stage 1 (C5).

## 5. Which relations chain

### 5.1 Other languages

- **Python** chains every comparison: `<`, `<=`, `>`, `>=`, `==`, `!=`,
  `in`, `not in`, `is`, `is not`, mixed freely. Each middle is evaluated
  once, and the chain stops at the first false link. The freedom is the
  source of its known surprises: `a < b > c` is legal (and says nothing
  about `a` and `c`); `a != b != c` doesn't mean "all different"; `False ==
  False in [False]` is `True`, being `False == False and False in [False]`;
  `x == y in z` is rarely what was meant.
- **Julia** chains comparisons too, mixed (`1 < x <= 3`, `a == b < c`), and
  its manual says the order in which a chain's operands are evaluated is
  undefined, so side effects in them shouldn't be relied on.
- **Lean 4 / Mathlib**: no chain notation that I know of; `≤` is a
  non-associative infix, so `a ≤ b ≤ c` doesn't parse. Mathlib writes `a ≤ b
  ∧ b ≤ c`, or `x ∈ Set.Icc a b` (and `Ico`, `Ioc`, `Ioo`) for intervals,
  and uses `calc` for chains of reasoning.
- **Rust** refuses, with a targeted error: "comparison operators cannot be
  chained", and a suggestion to split it into `a < b && b < c`.
- **Swift** refuses: comparison operators are in a non-associative
  precedence group ("adjacent operators are in non-associative precedence
  group 'ComparisonPrecedence'").
- **Haskell** refuses: `<` is `infix 4`, so `a < b < c` is a precedence
  parsing error ("cannot mix … in the same infix expression").
- **Idris 2** likewise: comparisons are declared `infix`, non-associative.
- **Agda**: mixfix operators let a library define `_≤_≤_` as one
  three-place relation; nothing is built in.

So the languages split into "chain everything" (Python, Julia) and "chain
nothing, with an error" (Rust, Swift, Haskell, Lean). None of the second
group has a problem with ordering chains as such; what they avoid is the
mixed ones.

### 5.2 Recommendation

Chain what reads as one statement about an order, and nothing that
surprises:

| Chain | Allowed? | Why |
| --- | --- | --- |
| `<` and `<=`, any mix: `0 <= i < n` | yes | the main case; "in this range" |
| `>` and `>=`, any mix: `hi >= x > lo` | yes | the same, read downwards; `calc` allows it too |
| `<`/`<=` with `>`/`>=`: `a < b > c` | no | says nothing about `a` and `c`; `E-CALC-RELATION`'s rule |
| `=` with orders: `a <= b = c` | no, for now (C2) | rare; `calc` is the tool for mixed reasoning |
| `=`, `==` alone: `a == b == c` | no, for now (C2) | in C-family code this means `(a == b) == c`; worth an error that says so |
| `!=`, `≠`: `a != b != c` | no | doesn't mean "all different" |
| `in`, `!in`, `∈`: `x ∈ xs ∈ ys`, `a <= x ∈ xs` | no | not a relation between neighbours of one type |

A descending chain is stored as an ascending one, as a single `>` is: `hi >=
x > lo` is `x <= hi ∧ lo < x` (each link flipped, the links in the order
written) **[estimate]** of what reads best in goals; the alternative is to
reverse the whole chain to `lo < x <= hi`, as `calc` does (`reverse_calc`,
parser.rs:4695), which changes the order of the conjuncts from the written
one. I recommend flipping each link and keeping the written order, so
`h.left` is the first comparison written (C1).

Allowing `=` in chains later is backward compatible: the refused forms stay
parse errors until then.

## 6. How it is built

### 6.1 Parsing

`cmp_expr` loops while the next token is `<`, `<=`, `>` or `>=`, collecting
operands and relations, then checks the direction rule. Operands are parsed
as today (each may be a pipeline; only the last may be an `if`, as the right
operand of a single comparison may today, parser.rs:3795-3801).

The tree: the parser builds the conjunction itself, with the middle's
syntax copied (same spans), and a new `BinOp::Chain` in place of
`BinOp::And` joining the links:

```
a <= b < c   ==>   Binary(Chain, Binary(Le, a, b), Binary(Lt, b', c))
```

Every walk that treats `Binary(_, x, y)` generically (free variables,
captures, spans, the LSP's position lookups) needs nothing new; 23 source
files match on `Expr::Binary` **[checked]**, and only the ones that match
`BinOp::And` by name need `Chain` added: `logic.rs` (the `Logic::And` view,
crates/elab/src/logic.rs:57 and 201), `probe.rs` (35, 136), `effects.rs`
(2816, 3110), and `op_text` (numbers.rs:687) **[checked]** that these are the
sites; whether there are others outside elab is **[estimate]**. The effects
pass uses `Chain` to know that `b'` is `b` (§4.2). An `Expr::Chain` node of
its own would be cleaner to read, but every walk would need a case for it.

The copy means the middle is elaborated twice. A type error in it stops the
declaration at the first copy **[estimate]**, so it is reported once; if the
elaborator turns out to keep going, the second report needs suppressing by
span. One oddity: a literal middle is typed per link, so `n <= 5 <= i` with
`n: Nat` and `i: Int` checks, with `5: Nat` on the left and `5: Int` on the
right. Harmless, and not worth a single numeric group across the chain.

### 6.2 Precedence

A chain sits where a comparison does: tighter than `&&`, `||`, `<->` and
`->`, looser than `|>`, `++` and arithmetic. So `0 <= x + 1 <= n && ok` is
`(0 <= x + 1 <= n) && ok`, and under C3 (a) the chain stays one conjunct.
`!` binds tighter, as now: `!a <= b <= c` is `(!a) <= b <= c`.

### 6.3 Sections

`(<= 9)` stays a section of one operator. `(0 <= <= 9)` and `(<= b <= c)`
are not sections: an error, "a section takes one operator; write a lambda
`x => 0 <= x <= 9`". A method section that starts a chain already takes the
whole expression (`(.id == id)` is `x => x.id == id`,
crates/syntax/src/parser/sections.rs:1-6) **[checked]**, so `xs.filter
(.size <= limit)` is unchanged and `xs.filter (.size <= 9 <= limit)` would be
`x => x.size <= 9 <= limit`, which reads badly but is what the rule gives;
not worth a special case.

### 6.4 Diagnostics

The refused chains, now `E-PARSE` "expected the end of the declaration", get
messages of their own, Rust-style, labelled at the second operator:

- Mixed directions: `E-CALC-RELATION`'s wording, or a new code
  `E-COMPARISON-CHAIN` (C6): "a chain of comparisons goes one way: `<` and
  `<=` can't be mixed with `>` and `>=`", note "write `a < b && c < b`".
- `==`, `=`, `!=`, `in`: "`==` can't be chained", note "`a == b == c` would
  compare `a == b` with `c` in some languages; write `a == b && b == c`".
- `(a <= b) <= c`, today's type error: a note "to chain comparisons, leave
  out the brackets: `a <= b <= c`" when the bracketed side is a comparison.

### 6.5 Formatter, LSP, printing

- **Formatter.** It is token-based (crates/fmt/src/spacing.rs,
  layout.rs) and refuses files that don't parse **[checked]**: today `stitchwort fmt`
  on a chain is the parse error. Once chains parse, `a<=b   <= c` should
  print as `a <= b <= c` with no change to the formatter **[estimate]**; an
  example round-trip confirms it.
- **LSP.** Hover and go-to on an operand see the first copy of the middle,
  with the same span **[estimate]**; semantic tokens come from tokens, so
  they're unchanged.
- **Goals and messages** print the conjunction, `a ≤ b ∧ b ≤ c`, not the
  chain. Reading a conjunction back as a chain when the middles match is
  possible later; not proposed now, since a goal shows what was proved, and
  the chain and the conjunction are one term.
- **The equivalence checker** (crates/syntax/src/equivalence.rs) compares
  trees without spans; `Chain` is a distinct `BinOp`, so a chain and its
  hand-written conjunction differ there, which is right for the converter.

## 7. Docs and the guide

- docs/syntax.md: the operator table's `a < b, a <= b` and `a > b, a >= b`
  rows say "Not associative"; they'd say "chain: `a <= b < c` is `a <= b &&
  b < c`", with a short section under the comparisons (the rules of §5.2,
  the middle once, the refused chains).
- docs/proving-guide.md "Writing statements": prefer `lo ≤ x ≤ hi` to `lo ≤
  x ∧ x ≤ hi` in statements, the same way it prefers operators to prefix
  forms; the term is the same.
- The AoC statement style memory and CLAUDE.md's `.sw` rules could mention
  it once it lands (the orchestrator's call).

## 8. Interactions checked and not affected

- `rewrite … in` and `at` stop at their keywords, the pattern guard at `=>`
  (docs/proposals/pattern-guards.md §2.2): a chain inside either is parsed
  by the same `cmp_expr` and ends at the same stops **[estimate]**.
- `calc` steps take `calc_operand`, which is above the relations
  (parser.rs:3010-3022) **[checked]**, so `_ <= a <= b` in a `calc` step is
  still an error, as it should be: a step is one relation.
- `x in lo..hi`-style ranges (Kotlin, Rust) are another answer to the same
  problem; Stitchwort's `in` is list membership, and a range type is a
  bigger change. Not proposed.

## 9. Sites that would read better

A search for `p op m (&& | ∧) m op q` with the same `m` on both sides
(`rg --pcre2` over `*.sw`) finds 87 lines: 32 in aoc/, 33 in the standard
library (crates/elab/src/std), 1 in games/, 21 in examples/. The 66 outside
examples are in 30 files **[checked]**. The reversed form `x >= lo && x <=
hi` doesn't occur. A sample:

| Site | Today | Chained |
| --- | --- | --- |
| aoc 2020 day 2, Day02.sw:45 (D2385's example) | `entry.low <= times ∧ times <= entry.high` | `entry.low <= times <= entry.high` |
| aoc 2020 day 2, Spec/Spec.sw:12 | `entry.low <= appearances ∧ appearances <= entry.high` | `entry.low <= appearances <= entry.high` |
| aoc/src/Aoc/Common/Range.sw:21 | `range.from ≤ id ∧ id ≤ range.to` | `range.from ≤ id ≤ range.to` |
| aoc 2021 day 17, Day17.sw:68 and Spec | `target.left ≤ probe.x ∧ probe.x ≤ target.right ∧ target.bottom ≤ probe.y ∧ probe.y ≤ target.top` | `target.left ≤ probe.x ≤ target.right ∧ target.bottom ≤ probe.y ≤ target.top` |
| aoc 2020 day 4, Spec/Spec.sw:45 | `150 <= n ∧ n <= 193`, `59 <= n ∧ n <= 76` | `150 <= n <= 193`, `59 <= n <= 76` |
| aoc 2024 day 9, Spec/Spec.sw:76 | `target <= position && position < target + length` | `target <= position < target + length` |
| aoc 2024 day 2, Day02.sw:34 | `lower < higher && higher <= lower + 3` | `lower < higher <= lower + 3` |
| games/rogue Level.sw:21 | four comparisons, `row` and `column` each twice | `corner.row ≤ position.row ≤ corner.row + down ∧ …` |
| std Text.sw:402 | `(97 <= code && code <= 122) \|\| (65 <= code && code <= 90)` | `97 <= code <= 122 \|\| 65 <= code <= 90` |
| std Terminal/Key.sw:148-249 (9 lines) | `32 ≤ byte && byte ≤ 126` … | `32 ≤ byte ≤ 126` … |
| std Parse/Reads.sw:1513 etc. (6 lines) | `atLeast ≤ count ∧ count ≤ atMost` | `atLeast ≤ count ≤ atMost` |
| std Nat/Arith.sw:311-335 (`Nat.between*`) | `(lo ≤ x ∧ x ≤ hi) = True` | `(lo ≤ x ≤ hi) = True` |
| aoc 2025 day 9, Day09.sw:69 | `(one ≤ value ∧ value ≤ other) ∨ (other ≤ value ∧ value ≤ one)` | `one ≤ value ≤ other ∨ other ≤ value ≤ one` |

The sweep is optional and separate. Under C3 (a), sites inside a longer
`∧` (Day17, Level.sw, Reads.sw:1513) change shape and may need their proofs
adjusted; sites that are a whole conjunction on their own (Day02, Range.sw,
Key.sw, Arith.sw) keep their exact term and hash.

## 10. Size and order of work

Sizes are **[estimate]**.

1. **Parser** (Sonnet, 45-60 min): the loop in `cmp_expr`, `BinOp::Chain`,
   the direction rule, the refused-chain errors, the section error, the
   bracketed-comparison note; unit tests (shapes of `a <= b < c`, `a > b >=
   c`, four links, `&&` around a chain; the errors), updating the `a > b >
   c` test.
2. **Elaborator** (Sonnet, 45-60 min): `Chain` wherever `And` is matched by
   name (§6.1); the effects rewrite (§4.2).
3. **Examples and docs** (30 min): `examples/accept/chained-comparisons.sw`
   (Prop and Bool forms, `if h:`, a guard, `auto`, `omega` from a chained
   hypothesis, a performing middle run once with `#eval` showing it, a
   descending chain, a `test` that fails on its second link),
   `examples/reject/chained-comparison-*.sw` for each refused form;
   docs/syntax.md and the proving guide (§7); a `stitchwort fmt` round trip.
4. **Sweep** (Sonnet or DeepSeek, 30-45 min, a separate lane): §9's sites,
   with their proofs where C3 (a) changes a shape; `task test:one` per day
   touched.

Steps 1-3 are one lane, about 2.5-3 hours. The kernel is untouched.

## 11. Decisions for Matt

Numbered C1 to C6 here; the orchestrator gives them D numbers.

- **C1. Which chains.** `<`/`<=` together and `>`/`>=` together, any
  length; refuse mixed directions, `!=`, `in`, and (for now) `=`/`==`. A
  descending chain keeps its links in the written order, each flipped as a
  single `>` is. **[rec: yes]**
- **C2. `=` and `==` in chains.** (a) refused for now, with a targeted
  error; (b) allowed alone (`a = b = c`); (c) allowed with orders, as
  Python and `calc` do (`a <= b = c`). **[rec: (a); revisit if a site asks
  for it]**
- **C3. A chain inside a longer `∧`.** (a) one conjunct, `(lo ≤ x ∧ x ≤ hi)
  ∧ p`; (b) spliced, `lo ≤ x ∧ (x ≤ hi ∧ p)`, the hand-written tree.
  **[rec: (a)]**
- **C4. A pure middle.** (a) its term used twice, so a chain is exactly the
  hand-written conjunction (term, hash, goals); an expensive middle is
  computed twice at run time, as by hand, and the docs say to `let` it;
  (b) always `let`-bound, computed once, with a different hash. **[rec:
  (a)]**
- **C5. A middle that performs.** Run once, left to right, with the short
  circuit (§4.2), in the first lane; or refused with `E-ABILITY` until
  needed. **[rec: run once, in the first lane]**
- **C6. Error code for a mixed-direction chain.** Reuse `E-CALC-RELATION`'s
  wording under a new code `E-COMPARISON-CHAIN` (also for `==`/`!=`/`in`
  chains), or plain `E-PARSE` with the message. **[rec: `E-COMPARISON-CHAIN`]**

And, for the orchestrator: start the implementation lane (steps 1-3) on
Sonnet once C1-C6 are settled, and the sweep (step 4) after it merges.

## Sources

- Python language reference, "Comparisons": chains of any comparison
  operators, each operand evaluated at most once, `False == False in
  [False]`. From memory, **unverified**.
- Julia manual, "Chaining comparisons": evaluation order of a chain's
  operands undefined. From memory, **unverified**.
- Rust compiler diagnostic "comparison operators cannot be chained", with
  the `&&` suggestion. From memory, **unverified**.
- Swift, `ComparisonPrecedence` has no associativity. From memory,
  **unverified**.
- Haskell report, fixity `infix 4` for `<`, `<=`, `==`. From memory,
  **unverified**.
- Lean 4 core notation for `≤` (non-associative infix); Mathlib's
  `Set.Icc`. From memory, **unverified**.
