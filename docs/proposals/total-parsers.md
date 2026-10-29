# Design note: parsers that are total by type

**Status:** design only, 29 October 2026, for Matt's review. Ticket SW-884. Nothing in the language or Std changes. The prototype is [`total-parsers/consumes.sw`](total-parsers/consumes.sw), which checks and whose 8 tests pass. Decisions D1710 to D1712 are in §8.

Matt asked whether, and how, Stitchwort could get total parser combinators the way Idris 2 and Agda do: the type rules out a parser that could loop forever, such as `many (optional x)` or a left-recursive grammar, at compile time.

Evidence labels: **[checked]** means read in this repository's source, or run with the release build (`target/release/stitchwort`, 29 October). **[cited]** means read in the primary source; the copies are listed in Appendix B. **[inferred]** means reasoned from checked or cited facts but not run. **[unverified]** means believed but not confirmed.

## 0. In brief

- **Stitchwort's parsers are already total.** `Std.Parse` can't loop: `many`, `findAll`, `repeat` and `recursive` all run on fuel, and the kernel checks them like any other definition (§1). In Idris and Agda the consumes-index is what *makes* `many` total. Here, a type would do something smaller. It would turn one class of bug from a fatal error at run time into a type error at compile time. That class is "this loop's parser can succeed without reading", plus left recursion.
- **What the precedents guarantee** (§2). Idris 2's `Grammar … (consumes: Bool) …` and agdarsec's size-indexed parsers guarantee that the parse terminates, and nothing more. They say nothing about correctness, ambiguity or error quality. Idris's guarantee rests on two `assert_total`s inside its own interpreter, so the library's design carries it, not the checker. agdarsec's author calls proof combinators for such parsers "still an open problem". Danielsson's coinductive library is the only one with a correctness proof, and its back end is "at least exponential".
- **The options, ranked** (§3, §5):
  1. **(e) Do nothing,** with two small fixes. `many (optional x)` fails on *every* input, so the first test of the grammar finds it **[checked]**. The real gaps are left recursion hidden behind an earlier alternative, which fails only on bad input **[checked]**, and a forged `Parse.Mark` that silently cuts `many` short **[checked]**.
  2. **(a) A consumes-indexed parser data type.** It works today. The prototype has `Parser (consumes: Bool) a`, an agdarsec-style `fix` for recursive grammars, nested brackets, arithmetic and day 3. `many (optional p)` and left recursion are type errors **[checked]**. The lemma for `optional p` over any `p` that Std.Parse can't state is a three-line `match` here **[checked]**. On day 3 it is about 12 times faster than `Std.Parse` **[checked, with caveats]**. But it reads as nested `seq … (x => …)` lambdas, and it gives up direct style, which is what SW-883 is making shorter.
  3. **(d) A lint** for `many` over a parser that may read nothing. It is cheap, but it catches only what the first test already catches.
  4. **(c) Prove in Std that fuel never runs out.** This is blocked on the same lifting lemma as D1651's "full route". It is a theorem for people writing proofs, not a guarantee for people writing grammars.
  5. **(b) Index the `Parse` effect by consumption.** This isn't possible in Stitchwort's effect system. A row holds one instance of each ability, so a row can't hold both `Read True` and `Read False`, and a row's index says nothing about what the code actually reads **[checked]**. It would need graded effects.
- **Recommendation** (§7): don't make Std's parsers total by type now. Do the two small fixes of (e): make a forged mark unable to change a result, and document left recursion. Keep (a) on file as the route to take if proving parsers becomes a goal (D1651). The prototype shows that the data style is where parser proofs become easy, not where grammars become safe.

## 1. What Std.Parse guarantees today

`Parse.many` runs `Parse.manyFuel` with the number of characters left, plus one, as its fuel (`crates/elab/src/std/Parse/Parse.sw:342-357`) **[checked]**. Each round marks the input, runs `optional parser`, and checks that the offset grew. If it didn't, the parse stops with ``Parse.fatal "`many`: the parser matched without reading anything"``, which no choice backs out of. `findAll` (`:480`) and `recursive` (`:566-577`) work the same way. When `recursive` runs out of fuel, that is fatal too ("the parser called itself without reading anything").

So:

- **Termination is a theorem the kernel checks.** The fuel makes each loop structurally recursive. This is stronger than Lean's `partial def manyCore` and Koka's `pretend-decreasing` (§2.4).
- **The fatal error fires whenever the bad loop is reached.** A nullable parser under `many` succeeds without reading at the point where the loop would end, so the error comes on every input. A scratch file ran `many (() => optional (() => char 'a'))` on `aaa`, the empty line and `b`, and `many (() => takeWhile …)` on `aab` **[checked]**. Every run fails, for example with ``column 4: `many`: the parser matched without reading anything``. The first test of such a grammar finds the bug.
- **Left recursion can hide.** In this grammar, the left-recursive alternative comes last:

  ```
  def sum(): {Parse} Nat := recursive (self =>
    oneOf [
      nat,
      () =>
        let left := self()
        char '+'
        left + nat()
    ])
  ```

  It parses `12` as 12. On `1+2` it says `column 2: expected the end of the line, got '+'`, because PEG choice never comes back to the second alternative after `nat` succeeds. Only on `x` does it fail with ``column 1: `recursive`: the parser called itself without reading anything`` **[checked]**. A test suite of good inputs passes. The bug shows up on bad input, as a confusing message, or as a grammar that quietly accepts less than intended. A type would reject this grammar.
- **The "fuel never matters" argument assumes honest marks.** `Parse.Mark = { rest, offset, left }` is an ordinary record (`:31`), and `Parse.reset` takes any mark (`:57`, handler `:133`). The fuel is read from `mark().left`. A scratch test resets to `{ here | left = 0 }` and then runs `many digit` on `123`. It returns **one** digit, with no error **[checked]**. No sensible grammar does this. But it means the statement "the fuel changes nothing" is true only for marks that `mark` made, and Std doesn't enforce that. Any theorem of option (c) would need it as a hypothesis.
- **No proofs about loops.** parser-combinators.md §8, "Not proved": lifting a fact about `p` through `optional p` is an induction over `p`'s computation tree, which an opaque thunk doesn't expose. So there are no lemmas for `many`, `findAll` or `repeat` **[checked: the note]**.

## 2. Precedent

### 2.1 Idris 2, `Text.Parser.Core`

`Grammar : (state : Type) -> (tok : Type) -> (consumes : Bool) -> Type -> Type` is a data type of grammar descriptions, interpreted by `doParse` over a `List` of tokens **[cited: Core.idr]**. The constructors carry the index:

- `Terminal : … -> Grammar state tok True a` reads a token. `Empty`, `NextIs`, `EOF`, `Position`, `Commit` and `Act` are `False`. `Fail : … -> Grammar state tok c ty` works at any `c`, because failing never violates "consumes on success".
- `SeqEat : Grammar state tok True a -> Inf (a -> Grammar state tok c2 b) -> Grammar state tok True b`, and `SeqEmpty : Grammar … c1 a -> (a -> Grammar … c2 b) -> Grammar … (c1 || c2) b`. `>>=` takes `inf c1 (a -> Grammar …)` and picks one of the two by `c1` (Core.idr:59-66). So the continuation is lazy (`Inf`, codata) only after something consumed. That is where a recursive grammar may refer to itself, and the productivity checker sees the guard.
- `Alt : Grammar … c1 ty -> Lazy (Grammar … c2 ty) -> Grammar … (c1 && c2) ty`.
- `many : Grammar state tok True a -> Grammar state tok False (List a)` and `some : Grammar … True a -> Grammar … True (List1 a)` (Parser.idr:76-84).

**What it guarantees.** `doParse` is total, so every parse terminates, and a `Grammar … True` that succeeds has read a token.

**What it doesn't guarantee:**

- **The checker doesn't verify the interpreter.** `doParse`'s `SeqEat` and `ThenEat` cases call `assert_total doParse s com (next v.val) xs` (Core.idr:345, 355) **[cited]**. The token list does shrink there, but Idris can't see it. The guarantee is "the library is designed right", trusted.
- **Nothing about meaning.** It doesn't say the grammar parses what was intended, or that it is unambiguous. `Alt` takes the first success, `commit`/`mustWork` control backtracking by hand, and error quality is the author's business.
- **Index arithmetic leaks into the library.** `option` is defined twice, once for each value of `c`. `sepBy1` needs `rewrite sym (orFalseNeutral c)`, and `choiceMap` needs `andSameNeutral` (Parser.idr:26-30, 58, 156) **[cited]**. The prototype hit the same wall (§3.1).
- Left recursion is not handled. It is simply not total, because a self-reference before consuming isn't under `Inf` **[inferred]**.

### 2.2 agdarsec (Allais)

From the paper ("agdarsec — Total Parser Combinators", Allais, 2018 draft) and the repository **[cited]**:

- A parser is indexed by an upper bound on the input's length. `record Parser (A : Set≤ l) (n : ℕ)` has `runParser : ∀ {m} → .(m ≤ n) → Lift (Toks m) → M (Success Toks A m)` (`Text/Parser/Types.agda`).
- **Every success consumes.** `record Success … (n : ℕ)` has `.small : size < n` (`Types/Core.agda`). In the paper's words: "we adopt a radical solution: for a parser's run to be considered successful, it must have consumed some of its input. Some nullability can be recovered later … when defining combinators where one of the sub-parses is allowed to fail" (§5). Hence `_<&?>_ : Parser A ⇒ □ Parser B ⇒ Parser (A × Maybe B)`, with no stand-alone `optional`.
- **Recursion goes under the box.** `□ A n` is "A at every m < n". `fix : ∀ A → [ □ A ⟶ A ] → [ A ]` "would correspond exactly to strong induction for the natural numbers" (§4). Sequencing gives the second parser a boxed type, `_<&>_ : [ Parser A ⟶ □ Parser B ⟶ Parser (A × B) ]`, so the recursive call is usable after something has been read. "Trying to define a left-recursive grammar by immediately using a recursive substructure on the left is now a type error. But it still possible to have some on the right or after having consumed at least one character" (§5). Left chains come back as `chainl1`/`hchainl`.
- **Needs only strong induction**, no coinduction: "it is compatible with languages a lot less powerful than Agda" (§8.1).
- **Limits**: totality only. The library is list-of-successes, so ambiguity is allowed. Users insert `box` by hand where Agda has no coercions (§6). Nullable top-level grammars must be restructured. And: "If we want to provide our users with the tools to modularly prove some of the properties of their grammars, we need to come up with proof combinators corresponding to the value ones. As far as we know this is still an open problem" (§9).

### 2.3 Danielsson, "Total Parser Combinators" (ICFP 2010)

A different design **[cited]**. Grammars are values of a mixed inductive-coinductive type. A parser's index is its *initial bag*, the results it gives on the empty string, rather than a Boolean. Sequencing reads an argument coinductively "only … if the other argument does not accept the empty string". It "guarantees termination of parsing, while still allowing many forms of left recursion". The type is more informative than Idris's, and the library has a formal semantics and a machine-checked correctness proof. But "in the worst case, parse is at least exponential in the size of the input". It also needs codata, which Stitchwort doesn't have: partial.md §2 leaves general coinductive types as a larger step **[checked]**. agdarsec §8.1 sums up the comparison: Danielsson can certify, agdarsec is "more lightweight".

### 2.4 Elsewhere

| System | Loops that read nothing | |
|---|---|---|
| cats-parse (Scala) | Two types, `Parser` (must consume on success) and `Parser0`. `rep` exists only on `Parser` | the consumes-flag as two types, no dependent types (parser-combinators.md §3.1) **[cited there]** |
| Lean 4 `Std.Internal.Parsec` | `partial def manyCore (p : Parsec ι α) …` | nothing can be proved about it **[cited: Basic.lean:153]** |
| Koka `std/text/parse` | `many-acc(pretend-decreasing(p), …)`, with the comment "The `many` combinator is non-divergent only when `p` always consumes input or `fail`s" | Koka's `div` effect would otherwise show in the type; `pretend-decreasing` hides it **[cited: parse.kk:200-205]** |
| Effekt, Unison | no termination checking, so nothing to guarantee | **[unverified]** |
| Parsec, nom, winnow | a run-time error, as Std.Parse | parser-combinators.md §3.1 **[cited there]** |

Among effect languages I found none whose effect parser is total by type. Koka, the one with a divergence effect, opts out of it.

## 3. The options in Stitchwort

### 3.1 (a) A consumes-indexed parser data type

**Built as a prototype**: [`total-parsers/consumes.sw`](total-parsers/consumes.sw), 329 lines, 8 tests, 3 theorems **[checked]**. In outline:

```
def Within: Bool → Nat → Nat → Prop       -- True: rest < input; False: rest ≤ input
  | True, rest, input => rest < input
  | False, rest, input => rest ≤ input

type Reply (consumes: Bool) (input: List Char) (a: Type) =
  | Got (value: a) (rest: List Char) (within: Within consumes rest.length input.length)
  | Missed (expected: Text)

type Parser (consumes: Bool) (a: Type) = { run: (input: List Char) → Reply consumes input a }

def seq [c1 c2: Bool] (p: Parser c1 a) (next: a → Parser c2 b): Parser (eitherConsumes c1 c2) b
def alt [c1 c2: Bool] (p: Parser c1 a) (q: Parser c2 a): Parser (bothConsume c1 c2) a
def optional (p: Parser c a): Parser False (Option a)
def many (p: Parser True a): Parser False (List a)     -- `decreasing input.length`; the proof in `Got` is the measure
```

The type is a parameter, not an index: `Reply` carries the bound as a proof field. No inductive family is needed.

`many (optional (char 'a'))` is refused **[checked]**:

```
expected `Parser True ?0`, but this has type `Parser False (Option Char)`
```

**Recursive grammars** follow agdarsec. `Bounded strict bound consumes a` runs on inputs within a bound, and `Bounded True n` is the box. `eat (p: Bounded s n True a) (next: a → Bounded True n c b)` is Idris's `SeqEat`: what follows a consuming parser runs below the bound. `fix` is defined by structural recursion on the bound, and the kernel accepts it. At `Succ m`, the body's self is the fixed point at `m`, because `r < Succ m` and `r ≤ m` are the same by computation. At `Zero` the self is unreachable, which `Bool.falseNotTrue` shows. Left recursion is refused **[checked]**:

```
def leftRecursive: Parser True Nat := fix (n => self =>
  balt (bseq self (left => …)) (lift nat))
-- expected `Bounded False n True Nat`, but this has type `Bounded True n True Nat`
```

**Costs met while building it** **[checked]**:

- **Index arithmetic.** `optional` written as `alt (map p Some) (pure None)` has the index `bothConsume c False`, which doesn't compute while `c` is a variable. This is the same thing Idris works around with two definitions of `option`. The prototype writes `optional` directly.
- **No subtyping.** A `Parser True` isn't a `Parser False`, so `mayNotConsume` has to be called where needed, as in `textRest`.
- **Two copies of the combinators**: `seq`/`alt`/`map`/`many` for plain parsers, and `bseq`/`balt`/`bmap`/`bmany` for bounded ones. There are also `lift` (agdarsec's `box`) and `below`. A real library would merge them by making every parser bounded, as agdarsec does. Then every signature carries the `n`.
- **The checker is fine with it.** `decreasing input.length` in `manyFrom` and `findAllFrom`, `auto`-free proofs from `Nat.leTrans`, and the structural `fixAt` all checked on the first try once the types were right. Multi-letter implicits need `[c1 c2: Bool]`.
- `text` needs no proof that its text is non-empty. On `""` it simply fails, which a consuming parser may do, as Idris's `Fail` may.

**What it buys for proofs.** A parser here is a pure function, so facts lift through combinators by a `match` on what the inner parser gives. The prototype proves `optionalResultLemma` (what `optional p` gives, for *any* `p`) and `altResultLemma`, each in a few lines, and `day3Example` by `rfl` **[checked]**. These are exactly the lemmas parser-combinators.md §8 couldn't state for `Std.Parse`. So the data style is where D1651's "full route" becomes ordinary work. The type index has nothing to do with that. It is a property of data style.

**Run-time cost.** The day 3 grammar in this style (§4.1) was run on the real input and on the input ×10 (180 KB), machine back end, warm cache **[checked]**:

| | real input | ×10 |
|---|---|---|
| prototype (`findAllFrom instruction`) | 0.20 s, 82 MB | 0.36 s, 93 MB |
| `Std.Parse` day 3 (`findAll instruction`) | 0.41 s, 111 MB | 2.40 s, 121 MB |

The part-1 answer matches (174960292). Beyond the 0.2 s start-up, that is about 0.16 s against 2.0 s, roughly 12 times faster. **Caveat:** the prototype keeps no positions and no furthest-failure set, and its errors are bare strings, so it does much less per try. Whether the proof fields cost anything at run time I didn't measure; I expect them to be erased as `Prop` **[unverified]**. parser-combinators.md §7.1 measured data parsers at 1.7 to 2.8 times faster than abilities per line, with full errors in neither **[cited there]**.

**Abilities and handlers.** A data parser is pure. `Fail` helpers need converting, and `IO` or `Each` can't be used inside without an effectful `run` field (`run: input → {e} Reply …`), which would make every combinator effect-polymorphic **[inferred]**. The `Each`-over-`Parse` trick of parser-combinators.md §4.3 is lost.

**Users.** The day 3 rule becomes `seq (text "mul(") (u => seq shortNumber (left => seq (char ',') (comma => …))))` (§4.1). That is the reading problem that made parser-combinators.md §4.2 reject data parsers, and it is untouched by SW-883's direct-style work, since none of SW-883's forms (effectful arguments, `(char ','; shortNumber())` blocks) apply to values that aren't effectful code.

**Variant (a′): typed pieces inside direct style.** Keep `{Parse}` grammars, but give the loops a typed, consuming head: `Parse.manyAfter (head: Parser True h) (body: h → {Parse} a)`. The head would be run through today's `mark`/`reset`, so no new operation is needed. The type would forbid `many (optional x)` only where users opt in, and the body could still `reset` backwards, so the run-time check stays **[inferred, not built]**. It splits the vocabulary in two for a guarantee the first test already gives. Not recommended.

### 3.2 (b) Indexing the `Parse` effect by consumption

Rows don't support this **[checked]**:

```
ability Read (consumes: Bool) where
  step: () → {Read consumes} Nat

def both(): {Read True} Nat :=
  let x := one()      -- {Read True}
  let y := none()     -- {Read False}
  x + y
-- E-TYPE-MISMATCH: `Read` is used with different arguments: `False` and `True`
```

A row has at most one instantiation of each ability (abilities.md, "Labels") **[checked]**. More fundamentally, a row's parameter is a claim about the whole computation's type, not something the operations add up: `def fake(): {Read True} Nat := 0` checks **[checked]**, because pure code lifts into any row. Tracking "has read" through sequencing needs *graded* effects, where the index of `p; q` is computed from those of `p` and `q`, as Idris's `c1 || c2` is. That would be a new feature of the effect system and of the `Comp` translation, which is far beyond this question.

What can be done is to put the index on the *value* of a computation rather than on its row. A parser `() → {Parse} (Σ result, proof that the offset grew)` can't work either, because the proof would be about the handler's state, which the parser can't see. That is why (c) has to work through the handler.

### 3.3 (c) Keep fuel; prove in Std that it never runs out

The theorem would say: if `p` consumes whenever it succeeds (from every state with an honest mark), then `many p` from any state gives what the unfuelled loop gives and never reaches `fatal`. What it needs:

1. **A semantic predicate "`p` consumes"** over `Parse.runFrom`. `runFrom` gives a `Result a Failure` without the final state, so a variant that returns the state is needed first **[checked: `Parse.sw:119-137`]**.
2. **The lifting lemma** for `optionalFrom` over an arbitrary `p`. This is parser-combinators.md §8's open problem: an induction over `p`'s `Comp` tree with function extensionality at each `Call`.
3. **Honest marks** as a hypothesis or an invariant (§1).
4. **Per-grammar obligations.** A user who wants the guarantee proves that their `p` consumes, through closure lemmas (`char` consumes; `p; q` consumes if `p` does and `q` doesn't `reset` backwards; …).

The result is a theorem that users must invoke, not a check that happens to them. It has no run-time cost, and the grammar text doesn't change. It is the same work as D1651's "full route", and it is worth doing only for that reason, for proofs about parsers. The safety it adds over the fatal check is nil, since termination already holds.

### 3.4 (d) A static check

Mark Std's parsers that may succeed without reading (`optional`, `many`, `sepBy`, `takeWhile`, `spaces`, `pure` values, `findAll`, …) with an attribute. Then have the elaborator warn when the argument of `many`, `many1`, `sepBy1`'s repeat, `findAll`, `lines`, `sections` or `recursive`'s self-call position is one of them, or a lambda whose body is a sequence of only such calls. Attributes exist (attributes.md, stage 1 built), and so do warnings (`W-…` codes in `crates/elab/src`) **[checked]**. The analysis can only be approximate. Direct-style code is monadic, so nullability isn't decidable from the text (Swierstra's point, parser-combinators.md §3.3) **[cited there]**. A conservative check finds `many (optional x)` and `many spaces`, which the first test finds anyway (§1). It doesn't find left recursion behind an earlier alternative, the one case tests miss, unless it also tracks "calls `self` before anything that must read". That is a small abstract interpreter over elaborated `Comp` code, real elaborator work for a rare bug **[inferred]**.

### 3.5 (e) Do nothing

The honest case for it:

- Totality, the property Idris and Agda buy with the index, is already guaranteed and checked (§1).
- The common bug, `many` over a nullable parser, fails on every input with a message naming the combinator and the column (§1). A grammar that was run once doesn't have it.
- Every alternative costs readability (a), a type-system feature (b), a hard proof (c) or elaborator work (d).

And the case against: left recursion behind an earlier alternative escapes tests of good input (§1), and forged marks can silently shorten `many` (§1). Neither needs a type. The first needs a sentence in the guide, and the second a small Std change (§7).

## 4. Day 3 and a recursive grammar under the viable options

Options (c), (d) and (e) leave grammar code exactly as it is today, so their versions are the current ones. (b) isn't viable. That leaves today's code and (a).

### 4.1 AoC 2024 day 3

**Today, and under (c), (d), (e)** (`aoc/src/Aoc/Year2024/Day03/Day03.sw`) **[checked]**:

```
def shortNumber(): {Parse} Nat := natDigits 1 3

def instruction(): {Parse} Instruction :=
  oneOf [
    () =>
      text "mul("
      let left := shortNumber()
      char ','
      let right := shortNumber()
      char ')'
      Mul left right,
    () => pick [("do()", Do), ("don't()", Dont)]
  ]

def parseInstructions (memory: Text): {Fail} (List Instruction) := Parse.all memory (() => findAll instruction)
```

SW-883 may shorten the first alternative to something like `Mul (shortNumber()) (char ','; shortNumber())` after `text "mul("`. That is its business; none of (c), (d) or (e) interferes.

**Under (a)** (`consumes.sw`, tests "day 3" and "day 3, four digits") **[checked]**:

```
def shortNumber: Parser True Nat :=
  seq (many1 digit) (digits => if digits.length ≤ 3 then pure (Nat.fromDigits digits) else failWith "a number of 1 to 3 digits")

def instruction: Parser True Instruction :=
  alt (seq (text "mul(") (u =>
    seq shortNumber (left =>
      seq (char ',') (comma =>
        seq shortNumber (right =>
          map (char ')') (close => Mul left right)))))) (alt (map (text "do()") (u => Do)) (map (text "don't()") (u => Dont)))

def instructions (memory: Text): List Instruction := findAllFrom instruction memory.toList
```

`findAllFrom` takes a `Parser True`, so its loop needs no run-time check: the proof in `Got` is the `decreasing` measure.

### 4.2 Nested lists

**Today** (`Parse.sw`, test "Parse: recursive") **[checked]**:

```
def nestedSum(): {Parse} Nat := recursive (nested =>
  oneOf [
    nat,
    () =>
      char '['
      let items := sepBy nested (() => char ',')
      char ']'
      items.sum
  ])
```

**Under (a)** (`consumes.sw`, tests "nested", "nested, unbalanced") **[checked]**:

```
def nested: Parser True Nat := fix (n => self =>
  balt (lift nat) (eat (lift (char '[')) (open =>
    bseq (boptional (bsepBy1 self (char ','))) (items =>
      bmap (lift (char ']')) (close => (items.getOrElse []).sum)))))
```

`self` is a `Bounded True n`, which is usable only inside `eat`'s continuation, after `[`.

### 4.3 Arithmetic with precedence

**Under (a)** (`consumes.sw`, test "arithmetic": `2*(3+4)+1` is 15) **[checked]**:

```
def arithmetic: Parser True Nat := fix (n => self =>
  let factor := balt (lift nat) (eat (lift (char '(')) (open => bseq self (value => bmap (lift (char ')')) (close => value))))
  let term := bseq factor (first => bmap (bmany (eat (lift (char '*')) (times => below factor))) (more => (Cons first more).product))
  bseq term (first => bmap (bmany (eat (lift (char '+')) (plus => below term))) (more => (Cons first more).sum)))
```

**Today** the same grammar reads like this. It is not in the repository; it is scratch `arith-today.sw`, whose test of `2*(3+4)+1` passes **[checked]**:

```
def arithmetic(): {Parse} Nat := recursive (self =>
  let factor := () => oneOf [
    nat,
    () =>
      char '('
      let value := self()
      char ')'
      value
  ]
  let term := () => (Cons (factor()) (many (() =>
    char '*'
    factor()))).product
  (Cons (term()) (many (() =>
    char '+'
    term()))).sum)
```

## 5. Comparison

| | (a) data type | (b) indexed effect | (c) lemmas | (d) lint | (e) nothing |
|---|---|---|---|---|---|
| Catches `many (optional x)` | at compile time | — | as a theorem, if the user proves `p` consumes | as a warning | on the first run |
| Catches hidden left recursion | at compile time | — | as a theorem | only with a real analysis | only on bad input |
| How grammars read | nested `seq`/`eat` lambdas, `lift`/`below` | — | unchanged | unchanged | unchanged |
| Annotations | index arithmetic, `mayNotConsume`, the box | — | proof obligations per grammar | none | none |
| Implementation | a new Std module, about 600 lines with errors and positions **[inferred]** | graded effects: a type-system change | the lifting lemma (hard, open) and an honest-mark invariant | an attribute and an elaborator check | two small fixes |
| Run time | faster on day 3, with poorer errors (§3.1) | — | none | none | none |
| Helps proofs (D1651) | **yes**: lifting lemmas by `match` | — | it *is* the full route | no | no |
| Abilities and handlers | pure; needs effect-polymorphic `run` for others | — | unchanged | unchanged | unchanged |
| Works today | yes (prototype) | no (checked) | no | no | yes |

Ranked by value over cost for Std as it is used (puzzle input, read and written often): **(e) with its two fixes, then (a) as an opt-in library if proofs become a goal, then (d), then (c), then (b).**

## 6. Interaction with SW-883

SW-883 (`docs/proposals/direct-style-grammars.md`, in progress) is making direct-style grammar code shorter: effectful calls in argument position, `let () := …;` and bracketed blocks as arguments. Its evidence file shows `Mul (shortNumber()) (let _ := char ','; shortNumber())` working today **[checked: its `args.sw` at the time of writing]**. The interaction is one-way:

- Under (c), (d) and (e), grammars stay effectful code, and everything SW-883 adds applies.
- Under (a), grammars are values, and none of SW-883's forms apply. The data-style equivalent of its one-liner is the `seq … (left => seq … (comma => …))` chain of §4.1. Shortening that would need do-notation or user operators (D1207), a different language change. So adopting (a) as *the* Std parser would undo the point of SW-883. As a separate, opt-in library for grammars someone wants to prove things about, it wouldn't conflict.

## 7. Recommendation

**Don't make Std's parsers total by type.** Stitchwort already has what the type buys in Idris and Agda, termination checked by the kernel. The remaining benefit is moving a bug that tests find at once to compile time. That is not worth giving up direct style (a), a type-system feature (b) or a hard proof (c).

**The smallest first step is two small fixes under (e):**

1. **Make a forged mark unable to change a result.** For example, `many`, `findAll` and `recursive` could take their fuel from the length of `mark().rest`. That is O(n) per call to the loop, not per round, so it is cheap next to the loop itself. Or the handler could keep `left` itself, so that `reset` can't set it. Then "the fuel changes nothing" is true for any parser, which any later theorem (c) needs. It is a one-lane Std change with a test, the scratch test of §1 **[inferred]**.
2. **Document left recursion** in the guide's `recursive` section: the self-call must come after something that reads. Include §1's example, which passes good inputs and fails only on bad ones.

**If proving parsers becomes a goal** (D1651's full route), start from (a) rather than (c). The lifting lemmas that §8 of parser-combinators.md couldn't state are a few lines each over a data parser **[checked]**, where over `Std.Parse` they are an open induction. In that case the consumes-index comes almost for free, and is worth keeping, because the proof field is also the termination measure.

## 8. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D1710 | Total-by-type parsers in Std: pursue (a) as Std's parser, add it as a separate opt-in module, or not now? | [not now; keep `consumes.sw` as the design on file, and revisit together with D1651 if parser proofs become a goal] |
| D1711 | Make a forged `Parse.Mark` unable to change a result (fuel from the handler, not from the mark's `left`), as a small Std ticket? | [yes, one small lane with §1's test] |
| D1712 | Add a guide paragraph on left recursion behind an earlier alternative, with §1's example? | [yes, fold it into the D1711 lane] |

## Appendix A. Experiments

Committed: [`total-parsers/consumes.sw`](total-parsers/consumes.sw). Run `stitchwort test docs/proposals/total-parsers/consumes.sw`: 8 tests pass. `stitchwort check` passes and so does `stitchwort fmt`.

Scratch, not committed, in `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/sw884-exp/`:

| File | Shows |
|---|---|
| `fatal.sw` | `many (optional …)` and `many (takeWhile …)` fail on every input; left recursion as the last alternative passes `12`, rejects `1+2` with an ordinary message, and fails fatally only on `x` |
| `forged.sw` | resetting to `{ here \| left = 0 }` makes `many digit` on `123` return one digit |
| `indexed-ability.sw`, `indexed-ability2.sw` | (b): `Read True` and `Read False` in one row is refused; `{Read True}` holds code that reads nothing |
| `reject.sw`, `left.sw` | (a): `many (optional …)` and a left-recursive `fix` are type errors (messages in §3.1) |
| `proofs.sw` | the first form of the proofs now in `consumes.sw` |
| `arith-today.sw` | §4.3's arithmetic grammar with `Std.Parse` today |
| `timing.sw` | §3.1's timing, with part 1 printed to check the answer; run by `../sw884-scripts/time.sh` |

## Appendix B. Sources

Copies saved in `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/sw884-refs/`, with text extracted from the PDFs into `.txt`, and the `Text.Parser.Core` copy in `…/scratchpad/d2024-03/refs/idris-core.idr`.

- Idris 2: [`Text/Parser/Core.idr`](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser/Core.idr), [`Text/Parser.idr`](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser.idr).
- Allais, [agdarsec — Total Parser Combinators](https://gallais.github.io/pdf/agdarsec18.pdf); [repository](https://github.com/gallais/agdarsec) (`src/Text/Parser/Types.agda`, `Types/Core.agda`, `Combinators.agda`); ports [parseque](https://github.com/gallais/parseque) (Coq) and [idris-tparsec](https://github.com/gallais/idris-tparsec).
- Danielsson, [Total Parser Combinators](https://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf), ICFP 2010.
- Lean 4, [`Std/Internal/Parsec/Basic.lean`](https://github.com/leanprover/lean4/blob/master/src/Std/Internal/Parsec/Basic.lean); Koka, [`lib/std/text/parse.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/text/parse.kk).
- In this repository: [parser-combinators.md](parser-combinators.md) §§3–5, 8, 11; [tail-resumptive-handlers.md](tail-resumptive-handlers.md) (handler costs: why `Std.Parse` pays per operation and per forwarding handler); [abilities.md](abilities.md) (rows, labels, `Comp`); [well-founded-recursion.md](well-founded-recursion.md) (`decreasing`); [partial.md](partial.md); [attributes.md](attributes.md); `crates/elab/src/std/Parse/Parse.sw`; `aoc/src/Aoc/Year2024/Day03/`; [docs/comparisons/aoc-2024-day03-community.md](../comparisons/aoc-2024-day03-community.md) (D1651).
