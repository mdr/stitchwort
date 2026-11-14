# Text literals in patterns

**Status:** design note, 14 November 2026 (SW-3231, a paper lane). Nothing
is built. Two questions for Matt are in [§9](#9-questions-for-matt): the
syntax is user-visible. It's one of the foundation pieces for the formatter
written in Stitchwort (D3579; [self-hosted-fmt.md](self-hosted-fmt.md),
whose findings list has this gap).

Claims are marked **[source]** (read in the code at `dc26a104f`),
**[measured]** (the main checkout's release binary, built 15:46 today; the
probes are in [Appendix A](#appendix-a-the-probes)) or **[estimated]**.

## In plain words

**The problem.** A program that reads words, a lexer's keyword table, a
command reader or an AoC day's instruction names, wants to write

```
def keyword (word: Text): Option Keyword := match word with
  | "def" => Some Def
  | "theorem" => Some Theorem
  | "match" => Some Match
  | _ => None
```

Today that is a syntax error ("expected a pattern or `=`, but found
`"def"`"), so it's written as a chain of `if word == "def" then … else if …`
or a `Map` lookup. Both are longer, the chain is slower, and neither gives
the redundancy warning, the missing-case check or the arm equations that a
`match` gives.

**The change.** A text literal is allowed as a pattern. It means exactly
what spelling the text out would mean: `"def"` on a `Text` is the pattern
`MkText ['d', 'e', 'f']`, which already works today [measured]. On a
`List Char`, `"def"` is `['d', 'e', 'f']`. Optionally (the second
question), `"--" ++ rest` matches a text or character list that starts with
`--` and binds the rest, which a lexer's lookahead wants: `| "->" ++ rest`
instead of `| ['-', '>', ..rest]`.

**What it should do.** Nothing new in the kernel: the compiler already turns
a match on spelled-out characters into a tree that reads one character at a
time, so a 31-keyword match runs about 3 times faster than the `if` chain
[measured, one run each: 0.2 s against 0.6 s over a million words, beyond the
1.9 s the rest of the program takes]. A match with no catch-all says
"missing case: no arm matches texts other than "def", "theorem" and
"match"", and a proof gets `word = "def"` in an arm and `word ≠ "def"` …
in the catch-all's equation, as for characters. About 6 to 9 lane hours for
the first stage [estimated], all Opus (syntax and `match`, D2506).

## 1. How patterns work today

**Parsing** [source]. `crates/syntax/src/parser.rs`, the pattern atom
(around line 2040): names, `_`, numbers, `'c'`, `[…]` lists with an
optional `..tail`, brackets and tuples, `(-k)`, records. Anything else is
`unexpected_name("a pattern or `=`")`. A text literal is one `Tok::Str`
(decoded, escapes applied), or `StrStart`/`StrMid`/`StrEnd` around `${…}`
interpolations (`lexer.rs`, 19-33).

**Lowering** [source]. `crates/syntax/src/lower/patterns.rs`, `leaf_pattern`:
a `Tok::Num` is `Pattern::Num`, a `Tok::Char` is `Pattern::Char`. The AST
(`ast.rs`, 841) has `Num`, `NegNum`, `Char`, `Ctor`, `Tuple`, `Nil`, `Cons`,
`Named`, `Record`, `CtorFields`, `Or`. No text.

**Match compilation** [source]. `crates/elab/src/lib.rs`. Patterns are
compiled column by column into a `Tree` (Maranget style: pick a column,
split its constructors, keep for each constructor the rows that have it or a
variable). `pattern_ctor` (around 4380) turns each pattern into a
constructor and argument patterns, by the column's type:

- `'L'` is `MkChar 76 _` (4535): `Char` is
  `type Char = | MkChar (code: Nat) (valid: Char.isScalar code = True)`
  (`std/core/Char.sw`). The span is remembered in `char_patterns` so that
  messages can say `'L'` rather than `76`.
- A number is `Succ` of a number, `Zero` at the bottom, on `Nat`; `OfNat`
  or `NegSucc` around a `Nat` pattern on `Int`; `FZero`/`FSucc` on `Fin`.
- A column of numbers is not split constructor by constructor:
  `compile_numbers` (4250) makes one `Tree::NumCase`, an arm per number and
  a default, which becomes the kernel's `NumCase(x, arms, default)`
  ([core.md](../core.md), the `NumCase` rule; [number-patterns.md](number-patterns.md)).
  So `'a' | 'b' | _` is a case on `MkChar`, then one `NumCase` on the code.
- `[p, ..q]` is `Cons p q`, `[]` is `Nil`.

**Coverage** [source]. A split with no arm for some constructor leaves a
`Tree::Missing`; `missing.rs` writes the arm that would cover it, and the
errors of one `match` merge into one `E-NONEXHAUSTIVE` listing them as arms
to paste (SW-1027). A number case with no default row has
`Arm::other_numbers`: "no alternative of this `match` matches numbers other
than 3 and 7", or "characters other than 'a' and 'b'" when every number
came from a character (SW-1034) [measured, p4].

**What the kernel sees.** Constructor cases and `NumCase`s. No literal
patterns, no equality tests.

**Text** [source]. `type Text = | MkText (chars: List Char)`
(`std/core/Text.sw`). A text literal elaborates to `MkText` of a *range*, a
slice of an array of characters (`Term::Chars`; [core.md](../core.md),
"Text"; [compact-text.md](compact-text.md)), whose meaning is its expansion
`Cons (MkChar c rfl) … Nil`. Matching a range takes the `Nil` or `Cons`
branch without building cells. In the runtimes, a `Text` is native (a JS
string; the Rust runtime's own text value), and matching `MkText cs` makes
the list of characters (`charsOfText` in `crates/js/src/lib.rs` around 3117;
`Instr::TextChars` in `crates/rt/src/machine.rs`, 1522), in full.

## 2. What already works

Spelled out, text patterns work today [measured, p2, p5-p8, p10, p12]:

```
def kw (t: Text): Nat := match t with
  | MkText ['d', 'e', 'f'] => 1
  | MkText ['d', 'o'] => 2
  | _ => 0
```

- It checks and runs: `kw "def"` is 1, `kw "do"` 2, `kw "dog"` 0. The same
  on `List Char` with `['d', 'e', 'f']` and `['d', 'o', ..rest]`.
- `theorem kwDef: kw "def" = 1 := rfl` checks.
- In a proof, `match t with | MkText ['d', 'e', 'f'] => rfl` proves
  `t = "def"`: the goal is shown as `"def" = "def"`, since the printer
  already reads the spelled-out list back as text, and `rfl` closes it
  because comparison skips the `valid` proof fields ([core.md](../core.md),
  "Proof irrelevance"). The arm's context also shows the three hidden proofs,
  `valid✝²: Std.Char.isScalar 100` and so on: noise (§5, and a finding).
- The arm equations come for free (function-equations.md, stage 1):
  `kw.eq3: ∀ (t: Text) => t ≠ "def" → t ≠ "do" → kw t = 0`. With it and
  `if h: t = "def"` (`Text.decEq`), "`kw t = 1` only for `"def"`" is a
  ten-line proof (p12).
- A repeated literal is `W-REDUNDANT` (p10).
- The missing-case message is wrong in spirit: with no catch-all it says
  "no alternative of this `match` matches characters other than 'd'"
  (p3), the first gap the tree found, at one character, where the user
  thinks in words.

So the language already has the semantics; it lacks the notation, a message
in the user's terms, and some proof-side polish.

## 3. How others do it

- **Haskell (GHC).** `String` is `[Char]`, and a string literal pattern is
  allowed. GHC compiles it to an equality test (`eqString`) against the
  literal, tried in order, not into a character tree; with
  `OverloadedStrings`, a literal pattern needs `Eq` and `IsString` and is
  `(== fromString "…")`. No prefix pattern: `'-':'>':rest` on `[Char]`, or a
  view pattern `(stripPrefix "->" -> Just rest)`.
- **Lean 4.** String literal patterns are value patterns: the match compiler
  splits them with `caseValues`, one `if h : s = "def"` (decidable equality)
  per value, in order. Arms get `h : s = "def"`, the catch-all's equation
  lemma gets `s = "def" → False` for each earlier literal
  ([literal-match-facts.md](literal-match-facts.md) quotes the source). A
  catch-all is required. No prefix patterns.
- **Agda.** `String` is a primitive type, and string literals are allowed as
  patterns, compiled to primitive equality tests. A catch-all is required,
  and on an unknown string the catch-all clause doesn't compute: a proof
  splits on `_≟_` itself (`with`).
- **Idris 2.** String literals are constant patterns, compiled to a `case`
  on constants that tests `==` in order (backends may turn it into a
  switch); catch-all required. No prefix patterns; `unpack` to a
  `List Char` for character-level matching.
- **Elsewhere.** Elixir and Erlang match a binary prefix (`"de" <> rest`);
  Scala matches interpolations (`case s"$a-$b" =>`), which needs a search,
  so its meaning is "the first split that works".

Stitchwort differs from all four in one useful way: `Text` is *defined* as a
list of characters, so a text pattern needs no new primitive, no equality
test and no new kernel rule. It is a constructor pattern, so the match
compiler's column-by-column splitting turns many literals into a character
tree for free, and the kernel already checks it.

## 4. The design

### 4.1 Syntax

A pattern may be a **text literal without interpolations**: `"def"`, `""`,
`"\n"`, `"→"`, or a text block. It is allowed wherever a pattern is: arms,
alternatives (`| "y" | "yes" => …`), nested (`Some "on"`, `("add", n)`),
`matches | …`, clause lambdas, `if let`.

On a `Text` it means `MkText` of the characters: `"def"` is
`MkText ['d', 'e', 'f']`, `""` is `MkText []`. On a `List Char` it means the
list: `['d', 'e', 'f']` (question D3591). The meaning is chosen by the
column's type, as a number pattern's is (`Nat`, `Int` or `Fin`), and as `[]`
on a `NonEmptyList` is an error rather than `Nil`.

**Why also `List Char`.** The formatter's lexer is a state machine over the
remaining `List Char` (self-hosted-fmt.md, "Lexer"), as is any hand-written
parser in Stitchwort today, and `Std.Parse` works on `List Char` too. Its
lookahead and its keywords are character-list patterns. Expressions don't
change: `"ab"` is still a `Text`, and `def x: List Char := "ab"` is still a
type error [measured]. The pattern is the only place the literal is read at
the column's type, so a reader can always tell from the scrutinee. The cost
is that `match cs with | "def"` works while `cs == "def"` doesn't; the
error for the latter already says `expected List Char, but this has type
Text`, and could gain a note pointing at `.toList` (a finding).

On any other type it is `E-TYPE-MISMATCH` at the pattern: "a text pattern
matches a `Text` or a `List Char`, but this is `Nat`".

**Interpolation** (`"${a}b"`) is refused with a message of its own (code
`E-TEXT-PATTERN`): "a text pattern can't interpolate". Its note depends on
D3592: with prefixes, "to match a text that starts with `"--"`, write
`"--" ++ rest`"; without, "use `Text.stripPrefix` in a guard". Today it's
the generic `E-PARSE` [measured, p9].

### 4.2 Prefixes, `"lit" ++ rest` (the second question)

`"--" ++ p` matches a text or character list that starts with `--`, and
the rest by `p`. The left must be a text literal; `p` is any pattern of the
same type, so `"a" ++ "b" ++ rest` is `"ab" ++ rest` and `"a" ++ "b"` is
`"ab"`. `++` is right-associative here as in expressions.

- On a `List Char`: `"->" ++ rest` is `['-', '>', ..rest]`. Nothing new.
- On a `Text`: `"--" ++ rest` is `MkText ['-', '-', ..r]` with `rest` bound
  to `MkText r`, a value the match builds rather than a part it found. The
  match compiler has no such binding today: a row's `aliases` are variables
  at levels. The arm would get a hidden `let rest := MkText r` at its start.
  In a proof, the goal then has `t` as `MkText ['-', '-', ..r]` and `rest`
  as `MkText r`; `t = "--" ++ rest` holds by `rfl` (`Text.append` unfolds
  to `List.append` on a `Cons`). A nested `p` that is itself a text pattern
  (a literal, a prefix, `_`) expands into the list directly with no `let`.
- Only a prefix. `rest ++ ".sw"` and `a ++ "-" ++ b` are refused with
  `E-TEXT-PATTERN` ("a text pattern can only take a fixed start"), whose
  note names `Text.endsWith`/`stripSuffix` and `splitOn` in a guard. A
  suffix or a middle needs a search, which a constructor pattern can't
  express and whose "which split" rule (Scala's first split) is a rule a
  reader has to know.

**Why `++`.** It is the expression that would build the value, as
`[x, ..rest]` is in lists, and Stitchwort's text append is already `++`.
Elixir's `<>` and an interpolation form (`"--${rest}"`) were considered:
`<>` is a new operator for one use, and an interpolation pattern suggests
that `"${a}-${b}"` would work too.

**Weighing it.** For a lexer, the gain is real: Stitchwort's lexer has about
20 multi-character tokens and comment openers (`->`, `=>`, `:=`, `..<`,
`--|`, `"""`, `${`) [source: `crates/syntax/src/lexer.rs`], each a
lookahead arm, and `| "..<" ++ rest` reads better than
`| ['.', '.', '<', ..rest]`. On `List Char` it costs nothing beyond the
parser. On `Text` it costs the computed binding (about 2 lane hours more
[estimated]), and a `Text` prefix match still converts the whole text to a
list in the runtimes (§7). So: on both types, or on neither; doing `List
Char` only would make `++` mean different things by type.

### 4.3 What it elaborates to

In `pattern_ctor`, a `Pattern::Text(chars, span)` on a column:

- of type `Text`: the constructor `MkText` with one argument, the list
  pattern of `Pattern::Char`s, ending in `Nil` (or the prefix's tail);
- of type `List Char`: that list pattern itself;
- otherwise the error above.

The characters then go the usual way: each `Cons` splits the list, each
character is `MkChar code _`, and the codes of one position become one
`NumCase`. So a match on `"def"`, `"do"`, `"else"` compiles to

```
case t of MkText cs =>
  case cs of
    Nil => default
    Cons c₁ r₁ => case c₁ of MkChar k₁ _ =>
      NumCase k₁ [100 => (case r₁ … 'e' … 'f' …, 'o' …), 101 => (… 'l' 's' 'e' …)] default
```

a character tree (a trie), shared prefixes read once. No kernel change, no
new term, no equality test. The spans of the expanded patterns are recorded
(a `text_patterns: HashMap<Span, …>` beside `char_patterns`) so that
messages and goals can speak in texts.

### 4.4 Coverage

A match on text with only literals can't be exhaustive: there are always
other texts. The tree finds the first gap at one character or at `Nil`,
and today reports that (p3). The message should be at the level the user
wrote:

```
[E-NONEXHAUSTIVE] Error: missing case: no arm of this `match` matches texts other than "def", "do" and "else"
  Note: a `match` on text can't list every text: add `| _ => …` as the last arm
```

with "character lists other than …" on a `List Char`, at most a few
literals listed as `list_numbers` does, and `"--" ++ _` among them for a
prefix. The arm to paste (SW-1027) is `| _ => ?`.

How: when every row in a text column is a text pattern (no variable, `_` or
spelled-out `MkText`), the default is certainly missing, and the compiler
can say so before splitting, as `compile_numbers` does for numbers
(`Arm::other_texts`). In a match on several columns, a missing case whose
text column was split by an expansion prints that column as `_` with the
text message, never as `MkText [MkChar _ _, .._]`. Redundancy needs
nothing: `"def"` after `"de" ++ _` or after `"def"` is `W-REDUNDANT` by the
usual check of the tree [measured for the spelled-out form, p10].

### 4.5 Proofs

What a proof sees is what it sees for the spelled-out pattern today (§2):

- **In a literal arm**, the scrutinee is replaced by the literal: a goal
  `t = "def"` is `"def" = "def"`, closed by `rfl`. The hidden `valid`
  proofs of each character should not be listed in the context: they are
  bound by a `_` the user never wrote. Today they are, one line per
  character (a finding, which applies to `'c'` patterns too).
- **In the catch-all**, the arm equation states the facts:
  `kw.eq3 (t: Text) (notArm1: t ≠ "def") (notArm2: t ≠ "do"): kw t = 0`
  [measured, p8]. For characters, earlier literals on one variable are
  merged into one hypothesis `char ∉ ['k', 'j']` (function-equations.md,
  "Literal patterns"), so a 30-key table is one hypothesis and a program's
  own key list can be passed as it is. Text should get the same:
  `notListed: t ∉ ["def", "do"]`, provable by `decide` for a known `t` and
  passed as is from a program's keyword list (stage 3). Prefix rows add
  `¬ t.startsWith "--"` (stage 3, with D3592).
- **Reasoning by cases.** A proof can write its own `match t with | "def" =>
  … | _ => …`. The arms that name the program's literals compute the
  program; a proof's catch-all computes the program only where the proof's
  tree split the same characters (the `NumCase` apart rule needs the
  proof's numbers to cover the program's: [core.md](../core.md), `NumCase`).
  A proof that lists only some of the program's literals gets stuck leaves
  [measured, p7: `omega` finds no contradiction at the leaf where the second
  character is apart from `'e'` but not from `'o'`]. The robust route is
  the one that works today, `if h: t = "def"` then the arm equation (p12);
  the guide's section on literal matches should say so, with an example.
- **The goal printer** already reads a spelled-out character list back as
  text (`"def" = "def"` above) [measured]. A prefix with an unknown rest
  prints as `MkText ['-', '-', ..r]`; reading it back as `"--" ++ MkText r`
  is a small printer change (stage 2).

### 4.6 Performance

**Many arms.** The tree reads each character once and goes straight to the
arms with that character: for k literals of length up to n, a match costs
at most n character steps (each a `NumCase`, a switch in the runtimes),
not k equality tests. Measured on a 31-keyword table over a million words
(p `big.sw`, one run each, `stitchwort run`): the match takes about 0.2 s
and the `if t == "…"` chain about 0.6 s, beyond the 1.9 s the rest of the
program takes (2.10 s, 2.51 s and 1.94 s in all) [measured]. Lean, Idris
and GHC test in order, so this is a point where Stitchwort's definition of
`Text` pays.

**Checking.** A tree with k literals has up to one default leaf per trie
node and per `Nil`, and each leaf elaborates and checks the catch-all's
right-hand side again (`check_leaf` per `Tree::Leaf`) [source]. With a
small catch-all that is cheap: 50, 100, 200 and 400 random keywords check in
0.71, 0.82, 1.04 and 1.51 s, against 0.24 s for an empty file [measured].
With a large catch-all it isn't: 200 keywords whose catch-all is a sum of
twelve small matches check in 4.34 s, and 1.11 s with the same catch-all
moved into a function [measured]. Characters and numbers have the same
cost today, so the fix is general (stage 4): when one row's right-hand side
lands on many leaves and the goal doesn't depend on the scrutinee, check it
once as a join point (a local function of the arm's variables, applied at
each leaf), as GHC does with join points; Lean elaborates each arm once
anyway, as a function passed to the generated matcher. In a proof, or
when the goal depends on the scrutinee, keep the per-leaf check, which is
what lets each leaf use what it knows.

**Runtimes.** Matching `MkText cs` builds the whole list of characters in
both runtimes before the tree reads the first one (§1). For keywords
(short) that's fine, and it is what the 0.2 s above includes. For a prefix
match on a long text (`"--" ++ rest` on a whole line) it's O(length) per
match. Two fixes, either later and measured first: read characters lazily
(a cursor that conses on demand, as the kernel's range does), or recognise
a text-literal tree under `MkText` whose leaves use only the whole text and
compile it to a switch on the string (JS `switch`, a hash or sorted table in
the Rust runtime). Neither changes the kernel term. The formatter's lexer
works on one `List Char` for the whole file, so it doesn't meet this.

### 4.7 Character lists

Covered above: the same literal on a `List Char` column (D3591), and the
same prefix (D3592). Without D3591, character lists keep
`['d', 'e', 'f']`, which works today.

## 5. What changes, by file [source]

- `crates/syntax/src/parser.rs`: the pattern atom accepts `Tok::Str` (a
  `PatternText` node), refuses `StrStart` with `E-TEXT-PATTERN`; with
  D3592, `++` after a text pattern (a `PatternPrefix` node).
- `crates/syntax/src/lower/patterns.rs`, `ast.rs`: `Pattern::Text(String,
  Span)` (and `Pattern::Prefix(String, Box<Pattern>, Span)`), with
  `span()`, `first_bound` and the exhaustive lists of pattern kinds (14
  places in 10 files list `Pattern::Char` today: `redundant.rs`,
  `autobind.rs`, `module.rs`, `nav.rs`, `equations.rs`, `lib.rs`,
  `tree/spans.rs`, …).
- `crates/elab/src/lib.rs`: `pattern_ctor`'s expansion by type (§4.3), the
  `text_patterns` spans, the text-column missing case (§4.4); with D3592,
  the computed binding for a `Text` prefix's rest.
- `crates/elab/src/missing.rs`: `Arm::other_texts` and the witness printed
  as `_` for an expanded text column.
- Goal display: the hidden `valid` proofs left out.
- `crates/fmt`: the pattern node printed as written (it prints from the
  lossless tree's tokens; a check, not new rules).
- Docs: `docs/guide/` (the pattern chapter, with a keyword table and the
  proof recipe), `docs/syntax.md` (patterns, and "Writing statements" for
  the catch-all's equation), a feature-tour page (`web/guide/`): this is
  one a newcomer enjoys. `docs/core.md` doesn't change.
- Examples: `examples/accept/text-patterns.sw` (keywords, nested, or-pattern,
  `List Char`, a proof by the equation), `examples/reject/` for the missing
  case, interpolation, the wrong type, a suffix.

## 6. Stages

| Stage | What | Gate | Model | Lane hours |
|---|---|---|---|---|
| 1 | Exact text patterns on `Text` and (D3591) `List Char`: parser, lowering, expansion, `E-TEXT-PATTERN`, the text missing-case message, hidden `valid` proofs, docs, guide, tour page, examples | examples pass; `examples/accept/char-patterns.sw` and the missing-case examples unchanged | Opus (syntax and `match`, D2506) | 6–9 |
| 2 | (D3592) Prefixes `"lit" ++ p` on both types, the computed binding on `Text`, the goal printer's `"--" ++ rest` | redundancy against exact literals; a proof that `t = "--" ++ rest` by `rfl` | Opus | 3–5 |
| 3 | The catch-all's equation merges earlier text literals into `t ∉ […]` as for characters (and `¬ t.startsWith` for prefixes) | function-equations examples unchanged; a 30-keyword example proved through one hypothesis | Sonnet | 2–3 |
| 4 | Check a catch-all once, as a join point, where it lands on many leaves of a program (characters, numbers and text alike) | the 200-keyword heavy catch-all from ~4.3 s to ~1.1 s; hashes of definitions without many leaves unchanged | Opus (kernel terms from the match compiler) | 4–6 |
| 5 | Runtimes: lazy characters, or a string switch, for text-literal trees under `MkText` | measured first on the formatter's lexer and a long-line prefix match; only if it shows | Opus to choose, Sonnet to build | 4–6 |

Stage 1 alone unblocks the formatter's keyword table. Stages 3 to 5 are
independent of the syntax questions and each is justified by its own
measurement; 4 is worth doing now for character tables anyway.

## 7. Risks

- **Type-directed meaning.** `"def"` means `MkText …` or a list by the
  scrutinee's type. Where the type isn't known when the match is compiled
  (a lambda's parameter with no annotation, a metavariable), the pattern
  has to wait or default. Number patterns already choose by the column's
  type (`number_kind`, which falls back to the `Nat` reading when the type
  isn't known) [source]; text should fall back to `Text`, the literal's
  expression type.
- **Hashes.** A definition written with `MkText ['d', …]` and one written
  with `"def"` elaborate to the same term and hash alike. Nothing that
  exists changes hash.
- **Large tables in proofs.** A proof that splits a 200-keyword match
  itself gets a goal per trie leaf. The equation route (§4.5) avoids that;
  the guide should steer to it.

## 8. What I did not check

- Whether the formatter (`crates/fmt`) needs a rule for a text token in a
  pattern position, or prints it as is; and the language server's
  hover/navigation on the new node.
- The JS and native runtimes' code for a large character tree (switch
  tables per `NumCase`): only `stitchwort run` was timed.
- Whether a text block (`"""`) in a pattern is worth refusing for
  readability; the design allows it, since it is just a literal.
- Lean 4's current `String` representation: older releases defined it as a
  structure around `List Char`, so `⟨['d', 'e']⟩` patterns were possible;
  whether that still holds wasn't checked.

## 9. Questions for Matt

**D3591: Text literals as patterns, on `Text` and on `List Char`?
[rec: yes, both]**

- *The problem:* matching on words (keywords, commands, instruction names)
  needs an `if` chain or a `Map`: `| "def" => …` is a syntax error today. A
  lexer working on a list of characters writes `['d', 'e', 'f']`.
- *The change:* a text literal is a pattern. On a `Text` it means the text,
  on a `List Char` its characters (chosen by what is matched, as a number
  pattern is on `Nat`, `Int` or `Fin`). Expressions don't change: `"def"`
  is still a `Text`.
- *What it should do:* keyword tables read as tables; they run about 3 times
  faster than the `if` chain [measured]; a missing catch-all says "no arm
  matches texts other than …"; redundancy warnings and the catch-all's
  equation come for free. No kernel change. Stage 1, 6–9 Opus hours
  [estimated]. Saying `Text` only would leave lexers on `['d', 'e', 'f']`.

**D3592: Prefix patterns, `"--" ++ rest`? [rec: yes, on both types]**

- *The problem:* a lexer looks ahead at the next few characters for each
  multi-character token (`->`, `:=`, `..<`, `--|`, about 20 in Stitchwort's
  own lexer [source]) and writes `| ['.', '.', '<', ..rest] =>`. A command
  reader wants "starts with `add `" and uses `stripPrefix` in a guard.
- *The change:* `"..<" ++ rest` matches anything that starts with `..<` and
  binds the rest (a `Text` on a `Text`, a list on a list). Only a fixed
  start: `rest ++ ".sw"` is refused with a note pointing at
  `Text.endsWith`.
- *What it should do:* lookahead arms read like the tokens they match; it
  costs 3–5 Opus hours more [estimated], and on a `Text` it builds the rest
  as a new text, an O(length) conversion in the runtimes until stage 5. If
  no, prefixes stay `['.', '.', '<', ..rest]` on lists and a `stripPrefix`
  guard on text, and the question can come back when the lexer is written.

## Implementation choices made here

- `E-TEXT-PATTERN` for interpolation, a suffix, a middle or a non-literal
  left of `++`; `E-TYPE-MISMATCH` for a text pattern on another type.
- A text pattern with an unknown column type defaults to `Text`.
- The missing-case message lists literals the way `list_numbers` lists
  numbers, and uses "texts" or "character lists".

## Findings worth tickets

- **A literal-heavy match checks its catch-all once per leaf:** 200 text
  keywords spelled out as `MkText [...]` with a catch-all of twelve small
  matches check in 4.34 s, 1.11 s with the catch-all in a function
  [measured]. The same holds for character and number tables. Stage 4.
- **Character-literal arms list the hidden validity proofs in every goal:**
  after `| MkText ['d', 'e', 'f'] => ?`, the context has
  `valid✝²: Std.Char.isScalar 100` and two more, bound by the `_` that
  `'d'` expands to; and they print without their `= True` [measured, p6].
- **The missing-case message for a character list speaks of one
  character:** `match cs with | ['d', 'o'] => … | [] => …` says "no
  alternative matches characters other than 'd'" (p11, function `b`), and
  with a second column the witness is `[MkChar _ _, .._], Zero` (p11,
  function `c`), where `[_, .._], Zero` with "a character other than 'd'"
  is meant.
- **The equation of a literal arm prints as `1 = 1`:** `kc.eq1` for
  `| 'a' => 1` shows type `1 = 1` in a type-mismatch message (p13), and the
  same for a number arm. Either the statement is reduced (then it can't be
  used to rewrite `kc 'a'`) or only the message is; worth a look.
- **`cs == "def"` on a `List Char`:** the type mismatch could note
  `.toList` (or `Text.fromList`), once text patterns make the pattern work
  on lists while the expression doesn't.
- **Runtimes convert a whole text to a list on `MkText cs`:** O(length) for
  a match that reads three characters (`charsOfText`, `TextChars`)
  [source]. Stage 5, measured first.

## Appendix A: the probes

In the lane's scratchpad (not committed), checked with the main checkout's
release binary.

- **p1** `| "def" => 1`: `E-PARSE`, "expected a pattern or `=`, but found
  `"def"`".
- **p2** `MkText ['d', 'e', 'f']`, `MkText ['d', 'o']`, and on `List Char`
  `['d', 'e', 'f']`, `['d', 'o', ..rest]`: checks; four tests pass.
- **p3** the same without a catch-all: "no alternative of this `match`
  matches characters other than 'd'".
- **p4** `'a' | 'b'` on `Char` without a catch-all: "characters other than
  'a' and 'b'".
- **p5/p6** `kw "def" = 1` by `rfl`; a proof's arm `MkText ['d', 'e', 'f']`
  shows goal `"def" = "def"` and three `valid✝` hypotheses; its `_` arm
  shows `MkText [MkChar code✝ valid✝, ..tail✝] = "def"` with `h: 0 = 1`.
- **p7** the proof `| MkText ['d','e','f'] => rfl | _ => omega`: `rfl`
  checks; `omega` fails at `MkText ['d', MkChar code✝ valid✝, ..tail✝]`,
  where the program's second-character case is stuck.
- **p8** `kw.eq3: ∀ (t: Text) => t ≠ "def" → t ≠ "do" → kw t = 0`.
- **p9** `def x: List Char := "ab"`: `E-TYPE-MISMATCH`; `| "${a}b"`:
  `E-PARSE`, "found a text literal".
- **p10** a repeated `MkText ['d', 'e', 'f']`: `W-REDUNDANT`.
- **p11** missing cases on `Text` and `List Char` (findings above).
- **p12** `kw t = 1 → t = "def"` by `if isDef: t = "def"`, `if isDo:` and
  `kw.eq3`: checks.
- **p13** `kc.eq1`, `kn.eq1` print as `1 = 1`.
- **big.sw** 31 keywords as a match and as an `if t == "…"` chain over
  1,000,000 words (`List.replicate 200000` of five words, mapped and
  summed): 2.10 s and 2.51 s; `t => t.toList.length` in their place 1.94 s.
- **bigN.sw** 50/100/200/400 random keywords (2 to 9 of 16 letters), small
  catch-all: `check` 0.71/0.82/1.04/1.51 s; an empty file 0.24 s.
- **heavy.sw** 200 keywords, catch-all a sum of twelve small matches: 4.34
  s; the catch-all in its own function: 1.11 s.
