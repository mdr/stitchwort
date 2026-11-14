# Naming the character case of a generic parser

**Status:** survey note, 14 November 2026 (SW-3277, for D3588). Paper lane:
nothing is built. Claims are marked **[source]** (read in the library's
docs or source today), **[measured]** (a throwaway probe run with the main
checkout's release binary at `90b62debe`) or **[estimated]** (my
reasoning).

## In plain words

**The problem.** [generic-parse.md](generic-parse.md) gives the `Parse`
ability a parameter for what it reads, so today's `{Parse}` becomes
`{Parse Char}` in 71 `aoc/` files (142 rows, every one of them `{Parse}`
alone) and in the guide. D3588 asks whether to write that out or keep a
short name for characters. Matt asked what other parser libraries do.

**What they do.** Of the fourteen libraries looked at, nine are generic in
what they read. None of them defaults the input type. They make the common
case pleasant in one of three ways: a short name the library provides, one
per input, in its own module (Parsec, attoparsec, Lean); a short name the
tutorial tells you to write yourself (Megaparsec, FParsec); or no name at
all, because the input type is written anyway as the parser function's
argument (nom, winnow, chumsky). Defaults do appear, but only for the
*error* type (nom, winnow, chumsky). The one effect-based parser with a
name for a set of effects, Effekt's, uses it exactly as D3596 proposes:
`effect Parser = { Nondet, Lexer }`.

**The recommendation.** Write `{Parse Char}`, as D3588 recommended, and
don't add a std name for it. The library aliases exist to shorten a long
type (`Parsec Void Text`, `ParsecT e s m`); `{Parse Char}` is already as
short as any of them, and a std alias would give every character parser
two spellings while the checker's messages show only one. Once set names
exist (SW-3267), they are for programs whose parsers perform more than
`Parse`, which is where Effekt uses one: `ability Grammar = {Parse Token,
Fail}`. Two small messages are worth fixing whatever the answer
([Findings](#findings-worth-tickets)).

## 1. The survey

### 1.1 Summary

| Library | Generic in input? | How the character case is spelled | Defaults? |
|---|---|---|---|
| Parsec (Haskell) | yes, `ParsecT s u m a` | library alias per input module: `Text.Parsec.String.Parser`, `Text.Parsec.Text.Parser` | no |
| Megaparsec | yes, `Parsec e s a` | convention: the tutorial's first step is `type Parser = Parsec Void Text` | no |
| attoparsec | yes internally, `Parser i a` | separate modules, each exporting `Parser`: `Data.Attoparsec.Text`, `.ByteString` | no |
| nom 8 (Rust) | yes, any `I` | the input is the argument: `fn p(i: &str) -> IResult<&str, Foo>` | error only: `E = Error<I>` |
| winnow 1.0 | yes | the input is the argument: `fn p(i: &mut &str) -> Result<Foo>` | error only |
| chumsky | yes, `Parser<'src, I, O, E>` | written out: `impl Parser<'src, &'src str, Foo>` | error only: `E = extra::Default` |
| combine | yes | written out as a bound: `where Input: Stream<Token = char>` | no |
| FParsec (F#) | no, `CharStream` only | convention: `type Parser<'t> = Parser<'t, UserState>` (fixes the user state, not the input) | no |
| Scala parser combinators | yes, abstract `type Elem` | fixed by the trait you extend: `RegexParsers` sets `type Elem = Char`, so `Parser[Int]` inside it means characters | no |
| Angstrom (OCaml) | no, string/bigstring | `int t` | no |
| Lean 4 `Std.Internal.Parsec` | yes, `Parsec ι α` | library alias per namespace: `Parsec.String.Parser`, `Parsec.ByteArray.Parser` | no |
| Koka `std/text/parse` | no, `sslice` | `pnat(): parse int` | no |
| Effekt (case study) | tokens only | a set name: `effect Parser = { Nondet, Lexer }`, then `parseNum(): Tree / Parser` | no |
| parseff (OCaml 5 effects) | strings in every example | `unit -> int` | no |

Unison has no maintained parser library I could find (one community
project, last pushed 2019); Eff has none.

### 1.2 The code users write [source]

**Parsec** provides the alias:

```haskell
-- Text.Parsec.String
type Parser = Parsec String ()
type GenParser tok st = Parsec [tok] st

number :: Parser Int
```

**Megaparsec** doesn't, and its tutorial makes writing one the first step:
"the best way to start writing a parser with megaparsec is to define a
custom type synonym for your parser", `type Parser = Parsec Void Text`.
The character combinators live in `Text.Megaparsec.Char` with the
constraint `Token s ~ Char` (and bytes in `Text.Megaparsec.Byte`). The
tutorial names the friction: without signatures "things like `e` will
often be ambiguous", "the flip side of the polymorphic API", and in GHCi
"the `:: Parser Char` annotation is necessary because `satisfy` by itself
is polymorphic".

**attoparsec** gives each input its own module whose `Parser` is the
internal generic one fixed: `type Parser = Parser Text` in
`Data.Attoparsec.Text`.

**nom, winnow** never name the input separately, because a parser is a
function of its input:

```rust
fn point(input: &str) -> IResult<&str, Point> { … }          // nom 8
fn point(input: &mut &str) -> winnow::Result<Point> { … }     // winnow 1.0
```

nom's `pub type IResult<I, O, E = Error<I>>` defaults only the error.

**chumsky** writes the input out in every signature and defaults the
error: `pub trait Parser<'src, I: Input<'src>, O, E: ParserExtra<'src, I> =
Default>`; its examples read `fn palindrome_parser<'src>() -> impl
Parser<'src, &'src str, String>`.

**combine** repeats the bound in every signature (`fn expr_<Input>() ->
impl Parser<Input, Output = Expr> where Input: Stream<Token = char>`); its
`parser!` macro exists to avoid naming large parser types, not to shorten
the bound.

**FParsec** is characters only (`type Parser<'TResult, 'TUserState> =
CharStream<'TUserState> -> Reply<'TResult>`); its tutorial's alias fixes
the *user state* because of F#'s value restriction (`let p = pstring
"test"` doesn't compile without it).

**Scala**: the element type is an abstract type member, fixed by the trait
an object extends: `trait RegexParsers extends Parsers { type Elem = Char
… }`. Inside `object Calc extends RegexParsers`, `Parser[Int]` means a
character parser. It is the module approach, done with mixins.

**Lean 4** made `Parsec` generic (`def Parsec (ι : Type) (α : Type) : Type
:= ι → Parsec.ParseResult α ι`, with an `Input ι elem idx` class) and
provides one alias per input, each in its own namespace:

```lean
namespace Std.Internal.Parsec.String
abbrev Parser (α : Type) : Type := Parsec (Sigma String.Pos) α
def pchar (c : Char) : Parser Char := …

namespace Std.Internal.Parsec.ByteArray
abbrev Parser (α : Type) : Type := Parsec ByteArray.Iterator α
```

**Koka**'s parser is an effect over string slices, characters only:
`pub fun pnat() : parse int`, with `pub alias parser<e,a> = () ->
<parse|e> a` naming the *function type*, not the effect.

**Effekt**'s frontend case study is the nearest design to Stitchwort's: a
parser is a function performing effects, and a name is given to the set:

```
interface Nondet { def alt(): Bool  def fail(msg: String): Nothing }
interface Lexer  { def peek(): Option[Token]  def next(): Token }
effect Parser = { Nondet, Lexer }

def parseNum(): Tree / Parser = …
```

The name bundles two different effects; it doesn't rename one effect at
one argument.

### 1.3 What the survey says

- **Nobody defaults the input.** Rust libraries default the error type,
  which is incidental to most users; the input, which decides which
  combinators apply, is always stated or fixed by a module. That agrees
  with Matt's instinct, and there's nothing here to argue against it.
- **Aliases exist to shorten long types,** and they are named `Parser`
  because they name a type: `Parsec Void Text`, `Parsec String ()`,
  `Parsec (Sigma String.Pos)`. The documented reasons are length,
  ambiguity when signatures are missing (Megaparsec, FParsec's value
  restriction) and, for Megaparsec, optimisation from fixing every type
  variable.
- **Neither reason applies here.** `{Parse Char}` is two words, the same
  as `Parser Char` in Megaparsec, and a definition here always has a
  signature (`def p() := …` is a parse error [measured]), from whose row
  the parameter is found (generic-parse.md §1.3 [measured there]). The
  ambiguity Megaparsec warns about comes up only in statements with no
  parser in them, three of std's own lemmas (generic-parse.md §1.3), never
  in user code.
- **Separate modules** are how Haskell and Lean give each input its own
  `Parser`. Stitchwort has no type-level alias for a row member to put in
  such a module (`type Chars = Parse Char` is `E-ABILITY`,
  generic-parse.md), and generic-parse.md already keeps one `Parse.`
  namespace with the character layer in its own file, which is the
  module split without a second name.

## 2. For Stitchwort

### 2.1 The options

**A. Write `{Parse Char}`.** One spelling in code, guide, hover, messages
and lemma statements (`Parse.Reads (parser: () → {Parse Char} a)`), and it
sits beside `{Parse Token}` and `{State s}` the same way. Cost: five
characters per signature, 142 rows changed by one substitution
(generic-parse.md stage 1). It needs nothing new.

**B. A std set name, after SW-3267.** The best name would be
`ability Parse.Text = {Parse Char}` or `ability Chars = {Parse Char}`,
giving `def seat(): {Chars} Seat`. Against it:

- *Two spellings, one shown.* Set names are replaced where a row is read,
  so the checker's types, hovers and messages show `{Parse Char}`
  (ability-granularity.md §4.1; folding a printed row back to a name in
  scope is a possible nicety, not designed). A newcomer would write
  `{Chars}`, read `{Parse Char}` in every message, and need the guide to
  explain why. The std docs and the lemmas would say `{Parse Char}` too,
  since their statements are generic or written against the ability.
- *It saves one word,* where the library aliases surveyed save two to
  four.
- *Errors get a layer.* A mismatch between `{Chars}` and `{Parse Token}`
  would be reported as `Parse` used with `Char` and `Token`
  ([measured] on a stand-in ability: "`Reads` is used with different
  arguments: `Char` and `Nat`"), naming nothing the user wrote.
- For it: AoC signatures stay as short as today, and the generic ability
  could be thought of separately. With set names built, it costs one std
  line.

**C. Separate modules.** A `Parse.Text` namespace re-exporting the
character layer under its own names (Lean's and attoparsec's shape). It
needs either the set name of B or a second ability, and generic-parse.md's
single namespace already gives the split by file. No gain over A.

**D. A default parameter** (`ability Parse (t: Type := Char)`). Ruled out
by Matt; the survey agrees (no library defaults the input), and it would
make `{Parse}` mean characters in a row while `Parse.many` is generic,
which is exactly the confusion the parameter removes.

**E. User-written set names, after SW-3267.** Megaparsec's and FParsec's
convention, in Effekt's shape: a program names its own bundle when its
parsers perform more than `Parse`:

```
ability Grammar = {Parse Token, Fail}
def expression(): {Grammar} Expr := …
```

That needs no std decision and is what set names are for
(ability-granularity.md §4.2, "Applications"). The guide's set-names
chapter can use a parser as its second example.

### 2.2 Recommendation

**A now, E when set names exist, not B.** Write `{Parse Char}` in the
generic-parse sweep; leave std without a character alias; let the
set-names lane (SW-3267) use a parser bundle as a guide example.

What depends on SW-3267: only B and E. Before it, A can be done in full,
and the two message fixes below help it straight away (a programmer who
writes `{Parse}` from habit gets told what to write). If Matt later wants
B, it is one std line and a substitution back, which D2303 says not to
count.

## Findings worth tickets

1. **`{Parse}` after the change gives an unhelpful arity error.** On a
   stand-in `ability Reads (t: Type)`, writing `{Reads}` gives "[E-ARITY]
   `Reads` takes 1 argument(s)" with the whole row underlined [measured].
   Once `Parse` takes `t`, every `{Parse}` written from habit or an old
   example hits this. For an ability in a row the message should name the
   parameter and show the form, e.g. "`Parse` needs what it reads: write
   `{Parse t}`, such as `{Parse Char}`"; and "argument(s)" should be
   singular or plural. Small; best before or with generic-parse stage 1.
2. **The "add it to the function's type" note drops the argument.**
   Calling a `{Reads Char}` function from a `{Fail}` one says "add `Reads`
   to the function's type (`-> {Reads …} …`)" [measured]; it knows the
   argument, and should say `{Reads Char}`. Also small, same timing.

## Sources

Parsec `Text.Parsec.String`, attoparsec `Data.Attoparsec.Text`
(hackage.haskell.org); Megaparsec tutorial (markkarpov.com/tutorial/
megaparsec.html); nom 8.0.0 `IResult`, winnow 1.0.5 tutorial chapter 1,
chumsky `Parser` trait, combine crate docs (docs.rs); FParsec tutorial and
reference (quanttec.com/fparsec); scala-parser-combinators
`RegexParsers.scala` (GitHub); Angstrom `angstrom.mli` (GitHub); Lean 4
`src/Std/Internal/Parsec/{Basic,String,ByteArray}.lean` (GitHub,
master); Koka `lib/std/text/parse.kk` (GitHub, dev); Effekt
"Compiler Frontend Phases" case study (effekt-lang.org/docs/casestudies/
frontend); parseff 0.3.0 (ocaml.org); zenhack/unison-parsers (GitHub).
Probes: `probe2.sw`, `probe3.sw` in the lane's scratchpad (a stand-in
`ability Reads (t: Type)`, since no std ability takes a parameter yet).

## Question for Matt

**D3603: write `{Parse Char}` everywhere, with no std short name for it?**
(Replaces D3588, which asked the first half.)
*The problem:* once `Parse` says what it reads, every character parser's
signature grows from `{Parse}` to `{Parse Char}`, in 71 AoC files and the
guide.
*The change:* write it out in the generic-parse sweep, and don't add a std
name such as `ability Chars = {Parse Char}` when ability-set names
(SW-3267) arrive; programs can still name their own bundles, like
`ability Grammar = {Parse Token, Fail}`.
*What it should do:* one spelling everywhere, the same one the checker
prints in hovers and messages; five more characters per signature. Of the
fourteen parser libraries surveyed, none defaults the input type; the ones
that offer a short name do so to shorten types of three or four words,
where ours is two. **[rec: yes]**
