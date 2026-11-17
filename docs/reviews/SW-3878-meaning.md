# SW-3878: review of the self-hosted formatter's `meaning`

Opus, 17 November 2026. Paper review of `tools/fmt/src/Fmt/Meaning.sw` and
`MeaningProofs.sw` (SW-3864, D3678's narrow form), against the compiler's
lowering (`crates/syntax/src/lower/`), the elaborator where the lowering
hands a choice on (`crates/elab/src/check.rs`), and the parser. Probes ran
the main checkout's release `stitchwort` (built 18:21 today) and the Twin
executable `target/fmt-twin/fmt` (18:27); the repro files are inline below.

**Verdict.** Two of `meaning`'s five rules are unsound: each has a pair of
files that `meaning` calls the same program and that `check` accepts one of
and rejects the other. In both the self-hosted passes make the change, and
in one the shipping Rust `stitchwort fmt` makes it too, so it is a live
formatter bug as well as a hole in the trusted definition. The other three
rules (commas, `∀`, binder-type brackets) hold. Nothing over-kept blocks a
true step fact. Leaving comments out is safe for `check` and `run`, but
docs need a line in `tidyKeepsComments`.

## Must fix

### M1. Splitting a group: the elaborator reads a group's type once, shared by its names

`meaning` splits `(a b: T)` into `(a: T) (b: T)` when `T` names neither
name. Its doc cites the Rust tree check's `one_binder_per_name` for this,
but that is the formatter's own assumption, not the compiler's reading. The
lowering keeps a group as one `Expr::Pi { names, dom }`
(`lower/binding.rs:183-194` for `∀`, `lower/header.rs:62` for a header),
and `infer_pi` (`elab/src/check.rs:2896-2903`) checks `dom` **once** and
binds every name to that one result, shifted. Any metavariable made while
checking `T` is then shared by all the names; split, each name gets its
own. That is visible in two ways:

- a hole, `_` (or `?`), written in the type;
- an implicit argument the elaborator inserts, which nothing in the text
  shows.

Repro, a `∀` (`p2/`):

```
def p: Prop := ∀ (x y: _) => x + 1 = 2 ∧ y = True        -- E-INSTANCE-NONE: no `Add` instance for `Bool`
def p: Prop := ∀ (x: _) (y: _) => x + 1 = 2 ∧ y = True   -- checked
```

A theorem's header (`p3/`):

```
theorem t ∀ (x y: _) (hx: x = 1) (hy: y = True): x = 1 := hx        -- E-TYPE-MISMATCH
theorem t ∀ (x: _) (y: _) (hx: x = 1) (hy: y = True): x = 1 := hx   -- checked
```

An implicit argument, no `_` written (`p4/`):

```
def Box [t: Type]: Type := List t

def p: Prop := ∀ (a b: Box) => a = [1] ∧ b = [True]        -- E-TYPE-MISMATCH
def p: Prop := ∀ (a: Box) (b: Box) => a = [1] ∧ b = [True]  -- checked
```

`meaning` equates each pair (`Group.splits`: bare, no `auto`, default or
attributes, and `_` or `Box` names neither name). **`stitchwort fmt` today
rewrites all three checking files into the failing ones** (P4 merges
`(x: _) (y: _)` and `(a: Box) (b: Box)`), and the Twin's P4 does the same.
Lambdas are not affected: `let h := (x y: _) => if y then x else 0` checks
either way, so the lambda's lowering or checking already goes one name at a
time. No `.sw` file in `aoc/`, `games/`, `tools/` or std has a group with
`_` as its type, so nothing in the repo is broken today [grep].

The implicit-argument case means no syntactic test (in `meaning` or in P4)
can close this: whether `T` leaves a metavariable is only known after
elaborating it. So the fix is a choice for Matt:

- **(a) The compiler reads `(a b: T)` as `(a: T) (b: T)`** (lower each name
  to its own binder with a copy of `T`, or check `dom` once per name in
  `infer_pi`). Then `meaning`, P4 and the Rust tree check are right as
  written, and the doc can cite the lowering. This changes the language: a
  shared `_` would no longer force the names to one type. Recommended: it
  is what every formatter piece already assumes, and "one group is
  shorthand for one binder a name" is the reading a newcomer expects from
  the merge.
- **(b) P4 stops merging, and `meaning` stops splitting,** for binders of
  `∀` and headers (the two places `infer_pi` shares). That gives up the
  house style's merge for `def` and `theorem` headers.

Until it is decided, P4 (Rust and Twin) should at least not merge a type
with `_` or `?` in it, which covers the written-hole case; the
implicit-argument case stays open. This needs a ticket for the Rust
formatter as a bug in its own right.

### M2. A pair at an application's head around a constructor update is read

`forgetLeft` forgets a pair at an application's head when what it holds is
`atomic`, on the claim that no atomic form reads as an application. The
lowering's test is not "the head is a `Paren` around an application" but
"the head's **first token** is `(` and the head **lowers to** `Expr::App`"
(`lower/exprs.rs:325-341`). `CtorFields` is in `atomic`, but a constructor
*update*, `C { r | x = e }`, lowers to `App(C, { r | x = e })`
(`ctor_fields`, `exprs.rs:308-310`, `Argument::Two` → `into_expr`). So
`(C { r | x = 1 }) b` is `App(Bracketed(App(C, …)), b)` and
`C { r | x = 1 } b` is `App(App(C, …), b)`, and the elaborator reads the
bracket: it finishes the call before applying it (`finished_call`,
`check.rs:2405-2421`, signature defaults §6.3).

Repro (`p1/`):

```
type R = { x: Nat }

def Pick (r: R) (k: Nat := 5): Nat → Type := j => Nat

def r0: R := { x = 0 }

def v: {IO} (Pick { r0 | x = 1 }) 2 := 3
```

checks; with `Pick { r0 | x = 1 } 2` it is `E-DEFAULT-POSITIONAL` ("this
argument comes after all of `Pick`'s parameters"). The two parse to the
same tree but for the `Paren` (`stitchwort dev passes`), and `meaning`
forgets it, so it calls them the same program. **The Twin's P3 drops the
pair** (its `--stage passes` P3 tree has no `Paren`; Rust's keeps it), and
`fmt --stage meaning p1/a.sw` answers `kept`: the proved step fact
`dropLeftForgotten` covers exactly this wrong drop. The Rust formatter is
fine (it asks the parser and its tree check sees `Bracketed`).

Fix, in both places:

- `meaning`: `Expr.atomic` of `CtorFields` is true only without a base
  (`CtorFields _ (Record _ None _ _ _)`); fix the doc's "three places" to say
  the lowering tests the head's first token and its lowered form.
- P3: `Expr.level` of a `CtorFields` with a base is that of `App` (20), so
  `dropLeft` keeps the pair under an application's head. `levelAtomic`
  then still holds.

Add both repros as `differentMeaning` tests, and the `p1/` file to the
Twin's golden inputs.

I checked the other atomic forms against the lowering: `Atom`, `Unit`,
`Universe`, `Include`, `Tuple`, `ListOf`, `Record` (with or without a
base), `Spread`, `RecordField`, `NamedArg`, `Annotation` (`Expr::Ann`),
`Interpolated` (`Expr::Interpolated`), `OperatorSection` (a lambda, and its
own first token is `(` anyway), `FieldAccess (Some _)` (`Expr::Field`; a
receiverless chain `.f.g` is wrapped in `Section`, which isn't atomic) and
`Paren` (nested: the inner pair is judged on its own). None lowers to
`App`. `Prefix` `!x` does (`App(Std.Bool.not, x)`) but isn't atomic.

## Should fix

### S1. `tidyKeepsComments` must carry docs, including a blank line the tree doesn't keep

Comments reach `check` and `run` in one way only: every `--|` comment's
doc links are resolved and an unresolved one is `W-DOC-LINK`
(`lower.rs:217`, `syntax/src/docs.rs:105-115`, `elab/src/doc_links.rs`).
That reads every `--|` in the file wherever it sits. No comment is a
pragma or attribute (the only code that reads a comment's text is
`docs.rs:358`, plus the LSP and `fixes.rs`, which only skip comments). A
`--` inside a text is part of the literal (`lexer.rs:303`), so it is the
`Word`'s text, which `meaning` keeps. So leaving comments out of `meaning`
loses nothing `check` or `run` reads, given the texts of `--|` comments are
kept.

Docs are read by search, hover, the index and `stitchwort doc`: a
declaration's or member's doc is the run of own-line comments directly
above its first token, with no blank line between them and the token
(`docs.rs:327-337`, `attached`). The tree's `Word` keeps each comment's
`blankBefore` but not whether a blank line separates the **last** comment
from its token (`Syntax/Expr.sw:21-35`), so `--| x` then a blank line then
`def f` and `--| x` directly above `def f` are the same tree, and only one
has a doc. (Both formatters keep the difference today [run], so something
below the tree carries it.) `tidyKeepsComments` should state:

1. the file's comments, in order, are the same: each one's text, whether
   it is own-line or trailing, and whether a blank line is above it;
2. each comment is on the same token, except one held by a comma that P2
   deletes, which moves to a token next to that comma (K1); and
3. whether a blank line separates the last own-line comment above a token
   from the token is kept for every declaration's and member's first token.

(1) keeps `W-DOC-LINK`'s input; (2) and (3) keep every doc's attachment,
since a deleted comma is before a closer and a closer is never a
declaration's or member's first token. If the tree can't state (3), it
belongs to the printer's theorem on the leaves instead, but it has to be
somewhere for the top theorem to promise docs.

### S2. Once comments are out, take every comment test out of `meaning`

With comments forgotten, the tests on them are trust surface with no job:
`open.bare && close.bare` in `unwrapped` and `forgetLeft`, `group.bare` in
`splits`, the stored `Group.bare` field itself, and `open = noComments` in
`pieces`. Worse, if `meaning` drops comments but keeps `Group.bare` (a
function of a group's comments), it still depends on comments through the
back door. Forget all of them: blank every `Comments` and `Group.bare` in
one step, and drop the `bare` conditions. `meaning` then forgets a pair
holding a comment that P3 keeps; that is fine (the compiler doesn't read
comments, and a step fact only needs `meaning` to forget at least what the
pass changes).

### S3. Correct the doc's grounds

- The splitting bullet cites `one_binder_per_name`; after M1 it should cite
  the lowering or elaborator line that makes the split true.
- "The compiler reads a pair in three places only": the first is a test on
  the head's first token and lowered form (M2), not on a `Paren` node.
- Say once, at the top, what "the same program" leaves out on purpose:
  spans (every position moves under formatting; `NegForm` Operand/Argument,
  which only messages read, `ast.rs:1345-1355`), and docs (S1).

### S4. An oracle that isn't `meaning` itself

`Twin --stage meaning` compares a file's `meaning` with its tidied file's,
so it can only find a pass that disagrees with `meaning`, never a `meaning`
that disagrees with the compiler: it answered `kept` on M2's file. Both
holes above were found by `check`ing the two sides. Add a cheap
differential: for each file whose tidied form `meaning` keeps, `check` both
sides and compare declaration hashes (D3635's cross-check), with inputs
seeded by generators for the two shapes found here: groups whose type is
`_` or a name with implicit parameters, and a constructor update at an
application's head.

## Fine

- **Trailing commas (P2).** All ten flags the tree keeps (`Tuple`,
  `ListOf`, `Record`, the four pattern forms, `Fields`, `Attributes`,
  `RuleSet`) are cleared; the lowering takes items only (`items(…)` in
  `exprs.rs`, `patterns.rs:95-96`). `[(0 ..< 3),]` and `[(0 ..< 3)]` both
  keep `Bracketed` since SW-3229 [run]. `(p,)` and `(a,)` are parse errors,
  so no one-item tuple loses its comma.
- **`∀` (P1).** The parser and the lowering skip it outright
  (`parser/declarations.rs:289-307`, `lower/definitions.rs:203`, D3472:
  "the term and hash are those of the header without it").
- **Negative numerals.** A pair right around one is never forgotten. A
  forgotten pair can change the token before a deeper `-` (`{IO} (-1 + x)`
  against `{IO} -1 + x`), but that only switches `NegForm` between
  `Operand` and `Argument` (or `prefix_op`'s `Operand`), which only
  messages read (`numbers.rs:915-942`, `check.rs:5104`).
- **`(f a) b`.** Kept (`App` isn't atomic). `((f a)) b` forgets only the
  outer pair, and both forms keep a first token `(`, so both are
  `Bracketed`.
- **A type that names its group's names.** `namesItself` reads every
  token's text in the type's dump, so it can say "names" wrongly, never
  "doesn't": the merged form checks `T` before binding any name
  (`infer_pi` checks `dom` before `bind`), the split form checks the second
  copy with the first name bound, and the two differ only if `T` mentions
  it. (M1 is a different difference.)
- **`instance` headers and `∃`.** Kept whole, as P4 leaves them;
  `∃ (a b: _)` would share like `∀`, so keeping it whole is right.
- **Attributes, defaults, `auto` in groups.** Groups with any of them are
  kept whole. Their types are still unwrapped, which the compiler doesn't
  see (a binder's type is never an application's head or a list's item).
- **Sections.** `(.f)` is a `Section`, not atomic, so `{IO} (.f) x` keeps
  its pair; where a pair around a section is forgotten (`{IO} (.f) + 1`)
  the bare text parses to a different tree (`Section(Binary …)`, [run]),
  so no two files collide there.
- **Coverage of the 98 kinds.** Every place the four passes change maps to
  a `meaning` rule that forgets at least that much: P2's five steps to the
  same five flags; P1 to `plainForall`; P3's row step to `forgetLeft`
  (proved, `dropLeftForgotten`); P3's `dropDeclBinders`, which reaches
  function-type binders, `∀`/lambda params, annotations and header groups
  down the spine, to `unwrapped`, which `meaning` applies at every such
  node anywhere (a superset); P4's header and binding steps to
  `splitGroups`/`splitParams`, on the same kinds (`def`/`theorem`, `∀`,
  lambda). I found no node a pass changes that `meaning` passes through
  unchanged.
- **Over-kept.** Nothing blocks a true step fact. P4's fact,
  `splitGroups (mergeGroups gs) = splitGroups gs`, needs each merged
  group's later pieces (current's `colon`, `close` and `annotation`) to
  equal the unmerged groups' own; `joins` gives the same `implicit`, empty
  attributes and comments, and equal `typeLines`, so it rests only on the
  dump telling comment-free types apart, as NOTES says. The one over-keep
  that does bite is comments under K1, which the orchestrator's call
  removes.

## Simplifications (question 5)

The trusted base is small (about 120 lines of code) and reads well; the
two holes are in the grounds, not in the code's size. After the fixes:

1. **Forget `∀` everywhere** (`forallKeyword = None` for every header),
   justified by one parser line, instead of mirroring P1's condition. The
   step fact becomes trivial and nothing about P1 needs reviewing again.
2. **No comment tests at all** (S2): about ten conditions and the
   `noComments` constant go.
3. **Keep `atomic` an allow-list** (fixed per M2) rather than a deny-list
   of what lowers to `App`: a forgotten new form fails safe.
4. **Under M1(a), keep the split rule as it is** (its `namesItself` test is
   still needed for scoping), and its doc can point at the lowering.

## Repro files

Written in the lane's scratchpad (`sw3878/p1` … `p5`); all are inline
above. To rerun: `stitchwort check FILE`, `stitchwort fmt - < FILE`,
`stitchwort dev passes FILE`, and the Twin's
`fmt --stage passes|meaning FILE`.
