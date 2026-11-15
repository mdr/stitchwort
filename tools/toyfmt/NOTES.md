# The toy formatter: notes

`toyfmt` formats Sprig, a small language made up to rehearse the parts of
the self-hosted Stitchwort formatter (docs/proposals/toy-formatter.md).
This file keeps the friction met while writing it, and the timings, stage
by stage. Compiler built from `main` at e2b1cb075, 15 November 2026.

## What is here

| Namespace | Files | What |
|---|---|---|
| `Toy.Doc` | `Doc/Doc.sw`, `Doc/Print.sw` | The layout engine, a port of the core of `crates/fmt/src/printer/engine.rs` |
| `Toy.Doc.Tests` | `Doc/Tests/Engine.sw` | Six of the Rust engine's eight tests (not `Verbatim`, `LineStart`) |
| `Toy.Syntax` | `Syntax/Tree.sw`, `Syntax/Dump.sw` | Sprig's tree, which the parser makes and the rules read; a dump for tests |
| `Toy.Fmt` | `Fmt/Rules.sw` | The printing rules P1 to P10 |
| `Toy.Fmt.Tests` | `Fmt/Tests/*.sw` | Twelve goldens, the disturber and its tests |
| `Toy.Timing` | `Timing/Timing.sw` | A generated file printed, to time the printer |

Stage A adds the lexer and parser in `Toy.Syntax`, making `SourceFile` as
`Syntax/Tree.sw`'s comment says; stage C the `{Files}` driver and `main`.

## Stage B (SW-3341): the engine, the rules, the goldens, the disturber

### Timings

Printing a generated file (`Toy.Timing.main`: tree built, laid out, printed,
counted), Speedwell, load about 5, one run each [measured]:

| Output | `stitchwort run` | native (`build --native`) | Peak memory, native |
|---|---|---|---|
| 104 KB | 0.53 s (0.18 s after the 0.35 s start) | 0.22 s | 34 MB |
| 1.08 MB | 2.12 s (1.77 s after the start) | 0.36 s | 319 MB |

So the printer is linear, about 1.7 s/MB on the machine and 0.3 s/MB
native: printing is not where the real formatter's 20 seconds go. The
whole-format timing (lex, parse, print) waits for stage A's parser.

### Friction

1. **The tree has no `==`.** A syntax tree's types always refer to each
   other (an expression holds blocks, which hold statements, which hold
   expressions), and `==` isn't derived for types defined together:
   `E-INSTANCE-NONE ... its field declarations has type List (Spaced
   Declaration), which has no DecEq instance`. Stage A's test `parse source
   == tree` and stage D's validation (`format` checks that the output parses
   to the same erased tree) both need it. `Syntax/Dump.sw` writes the tree
   as text, and tests compare dumps; a proof needs a real decision, so the
   real formatter, with 94 node kinds, will want derived `DecEq` for
   mutually recursive types (or a hand-written one per kind).
2. **Recursion through a list in the tree needs a helper per list.**
   `arguments.map (item => item.value.layout)` inside the rules' mutual
   group is refused (`E-TERMINATION`, first for passing `Declaration.layout`
   unapplied, then for the call through `map`). The documented way round is
   a helper for each container, defined with the functions and taking the
   list apart by patterns (`itemDocs`, `statementLines`, `dumpItems`). A
   helper that returns parts (`Body.single: Body → Option (Expr, …)`) doesn't
   work either: what it returns isn't known to be smaller, so four rules
   match the body's shape inline instead. The real formatter's 94 kinds will
   repeat this everywhere; recursion through `List.map` on a field of the
   scrutinee (nested fixpoints, as Coq has) would remove it.
3. **A constructor can't share its name with a type its fields use.** The
   Rust engine's `Doc::Text(String, usize)` ported as `| Text (text: Text)`
   is an error: "a data type's fields can mention the type itself, but not
   its constructors". Renamed `Chunk`.
4. **Constructors of different types collide even where the type is
   known** (toy-formatter.md §6 item 3, SW-510): a `Line` in `Doc` and one in
   a token type make `| Line =>` in a `match` on a `Doc` `E-AMBIGUOUS`. So
   names were chosen to stay apart: `Doc.Flatten` (Rust's `Flat`) beside the
   printer's `Mode.Flat`; the tree's `Var`, `NumberLiteral`, `StringLiteral`
   so that stage A's token kinds can be `Name`, `Number`, `Str`; the
   disturber's `WordPiece`, `SymbolRun`.
5. **No `List.intersperse`.** `Text.joinWith` exists, but nothing puts a
   separator between the items of a general list: written twice
   (`Doc.joinLines`, `Doc.joinedWith`).
6. **A tuple accumulator needs its type written.** `text.lines.foldLeft
   ([], None, 0) (...)` is `E-UNSOLVED` at `[]` until annotated `(([], None,
   0): (List Chunk, Option Chunk, Nat))`, though the step function's use says
   it.
7. **The formatter moves a record literal holding text blocks below `:=`**
   and re-indents all of it (`def groups: Golden :=` then `{` on the next
   line), where the same literal without text blocks opens on the `:=` line
   (games/rogue's `quiet`). The goldens all have that shape.
8. **No clock.** `IO` can't tell the time, so the toy's per-phase timings
   (lex, parse, print) can only be taken from outside, one `main` per phase.
9. **Small:** `W-RECEIVER-NOT-FIRST` moved Rust's `Doc::nest(indent, doc)`
   and a `joinWith (docs) (separator)` out of `Doc`'s namespace, since their
   first parameter isn't a `Doc`.

What went well: the engine, ported almost line for line, passed all its
tests on the first run, and a failing golden's report (the two texts line by
line, with the first difference's line and column) found both wrong
expectations at once.

### What the disturber does

A sample, from the comments golden with seed 5:

```text
-- Totals for one order.
fn   total(order)= 
    -- the base price
    let base= sum( order.items) -- before tax
    base+  tax(base)
let weights  =  [


      -- light
      1 ,
        2 , -- two
      3]
fn odd(x) = -- why
  x  %  2
```

The last declaration is left alone: its comment is where no rule places
one, so formatting keeps it as written.
