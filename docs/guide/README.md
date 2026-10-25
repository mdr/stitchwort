# The Stitchwort guide

Stitchwort is a functional language with dependent types. Its programs are total: every function finishes unless its type says otherwise. You can state facts about your programs as theorems, and the compiler checks the proofs. Side effects are described in types as abilities. Programs run on a fast native runtime, and exported functions compile to JavaScript modules with TypeScript declarations.

This guide is for programmers who know a language like Scala or TypeScript. It doesn't assume you know type theory. It sits between two other documents:

- the playground's **feature tour** (the Guide tab in the playground, `web/guide/`), a page per feature with a runnable example;
- the **reference**: [syntax.md](../syntax.md) (the surface language, in detail), [core.md](../core.md) (the core language and kernel), [projects.md](../projects.md), [testing.md](../testing.md), and the design notes in [proposals/](../proposals/).

The guide explains how things work and why, shows the idioms, and shows what the compiler says when something is wrong and how to read it. Where it says less than the reference, it links to it.

## Chapters

1. [Getting started](01-getting-started.md): installing, the `stitchwort` command, projects, the playground and editor support.
2. [Values and definitions](02-values-and-definitions.md): definitions, blocks, `if`, text and interpolation, numbers.
3. [Data](03-data.md): variants, records, field defaults, pattern matching and exhaustiveness.
4. [Functions](04-functions.md): lambdas, type parameters, named arguments, dot notation, pipes, sections, local definitions.
5. [Interfaces](05-interfaces.md): interfaces and instances, `auto`, and the equality, order and text every type gets.
6. [Namespaces, projects and the library](06-namespaces-and-library.md): imports, multi-file projects, and a tour of `List`, `Option`, `Result`, `Text`, `Map`, `Set` and `Vec`.
7. [Recursion and termination](07-recursion.md): structural recursion, `decreasing`, mutual recursion, `Partial`.
8. [Abilities](08-abilities.md): declaring and handling effects, effect polymorphism, `Fail`, `Abort`, `Each` and `IO`.
9. [Testing](09-testing.md): tests, what a failing test tells you, testing effectful code.
10. [Proofs](10-proofs.md): `theorem`, `rfl`, induction, `rewrite`, `calc`, `omega`, goals, dependent types, proofs about effectful code, and a worked example.
11. [Running and shipping](11-running-and-shipping.md): the runtimes, exporting to JavaScript and TypeScript, performance.

## The examples are checked

Every piece of Stitchwort code in this guide is quoted from a file in [examples/](examples/), and every compiler message and program output is what the compiler printed for it. The test `crates/cli/tests/guide.rs` checks that each example file type-checks and passes its tests (the files in `examples/errors/` must fail to check, and those in `examples/failing/` have failing tests), and that each quoted block still matches its file and the compiler's output. After changing an example or the compiler, regenerate the quoted blocks with

```sh
task guide:update    # STITCHWORT_GUIDE_UPDATE=1 cargo nextest run --release -p stitchwort-cli --test guide
```

and review the diff. In the Markdown source, a comment before each block says where it comes from: `<!-- snippet: values.sw#blocks -->` is the part of `examples/values.sw` between `-- begin blocks` and `-- end blocks`, `<!-- snippet: FILE@name -->` is the declaration `name`, and `<!-- output: check errors/divide.sw -->` is what `stitchwort check errors/divide.sw` prints, run in `examples/`.
