# 1. Getting started

## Installing

Stitchwort is written in Rust, and its development tools come from a Nix flake. In a checkout of the repository:

```sh
nix build                       # the command-line tool, as result/bin/stitchwort
nix run . -- check hello.sw     # or run it without installing

nix develop                     # a shell with cargo, node and the rest
task build   # target/release/stitchwort, with native code and its runtime library
```

Put `result/bin` or `target/release` on your `PATH`. The rest of this guide calls the command `stitchwort`.

## A first program

A program is a `.sw` file with a `main` function. This one reads names, one per line, and greets each:

<!-- snippet: hello.sw -->
```stitchwort
-- Chapter 1: a first program. Run it with
--   stitchwort run hello.sw < hello.input
import Std (IO, List, Text)

def main(): {IO} () :=
  let names := IO.readAllLines()
  names.map (name => IO.print (greeting name))
  IO.print "Greeted ${names.length} people"

def greeting (name: Text): Text := "Hello, ${name}!"

test "greeting" := greeting "Ada" == "Hello, Ada!"
```

A few things to notice, all explained in later chapters:

- `def` introduces a definition. Parameters and the result have types after a colon, as in Scala and TypeScript.
- `main`'s type is `{IO} ()`: it returns nothing interesting (`()`, the unit value), and it may perform the `IO` ability, which reads input and prints. A function that doesn't say `{IO}` can't print. Effects are part of the type ([chapter 8](08-abilities.md)).
- The body of `main` is a block: each line runs in order, `let` names a value, and the last line is the result.
- `"Hello, ${name}!"` inserts a value into text.
- `test` declares a test, which `stitchwort test` runs; running the program doesn't.
- `main` comes before `greeting`. Declarations can be in any order.

Run it with input from a file:

<!-- output: run hello.sw < hello.input -->
```text
Hello, Ada!
Hello, Grace!
Greeted 2 people
```

## The command

| Command | What it does |
|---|---|
| `stitchwort check FILE` | Type-checks the file (and its theorems), and prints nothing if all is well. |
| `stitchwort test FILE` | Checks the file, then runs its tests. Results are cached: a test runs again only when something it depends on changes. |
| `stitchwort run FILE` | Checks the file, then runs its `main` on the fast runtime, with standard input and output. `--reference` runs it on the type checker's own evaluator, and `--js` compiles it to JavaScript and runs it with Node ([chapter 11](11-running-and-shipping.md)). |
| `stitchwort fmt FILE…` | Formats files in place, in the house style. `--check` only lists the files that would change. |
| `stitchwort axioms FILE NAME...` | Lists the axioms a theorem or definition depends on ([chapter 10](10-proofs.md)). |
| `stitchwort eval FILE EXPR` | Evaluates an expression in the context of a file. |
| `stitchwort repl [FILE]` | An interactive session. |
| `stitchwort build --js FILE -o DIR` | Writes an ES module and its TypeScript declarations for the file's `export`s. |
| `stitchwort lsp` | The language server, for editors. |

`check`, `test`, `run`, `axioms` and `build` keep a cache in `.stitchwort/` (it writes its own `.gitignore`); `--no-cache` ignores it. `stitchwort run` exits with 0 on success, 1 if the program didn't check, and 2 if it failed while running.

Here are the tests of the program above:

<!-- output: test hello.sw -->
```text
  ✓ greeting  ran
1 test(s): 1 passed, 0 failed (0 from the cache)
```

Run `test` again without changing anything and each test says `cached` instead of `ran`. Tests are cached by the content of what they depend on, not by file times, so editing a comment or renaming a local variable doesn't rerun anything, and changing a function reruns exactly the tests that use it.

The REPL evaluates expressions in the context of a file, and prints each result with its type. `:t` shows the type alone, and `import` lines accumulate. Given these lines (from the file `values.sw` of [chapter 2](02-values-and-definitions.md)):

<!-- snippet: repl-session.txt -->
```text
double 21
summary "Ada" [3, 4]
:t describe
import Std (List)
List.range 4
```

it prints:

<!-- output: repl values.sw < repl-session.txt -->
```text
Stitchwort 0.1.0. Enter an expression to evaluate it, `import Std (List)` to use a namespace's names, `:t expr` for its type, `:q` to quit.
42: Nat
"Ada bought 2 items: [3, 4], costing 7": Text
Nat → Text
[0, 1, 2, 3]: List Nat
```

## Projects

A single file can use only itself and the standard library. Anything larger is a **project**: a folder with a `stitchwort.yaml` that says where the source files are.

```
project/
  stitchwort.yaml        sources: [src]
  src/Shop/Shop.sw       namespace Shop
  src/Shop/Parse.sw      namespace Shop
  src/Shop/Report.sw     namespace Shop.Report
  src/Shop/Tests/Tests.sw namespace Shop.Tests
```

Every file in a project starts with a `namespace` line, and files with the same namespace form one namespace together. Folder and file names don't matter to the compiler; keeping folders in line with namespaces is a convention. [Chapter 6](06-namespaces-and-library.md) goes through this project.

Inside a project, commands take namespaces and full names instead of files, and find the project from the current folder upwards (or take `--project DIR`):

```sh
stitchwort check                       # the whole project
stitchwort test Shop                   # Shop's tests, those of namespaces under it, and of what they use
stitchwort run Shop.Report.main        # a function, by its full name
stitchwort fmt                         # format every source file
```

Running a function checks only its namespace and what it depends on. That's why tests and proofs usually live in namespaces of their own (`Shop.Tests`, `Aoc.Day01.Proofs`): `stitchwort run` doesn't have to check them.

## The playground

The playground is a browser page with an editor, the compiler (built to WebAssembly), the feature tour and the Advent of Code project. It runs entirely in the browser. To use it locally:

```sh
./web/serve.sh          # builds it, then serves web/ at http://127.0.0.1:8000
```

Its tabs check the code, run its tests, evaluate an expression, show the generated JavaScript and TypeScript, and run `main` with input you type.

## Editor support

`editors/vscode/` is a VS Code extension: syntax colouring, and a client for `stitchwort lsp`. Install it with `./editors/vscode/install.sh`, and make sure `stitchwort` is on your `PATH` (or set `stitchwort.path`). The language server gives:

- errors and warnings as you type, for single files and whole projects;
- hover: a name's type and full name;
- go to definition and find references, including into the standard library, whose files open read-only;
- the outline and workspace symbols;
- completion of parameter names after `(` or `[` in a call (`clampTo (` offers `low`, `high` and `value`);
- formatting (Format Document and Format Selection);
- **goals**: each `?` in a proof shows what has to go there, and the command "Stitchwort: Show Goals" opens a panel that follows the cursor ([chapter 10](10-proofs.md)).
