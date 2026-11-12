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
- `main` is the name for a program's entry point and nothing else: give a helper or a value that a test checks a name that says what it is.
- `stitchwort run hello.sw` runs the file's `main`. `main` is a convention, not a keyword: in a project, `stitchwort run Shop.report` runs any function of that name whose type is `() -> {IO} ()` (or the same with `Fail` and `Partial`, or no abilities at all), and a function of any other type is refused with `E-RUN-TYPE` ([projects](../projects.md#running-and-testing)).
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
| `stitchwort audit FILE` | Checks that the file's theorems can be trusted: no axiom beyond those allowed, nothing unfinished, and hypotheses some input satisfies ([syntax.md](../syntax.md#auditing-theorems-stitchwort-audit)). |
| `stitchwort search QUERY` | Searches the library's and the project's theorems and definitions by the shape of their type; `--at FILE:LINE` lists what closes a `?` there ([syntax.md](../syntax.md#lemma-search-stitchwort-search)). |
| `stitchwort doc NAME` | What a declaration does: its header, doc comment, examples and theorems about it ([syntax.md](../syntax.md#doc-comments)). |
| `stitchwort eval FILE EXPR` | Evaluates an expression in the context of a file. |
| `stitchwort repl [FILE]` | An interactive session. |
| `stitchwort build FILE` | Builds a standalone executable that runs the file's `main` ([chapter 11](11-running-and-shipping.md)). |
| `stitchwort build --js FILE -o DIR` | Writes an ES module and its TypeScript declarations for the file's `export`s. |
| `stitchwort lsp` | The language server, for editors. |

`check`, `test`, `run`, `axioms`, `audit`, `search`, `doc`, `eval` and `build` keep a cache in `.stitchwort/` (it writes its own `.gitignore`); `--no-cache` ignores it. `stitchwort run` exits with 0 on success, 1 if the program didn't check, and 2 if it failed while running.

Here are the tests of the program above:

<!-- output: test hello.sw -->
```text
  ✓ greeting  ran
1 test(s): 1 passed, 0 failed (0 from the cache)
```

Run `test` again without changing anything and each test says `cached` instead of `ran`. Tests are cached by the content of what they depend on, not by file times, so editing a comment or renaming a local variable doesn't rerun anything, and changing a function reruns exactly the tests that use it.

The REPL evaluates expressions in the context of a file (a file of a [project](#projects), found from the file's folder, is loaded as its namespace in the project, so its imports resolve, and its names are in scope), and prints each result with its type. `:t` prints the expression with its type, without evaluating it, and `import` lines accumulate. Given these lines (from the file `values.sw` of [chapter 2](02-values-and-definitions.md)):

<!-- snippet: repl-session.txt -->
```text
double 21
summary "Ada" [3, 4]
:t describe
import Std (List)
0 ..< 4
```

it prints:

<!-- output: repl values.sw < repl-session.txt -->
```text
Stitchwort 0.1.0. Enter an expression to evaluate it, `import Std (List)` to use a namespace's names, `:t expr` for its type, `:q` to quit.
42: Nat
"Ada bought 2 items: [3, 4], costing 7": Text
describe: Nat → Text
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
stitchwort check --only Shop.Proofs.total   # one theorem and what it uses (chapter 10)
stitchwort test Shop                   # Shop's tests, those of namespaces under it, and of what they use
stitchwort run Shop.Report.main        # a function, by its full name
stitchwort fmt                         # format every source file
```

Running a function checks only its namespace and what it depends on. That's why tests and proofs usually live in namespaces of their own (`Shop.Tests`, `Aoc.Year2025.Day01.Proofs`): `stitchwort run` doesn't have to check them.

## The playground

The playground is a browser page with an editor, the compiler (built to WebAssembly), the feature tour and the Advent of Code project. It runs entirely in the browser. To use it locally:

```sh
./web/serve.sh          # builds it, then serves web/ at http://127.0.0.1:8000
```

Its tabs check the code, run its tests, evaluate an expression, show the generated JavaScript and TypeScript, and run `main` with input you type.

Press F2 on a name to rename it (see "Editor support" below); a prompt above the editor asks for the new name and offers "Rename anyway" when the check finds problems. Put the cursor on a `?` and a panel under the editor shows the goal there: what has to go in its place, and the names in scope, as VS Code's goals panel does. **Share** copies a link that carries the program itself in its address (compressed, nothing is stored on a server); opening it shows that program and leaves your own saved work alone until you edit it. For an Advent of Code day, Share links to the day.

## Editor support

`editors/vscode/` is a VS Code extension: syntax colouring, and a client for `stitchwort lsp`. Install it with `./editors/vscode/install.sh`, and make sure `stitchwort` is on your `PATH` (or set `stitchwort.path`). The language server gives:

- errors and warnings as you type, for single files and whole projects;
- hover: a name's type, full name and doc comment, a `?`'s goal, or (in VS Code, with a selection) the type of the selected expression;
- go to definition and find references, including into the standard library, whose files open read-only; an `include "path"` string is a link that opens the included file;
- the outline and workspace symbols;
- completion of parameter names after `(` or `[` in a call (`clampTo (` offers `low`, `high` and `value`);
- completion of names: the local variables in scope, then the namespace's own declarations, then what the imports and the prelude bring, each with its kind and type, also while the declaration you are typing doesn't parse; after a `.` the functions the value before it can go into (`xs.` on a list offers `length`, `map`, …, and your own `Shape.area` on a `Shape`) or a namespace's members (`List.`, `Std.`); and once two letters are typed, library names that need an import (`Ma` offers `Map`), which add the import when picked;
- signature help in a call's arguments: the function's parameters, with the one you are writing highlighted (a `(low := 1)` highlights `low`);
- a quick fix on an unknown name that needs an import (`Map` without `import Std (Map)`): "Add `import Std (Map)`" inserts it, into an existing `import Std (…)` line if there is one;
- a quick fix on a `match` that leaves cases out (`E-NONEXHAUSTIVE`): "Add the missing arms" adds one arm per missing case after the last arm, each with `?` as its body and variables named after the constructor's fields (`| Circle ref text => ?`, `| [x, ..xs] => ?`);
- "Split `x` into its cases", with the cursor on a variable in an arm's patterns whose right-hand side doesn't use it: the arm becomes one arm per constructor of the variable's type (`| Some o => ?` on an `Option Nat` becomes `| None => ?` and `| Some value => ?`), for data types without indices;
- "Split on `b`", with the cursor on a `?` (or on a parameter's name in the header, when the body is a single `?`): one action for each variable in scope whose type is a data type without indices (a hypothesis such as `h: andb b c = True` isn't offered). It replaces the `?` with `match b with` and an arm for each constructor, each with a `?` body and fields named as "Add the missing arms" names them. When the `?` is a whole arm of a `match` (after splitting `b`, on `| True => ?`), splitting `c` adds `c` as a new column of that `match` (`| True, True => ?`, `| True, False => ?`, and `_` in the new column of the other arms) instead of nesting another one. When the arm already has the variable in its patterns, as a name (`| Paper, theirs => ?`), as a `_` in the column the `match` scrutinises it in (`| Scissors, _ => ?`), or inside a constructor (`| S n => ?`), the action splits that arm in place, as "Split `x` into its cases" does, rather than nesting a `match`;
- "Search for a proof", with the cursor on a `?` in a proof (whose expected type is a proposition, such as `a = b` or `p ∧ q`; not on a `?` in a program, whose expected type is data such as `Nat` or `List a`): the quick actions (Cmd+. or Ctrl+.) always answer at once, and this one runs a search for proofs that close the goal only when you pick it, with a progress message. If a simple proof closes the goal (`rfl`, a hypothesis that is the goal, `byDecision`, `omega`, `ring`, or `cases` for an impossible hypothesis, tried in that order), it is the only one found. When the search finds exactly one proof, it replaces the `?` at once, with the cursor after it and a notice "Proved by `rfl`" (undo restores the `?`). When it finds several, they are listed, best first (in VS Code a pick list; each shows the proof text), and the one you choose replaces the `?`. If none is found within the time limit, a message says "No proof found within 5 s". The search is stopped if you cancel it or edit the file meanwhile;
- the type of a `let` whose type you didn't write, shown after its name (`let total` becomes `total: Nat`), once something uses the variable; no other inlay hints;
- colours from what the checker resolved each name to: functions, types, constructors, variables, theorems and abilities, with declarations in bold (VS Code: semantic highlighting; the playground draws them too);
- formatting (Format Document and Format Selection);
- **renaming** (F2, also in the playground): put the cursor on a local, a hypothesis, a function or a theorem, press F2, and type the new name; every use follows, in every file of the project, including `import` lines and the uses through dots, pipes and `rewrite`. The renamed project is checked before anything is changed. If the new name would cause an error or change what some declaration means (it captures another name, say), the rename is refused and the problems are listed. Choose **Rename anyway** to make the change regardless: the declarations whose meaning changed are marked with a warning, "meaning changed by rename: check this", until you next edit the file, and the new errors show as ordinary errors, for you to fix by hand. Fields, constructors, types and the standard library can't be renamed yet; `stitchwort rename` does the same from the command line;
- **run icons** above the declarations, in any `.sw` file (a single file outside a project too): "▶ Run test" above each `test`, "▶ Run tests" above the first when the file has several, and "▶ Run" above `main`. A test shows its result in a message, and a failure lists the two sides of its comparison in the Output panel and marks the line in the file. "▶ Run" starts `stitchwort run` in a terminal, so it can read input. They use the same `stitchwort test` and `stitchwort run` you can type yourself; `stitchwort test FILE --only "name" --json` is the form with one test's result as JSON;
- **the Testing panel** (the flask icon) lists the tests of the files of a project, those under a `stitchwort.yaml`: run all of them, a file, or one test, and see a failure at its line, with the two sides. A result that came from the test cache is marked "cached". Files outside a project use the run icons instead;
- **goals**: each `?` in a proof shows what has to go there, and the command "Stitchwort: Show Goals" opens a panel that follows the cursor, showing the goal or expected type anywhere ([chapter 10](10-proofs.md)).

**Settings.** Each optional feature can be switched off in one place. In VS Code, search the settings for "Stitchwort": `stitchwort.inlayHints.letTypes` (the types after `let`s), `stitchwort.codeLens.run` (the run icons), `stitchwort.proofSearch.enabled` and `stitchwort.proofSearch.timeLimitMs` (whether "Search for a proof" is offered on a `?`, and how long a search may run), `stitchwort.semanticColours`, and `stitchwort.goals.openAutomatically` (open the Goals panel when a file with a `?` opens; off by default). Stitchwort files are formatted when you save them; set `"[stitchwort]": { "editor.formatOnSave": false }` to stop that. In the playground the ⚙ button beside Share opens a menu with the same switches (except the run icons, which the playground doesn't have), "Format on save" (Ctrl/Cmd+S) and the editor's font size; the choices are kept in your browser.
