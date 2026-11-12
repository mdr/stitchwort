# Proving with Stitchwort

A hands-on book about proving things about programs, in Stitchwort. You
write small programs, state what they should do as theorems, and prove
them, with the editor helping at each step: goals, case splits, missing
arms, search. It is for programmers who know a typed language and have
never proved anything; no logic is assumed.

Each chapter is a Stitchwort file, read top to bottom in the editor:
the text is in comments, and the code between them is checked as you
read. Exercises are holes (`?`) for you to fill in.

## Opening it

From a checkout of this repository:

```
nix develop -c task vscode:install
```

This builds the `stitchwort` program and installs the VS Code extension.
Put `target/release` on your PATH (or set the VS Code setting
`stitchwort.path` to `target/release/stitchwort`), then open this `book`
folder in VS Code (File > Open Folder...) and start with
`src/00-setting-up.sw`. Chapter 0 checks that everything works.

The book doesn't open in the web playground yet; that is coming.

To see which exercises are still open, from this folder:

```
stitchwort goal --summary  # how many are open in each chapter, and in all
stitchwort goal            # every open `?`, and what relies on it
stitchwort check           # checks the book; says "N goals open, allowed by ..."
stitchwort test            # runs the chapters' tests
```

## Chapters

| | Chapter | File | Time | Status |
|---|---|---|---|---|
| 0 | Setting up | `src/00-setting-up.sw` | 15 min | written |
| | **Part I. Programs and their proofs** | | | |
| 1 | Computing: tests, `rfl`, counterexamples | `src/01-computing.sw` | 45 min | written |
| 2 | Cases: splitting, hypotheses, `cases` | `src/02-cases.sw` | 60 min | written |
| 3 | Numbers and induction | | 75 min | planned |
| 4 | Lists and options | | 75 min | planned |
| 5 | Generic and higher-order functions | | 75 min | planned |
| 6 | Specs | | 75 min | planned |
| | **Part II. Logic** | | | |
| 7 | Equations in depth | | 60 min | planned |
| 8 | Logic | | 90 min | planned |
| 9 | Decisions | | 60 min | planned |
| 10 | Rules as data | | 90 min | planned |
| 11 | Relations | | 60 min | planned |
| 12 | Proofs are programs | | 45 min | planned |
| | **Part III. A small language** | | | |
| 13 | Environments | | 45 min | planned |
| 14 | A calculator | | 90 min | planned |
| 15 | Commands and loops | | 90 min | planned |

Times are estimates until readers have measured them. The plan for the
whole book is in
[docs/proposals/proving-with-stitchwort-outline.md](../docs/proposals/proving-with-stitchwort-outline.md).

Each chapter is its own namespace (`Book.Computing`, `Book.Cases`, ...),
and imports from an earlier one only the definitions it builds on, so an
exercise you skipped never blocks a later chapter.
