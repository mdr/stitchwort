# Surface syntax (implemented subset)

**Status:** describes `crates/syntax` as of 1 November 2026. DESIGN.md §4 shows the intended language. Not yet implemented: anonymous record types and functions over any record with a field (records stages 3 and 4) and a `case` expression.

## Layout

Interim rule, until the full layout specification (DESIGN.md §14):

- A declaration starts at column 0.
- Every following line that's indented continues it.
- Tabs aren't allowed. `--` starts a comment that runs to the end of the line. The `--|` lines of a run of comments above a declaration are its doc; plain `--` lines are notes for maintainers ([Doc comments](#doc-comments)).
- Names are ASCII: letters, digits, `_` and `'`, starting with a letter or `_`. Other characters are fine in text, characters and comments, but `def café` is an error ("unexpected character"). A character that shows as nothing or as a plain space, such as a no-break space pasted from the web, is named by its code point: "unexpected character U+00A0 NO-BREAK SPACE", with the note to type a plain space or delete it. That includes format characters such as U+2061 (FUNCTION APPLICATION) and tag characters, which show as nothing.
- **ASCII is the base syntax, with a fixed set of Unicode spellings of operators** (D1200): `∈` `∉` `→` `↔` `∧` `∨` `¬` `≤` `≥` `≠` `∃` `∀` for `in` `!in` `->` `<->` `&&` `||` `!` `<=` `>=` `!=` `exists` `forall`. Each is exactly the token its ASCII form is, so meaning, precedence, errors and hashes are the same either way, and the two mix freely. Any other symbol from logic or mathematics (`⊆`, `∪`, `≡`, `λ`, `⇒` …) is an error saying what to write instead, or that it isn't supported. See [Logic notation](#logic-notation-in--and-exists).
- **Blocks.** An expression that starts on a new line is a block: each line at that line's column is a statement, and lines indented further continue it. A statement is `let x := e` (or `let x: T := e`), binding `x` for the following lines, or an expression run for its effects, whose value is dropped. The last line is the result. A statement line that performs no effects does nothing, so it warns (`W-NO-EFFECT`, D1702): a parser named but not called (`shortNumber` for `shortNumber()`, with the note "call it: `shortNumber()`"), a function missing its argument (`char` for `char ','`), `x + 1`, or `list.map f` written as if it changed `list`. A line whose value is dropped but which performs something, such as `shortNumber()` read only to skip a number, doesn't warn, nor does a `()` line, a `handle`, or a line whose type isn't known yet where it's checked (a call of a parameter whose type later lines settle). A call of an effect-polymorphic function (`List.map`) warns only when its callbacks perform nothing. The standard library has no such lines: a library file with one doesn't check (`examples/accept/no-effect-line.sw`). A `let` may hold a proof as well as data, and later lines know its value: after `let p := n`, `p` *is* `n` to the checker, so `Nat.leAddRight p 1` proves `n <= n + 1` ([proposals/let.md](proposals/let.md)). A `match` or local definition after a `let` knows it too, and a recursive call on `let r := rest` is as small as `rest`. The value is computed once when the program runs, before the lines after it; a proof or a type isn't computed at all (as for a proof parameter). Messages may show the value where you wrote the name. A `let` performs only what its right-hand side does: binding an effectful function performs nothing until it's called. A `let` whose right-hand side performs an operation (`let k := ask()`) is opaque: its value isn't known until the program runs. A line at the block's column straight after a line ending in an operator (such as `->`) continues that line. So does a line at the block's column (or further in) that *starts* with an infix operator that no expression begins with, as if the operator ended the line above: `&&` `||` `->` `<->` `=` `==` `!=` `<` `<=` `>` `>=` `+` `++` `*` `/` `%` `!in` and their Unicode spellings (`∧ ∨ → ↔ ≠ ≤ ≥ ∉`), as well as `|>` (above). `-` and `!` can begin an expression (negation), and `in` ends a `let` or a `rewrite` target, so at the block's column they are left as they were: `-y` is a new statement (`examples/accept/leading-operator-lines.sw`). An operator line left of the block's column is an error that names its column and the block's (in the spelling written, `∧` or `&&`).
- **An expression `let`** (D1425, D1453). `(let x := e; body)` binds `x` for `body` where a block's line would be awkward: inside brackets, as an argument, or in a one-line definition. It is `let x := e` followed by `body`, with the same tree as the block form, so everything above applies unchanged: later parts know the value, it may bind a proof, `let x: T := e` and patterns work, and a refutable pattern is `E-LET-REFUTABLE`. The `;` ends the value and is required; `in` can't be the separator because it is membership, so in `(let found := x in xs; found)` the value is `x in xs`. A `let` is a whole expression, like a lambda: after `:=`, `=>`, `then`, `else`, an opening bracket or a comma, or at the start of a block line (where `let x := e; body` on one line is the same as two lines). As an argument, an operand or a `|>` stage it needs brackets, and its body runs as far as an expression can, so `(let x := 1; x) + 2` needs the brackets. The only other use of `;` is a sequence, below. A missing `;` or body is `E-PARSE` (`examples/accept/let-expression.sw`, `examples/reject/let-expression-missing-*.sw`).
- **A sequence** (SW-888, D1700). `(a; b)` runs `a`, then gives `b`'s value. It is the block lines `a` and `b` on one line, with the same tree, so it means exactly what they mean: `a` runs first, with its effects, and its value is dropped whatever its type, as a block line's is (`(1; 2)` is `2`). An `a` that performs no effects warns, as such a block line does (`W-NO-EFFECT`, above): `(char; nat())`, with `char` missing its argument, and `(1; 2)`. One that performs and gives a value, such as `(nat(); char ',')`, doesn't. A chain `a; b; c` is three lines, and `let` mixes in on either side: `(let x := e; a; b)` and `(a; let x := e; b)`. It goes where an expression `let` goes, and binds the same way: looser than everything else, so `f a; g b` is `(f a); (g b)`, `a |> f; b` is `(a |> f); b`, `a; b |> f` is `a; (b |> f)`, and after `=>`, `then`, `else` or an arm's `=>` the rest of the expression is the sequence (`x => a; b` is `x => (a; b)`, and in `if c then a; b else d; e` each branch is a sequence). As an argument or an operand it needs brackets: `Mul (text "mul("; nat()) (char ','; nat())`. It ends at a comma or a closing bracket, so `(a; b, c)` is the pair `((a; b), c)` and `[a; b, c]` has two items. A `;` straight after a `let`'s value starts the `let`'s body, also when the value ends in a lambda or an `if`: in `(let f := x => x + 1; f 2)` the body is `f 2`, and a sequence as the value needs brackets, `(let x := (a; b); x)`. A `;` needs an expression after it: `(a;)`, or a `;` ending a block's line, is `E-PARSE`, since block lines need nothing between them (`examples/accept/sequence-expression.sw`, `examples/reject/sequence-*.sw`).
- **`if` across lines.** `then` and `else` may start a line, even at the block's own column (where any other token would start a new statement), as long as they're indented at least as far as the line the `if` is on. So `if c then a` / `else if d then b` / `else e` on separate lines, all lined up, is one expression. A nested `if` takes the closest `else`. An `else` further left than its `if`'s line is an error that says so.

## Style

Whitespace around `:` doesn't matter to the parser: `(n : Nat)`, `(n: Nat)` and `(n:Nat)` are the same binder. The house style is `x: T`, with no space before the colon and one after, as in Scala and TypeScript: `(n: Nat)`, `[a: Type]`, `{ lo: Nat }`, `def f (n: Nat): Nat`, `def x: Nat := 1`, `let x: T := e`, `(e: T)`, `match h: e with`, `if h: P then …`. `:=` has a space on both sides. A call with no arguments is written `f()`, with no space before the `()`. **`name()` with no space is a call**, and it is a single atom, so it is one argument: `parseTurns IO.readAllLines()` is `parseTurns (IO.readAllLines())`, `f x()` is `f (x())`, and `f().x` is `(f()).x`: dot notation applies to the result of the call (`IO.readAll().lines`, `f().g y`). With a space, `f ()` is the ordinary application to the unit, so `f x ()` is `f x ()` and `f ().x` is `f (().x)`. The compiler's messages and printed types use the house style.

## Doc comments

A declaration's **doc** is the comment above it (docs/proposals/documentation.md; stage 1a, SW-1018). No syntax is new: `--|` is a `--` comment, and the compiler ignores both. Tools read the text when they show it: `stitchwort search` prints a one-line summary under each result, `check --index` gives each symbol its `doc`, `summary` and `docMarker`, `stitchwort doc NAME` prints the full doc with the declaration's examples and theorems (below), and the language server shows the full doc when you hover a name (the playground shows only the summary).

```
--| Keeps the `Some` results, in order.
--|
--| `f` may perform abilities, which run in list order.
-- A function of its own so the recursive call is written once.
def List.filterMap: List a → (f: a → {e} Option b) → {e} List b
```

- **What gets a doc.** A top-level declaration, from the first token of its group, so the doc goes above its attributes (`@[noReceiver]`); a comment between an attribute and its `def` is not a doc. A constructor, a record or interface field and an ability operation, when its name is on a line of its own, after at most the `|`, `,` or `{` that introduces it, and no other member is on that line. A member on the declaration's own line, or sharing a line with another (`type Pair = { first: Nat, second: Nat }`), has no doc of its own. The equations and arms of a definition have none, and neither has a trailing comment (a comment after code on its line).
- **The comment run.** The comments directly above the declaration, with no blank line between them or before the declaration. Of the comments above it, only the last such group counts; a blank line ends the run.
- **The doc.** The `--|` lines of the run, in order, each without the `--|` and the one space after it; a `--|` line with nothing after it is a paragraph break. The plain `--` lines of the run are maintainer notes: they stay out of the doc, above or below it.
- **Plain `--` comments are never docs** (SW-1044). Since the sorting pass (D2134), only `--|` lines make a doc; a `--` block above a declaration, or at the top of a file, is a maintainer note and shows nowhere. `docMarker` is therefore always `"--|"`; it is kept so the JSON doesn't change.
- **File docs.** The comment runs before a file's first declaration, other than the run attached to it, are the file's doc, joined as paragraphs: their `--|` lines (a file of only `--` comments has no file doc). A `namespace` or `import` line is not a declaration here, so every run above one is the file's. A project file's doc belongs to its `namespace` line's namespace; a std file's to its folder's (`List/Toolkit.sw` to `Std.List`), and a `core/` file's to none, since the prelude's files mix namespaces.
- **The summary** is the doc's first sentence: the first paragraph's lines joined by single spaces, up to the first `.` outside backticks that is followed by whitespace or the end (not the ones in `e.g.` and `i.e.`). One over 160 characters is cut at the last space before the 160th that is outside backticks, and ends in `…`. It is never made from the type.

Docs are read from the declaration's file as it is, when they are shown. They are not part of elaboration, hashes or the check cache's key, so editing one changes no hash. The code is `stitchwort_syntax::docs`.

### What to write

**A comment says what the code can't** (SW-1099; Matt, 2 November 2026). The standard library documents its whole API; application code comments sparingly.

**The standard library** (`crates/elab/src/std`) is written for users who won't read the implementation. Every public definition, type, interface and ability has a `--|` doc that says what the type doesn't: the result in words, edge cases (empty, zero, past the end, not found), which abilities are performed and in what order, cost when it matters, and how it differs from its neighbours. Link a property's theorem (``[`List.isDistinctIff`]``) instead of restating it. Add an example when one or two lines show it; one that needs more setup belongs in a test or a `…Example` theorem, which `stitchwort doc` prints anyway. A std doc that only restates the type is improved, not deleted. A short opening sentence that the name nearly says is fine (`--| Whether the integer is below zero.` on `Int.isNeg`), as it reads well on hover; what earns the doc its place is what follows it: stable or not, edge cases, links to the theorems about it, and the related functions a reader might be looking for (``To get just the first, use [`List.find`]``) (D2432, Matt, 5 November 2026).

- Not `--| Whether no element appears twice.` on `List.isDistinct`, which the name says, but what the type can't say: ``--| Whether no element appears twice, in O(n log n): `List.Distinct` as a `Bool` ([`List.isDistinctIff`]).``
- The edge case is the doc: ``--| The number before `n`, and 0 for 0.`` (`Nat.pred`).
- A one-line example settles what prose leaves open:

  ```
  --| The position of the first `x` in the list, counting from 0, or the list's
  --| length if `x` isn't in it: `[5, 7, 5].indexOf 5` is 0, `.indexOf 9` is 3.
  def List.indexOf [auto eq: DecEq a]: List a → (x: a) → Nat
  ```

**Application code** (`aoc/`, `games/rogue/`, `examples/`) should explain itself through clear names and types. A comment is for what they can't say: why, an invariant, units, what a `None` or a constant means, a surprising choice, the rule from the puzzle that a function implements. Never restate a name, a type or a field list. Most declarations have no doc, and that's normal. Add an example only if one or two lines show it.

- Restates the fields, so it should be deleted:

  ```
  --| Where the guard stands and which way she faces.
  type Guard = { position: Position, facing: Direction }
  ```

  So does `--| What one character of the map shows.` above `type Cell = | Floor | Obstruction | GuardStart`.
- Says why: `--| How many states the guard can be in: a walk this long has repeated one.` above `def Lab.stateCount (lab: Lab): Nat := lab.height * lab.width * 4`.
- Says what the `None` means: ``--| The positions the guard visits before leaving, or `None` if she is still on the map after `stateCount` steps, and so walks forever.`` (`Lab.patrol`).
- Gives the input format and failure, which the type `List Text → {Fail} Lab` doesn't: ``--| One line per row, all as long as the first: `.` floor, `#` an obstruction, `^` the guard. A failure names the line.`` (`parseLab`).
- A file doc covers what spans the file: the puzzle in a sentence or two, how to run it, an invariant shared by several functions (the step budget in `Aoc.Year2024.Day06`'s).

**Name a definition `main` only when it is a program entry point**: `def main(): {IO…} ()` (Matt, 9 November 2026). A value or function that a test checks, or an example shows off, is named for what it is (`finComparisons`, `topDown`), not `main`: `stitchwort run` refuses a `main` of any other type (`E-MAIN-TYPE`), and a reader takes `main` to be what runs.

**Theorems.** In application code a theorem's statement usually is its doc; give one a `--|` doc only when the statement needs help: which sentence of the spec it covers, or why a hypothesis is there. In std, a theorem whose name and statement say it all (`List.lengthAppend`) needs no doc. [proving-guide.md](proving-guide.md) §2 has the rule for proofs.

**`--` notes** are for maintainers, with the same parsimony: why the code is as it is, a workaround and its ticket, or something a reader would otherwise "fix". The note on `opaque def lcg` (`games/rogue/src/Rogue/Random.sw`) explains why it is opaque. A note should never narrate what the next lines do. Tools never show `--` notes, so anything a user needs goes in `--|`.

**Coverage** (below) is a target only for std. In application code a low "documented" figure is no problem, and a doc written to raise it is noise (SW-1100 changes the report to match).

### Entry points

There is no annotation for an entry point: a function is one when its type can be run (SW-2561; D3452, Matt, 9 November 2026). The type is `()` to `()`, with abilities among `IO`, `Fail` and `Partial`, so exactly these five:

```
() -> ()
() -> {IO} ()
() -> {IO, Fail} ()
() -> {IO, Partial} ()
() -> {IO, Fail, Partial} ()
```

- **In a project**, `stitchwort run Shop.report` runs the function `Shop.report` by its full name, whatever it is called. A name that isn't in the project is `E-RUN-UNKNOWN` (with a "did you mean" for a near miss); a definition of any other type, such as `Nat` or `Nat → Nat`, is `E-RUN-TYPE`, which lists the five types.
- **For a file**, `stitchwort run shop.sw` runs the file's `main`, and only that: a file has no way to name another function, so put it in a project to run it. A file without a `main` is `E-NO-MAIN`, and a `main` of another type is `E-MAIN-TYPE`.
- **`main` is a convention**: the name that `run` looks for in a file, and the name to give a program's one obvious entry point. Nothing checks `main` where it is defined, so a `main` of the wrong type fails only when it is run. The rule above, to name a definition `main` only when it is an entry point, is what keeps the convention meaningful.

### Doc links

A `--|` line may link to another declaration with ``[`Name`]`` (SW-1042; docs/proposals/documentation.md §7, D2149, D2153). `Name` must be name-shaped: letters, digits, `_`, `'` and `.`, starting with a letter or `_`. Only that is a link: bare `[Name]` is not (`[x]` is list notation), and neither is prose such as ``its `[` is; its `]` `` or a plain `--` note.

```
--| Keeps the `Some` results, in order. Like [`List.map`] when `f` never gives `None`;
--| see [`List.filterMapSome`].
```

- **Resolution.** After a namespace is checked, each link in its files resolves first as the file resolves names (its imports and its namespace, so a link may point forward or at the declaration it is on). Failing that, a full name (`Std.List.filterMapSome`), a library name without `Std.` (`List.filterMapSome`) or a name in the file's own namespace resolves, whatever the file imports: a link never forces an `import`. A project namespace's names count before it is checked, so a link to another namespace doesn't depend on checking order. A type and its constructor of the same name are one link to the type. A link may name a namespace (``[`Std.List`]``).
- **`W-DOC-LINK`** is the warning for a link that names nothing, or two different things. It points at the link and, for a name that isn't there, says `did you mean` the nearest name within two edits. A namespace with errors isn't checked for links. A library file with the warning doesn't load, as for `W-REDUNDANT`, so the library has none (a test loads every file). A project only warns.
- **No dependency.** A link adds no dependency between declarations or namespaces, and the check cache's key is unchanged. The cache does not keep `W-DOC-LINK`: the warnings are worked out again after each check or replay, so one for a link into another namespace is never out of date (SW-1045).
- **`doc` and the index.** `stitchwort doc NAME --json` gives each link of a `--|` doc in `links`: `{"text", "status", "target", "file", "line"}`, in the order written, where `target` is the full name (`null` unless `status` is `"resolved"`; it can also be `"unresolved"` or `"ambiguous"`) and `file`/`line` say where it is declared (`null` for a namespace). The text output prints a link as its name and marks one that does not resolve with `(unresolved link)` after its name. `check --index` gives each symbol's doc `links`: `{"text", "target"}` with `target` `null` when it names nothing. Both read the file's `import` lines from the syntax (`import N (x)`, `import N (x as y)`, `import N (..)`), without checking, so a link that only an import makes resolve resolves there as it does in `check` (SW-1045).

### What a declaration does, `stitchwort doc`

`stitchwort doc NAME` (SW-1019; docs/proposals/documentation.md §5.3 to §5.5) shows a declaration in one place: its header as written (with the parameter names the elaborated type drops), its doc, where it is and what to import, the **examples** attached to it, and the **theorems** about it. **To find out what a function does, run it before reading the source.**

```
stitchwort doc List.filterMap                # the library, from anywhere
stitchwort doc Shape.scale                   # a project name, as `import N (..)` sees it
stitchwort doc Aoc.Common.Range.size         # or in full
stitchwort doc Option                        # a type: its constructors, then the namespace's declarations
stitchwort doc Std.List.Cons                 # a constructor, field or ability operation shows what it belongs to
stitchwort doc Aoc.Year2024.Day06            # a namespace: its file docs, then each definition, type, interface and ability with its summary
stitchwort doc Text.padLeft --theorems 0     # no check: header, doc and examples from parsing alone (about 0.2 s)
stitchwort doc List.map --json               # version 1
stitchwort doc --coverage List Vec           # how much is documented (below)
```

- **The name** is a full name, a library name without `Std.`, or a project name as `import N (..)` sees it (project namespaces are tried the way `import` does). Several matches are listed, and exit status is 2 (write one in full); none prints the names that look like it and exits 1; a name found exits 0, documented or not. A type that is also a namespace (`List`, `Option`, `Map`) prints the type first, then the namespace's listing. The project is the one found from the folder you're in, or `--project DIR`, or `FILE` instead of one; with none, the library alone.
- **Examples** (D2135, D2144): a `test` whose description is a qualified name of the declaration (`test "List.unzip"`; any suffix with two components or more counts), or starts with one and then a space, `,` or `:` (`test "Result.map, an error"`), or is its unqualified name when it is a function (a definition with a function type) and the test is in its file; and a theorem named `X.yExample`, `X.yExample2`, … for the declaration `X.y`. They are printed with their source and never run: `stitchwort test` runs the tests and `check` the theorems. A closed theorem proved by `rfl` that merely mentions the declaration is not an example (D2145); it is among its theorems.
- **Theorems** (D2141): for a definition, the theorems whose statement mentions it (what `stitchwort search NAME --theorems` finds, but for the `…Example` theorems, which are examples), in three groups, then in search's order (fewest premises, smallest, by name): **`rewrite`**, named after it, with an equation or `Iff` whose left side is headed by it (`List.filterMapAppend`); **`named`**, the other theorems named after it (`List.memFilterMapElim`); **`other`**, the rest (`Char.toTextDigits` mentions `List.filterMap` but is about digits). "Named after" means the theorem's last name component contains the declaration's as whole camel-case words, whatever the case of the first letter. At most 8 are shown (`--theorems N`; `0` shows none and skips the check, so there is no elaborated `type` in the JSON), with the total and the `stitchwort search` command, with `--limit` set, that lists all of them. A statement is printed without the leading parameters that only later ones use. Theorems are not listed for a type, interface, ability, constructor, field, operation, theorem or instance.
- **Scope** (D2146): for a library name, the library's theorems and tests (`--project` or a file adds the project's). For a project name, the declaration's namespace and the namespaces that use it, directly or not (they import from it or write a name that resolves into it: the project's own dependency graph), and only those are checked and searched: a namespace that doesn't use it isn't looked in, or even checked. For `Aoc.Common` that is most of the project; for a day's code it is the day's own namespaces.
- **JSON** (version 1): `name`, `kind` (`definition`, `theorem`, `instance`, `type`, `interface`, `ability`, `constructor`, `field`, `operation`), `header`, `type` (absent without a check, or for a type, interface or ability), `file`, `line`, `import`, `container` (for a member), `doc`, `summary` and `docMarker` (`null` without a doc), `members`, `examples` (`kind`, `name`, `file`, `line`, `source`), `theorems` (`total`, `shown` with `name`, `type`, `statement`, `file`, `line`, `summary`, `group`, and `command`; `null` when not listed) and `warnings`; a type that is a namespace has the listing under `namespace`. A namespace is `{version, namespace, fileDocs, members}`. Several matches are `{version, matches}`, none `{version, matches: [], closest}`.
- **Cost**: the doc, summary, header and examples need only parsing (about 0.2 s, std included). The elaborated type and the theorems load the library through the check cache: for `List.filterMap` about 0.4 s warm and 6 s cold (1 November 2026, release build); a project name also checks its namespace and those that use it (18 s for `Aoc.Common.Range.size`, whose dependents are most of AoC).

**Coverage** (`stitchwort doc --coverage [NAMESPACE…] [--list] [--json]`; SW-1025, docs/proposals/documentation.md §6.2, D2138, D2148): how much is documented, per namespace, from parsing alone (no check, so about 0.3 s for all of std). The namespaces are named as `doc` names them (`List` or `Std.List`; a nested one is counted with what is in it); none given, it covers the project's namespaces inside a project, and otherwise the library, by its first component (`Std.List`, `Std.Vec`, …, and `Std` for what is directly under it) with a `total`.

- **Figures.** Definitions, types, interfaces and abilities with a doc, out of the total; the same with an example attached by name (the rules above); and **theorems** with a doc, out of their total, reported apart and never added to the first. Constructors, fields, operations, instances and generated (`%`) names aren't counted.
- **A doc that doesn't count** is one under 4 words, or one that only repeats the name (its letters and digits, ignoring case, spelled the name's: `--| fill the whole bag` on `fillTheWholeBag`). Such a declaration is listed as undocumented with the reason (`no doc`, `too short`, `repeats the name`) (the `--` of a plain comment above it is no doc, so it is listed as `no doc`).
- **Plain comments.** A `--` comment above a declaration is no doc (SW-1044), so it counts as `no doc`; the report no longer tracks `--` docs.
- **Unattached examples.** A theorem named `X.yExample` or `X.yExample2` whose `X.y` is no definition or theorem is listed, to rename, since `doc` attaches it to nothing.
- **A target for the library only** (SW-1100). The standard library is documented comprehensively, so for `Std.*` the text gives percentages and lists the undocumented declarations. Application code (aoc, the roguelike, examples, any project) is documented sparingly, and a doc must not restate the code, so for a project the text gives plain counts (`with a doc: N of M declarations`) and no list; `--list` adds the declarations without a doc that counts, headed "without a doc that counts". `--list` needs `--coverage` and changes nothing for the library or in JSON.
- **Exit status** is 0 however poor the coverage; a name that isn't a namespace is 2 (with `--coverage` every positional is a namespace).
- **JSON** (version 1): `namespaces`, each `{namespace, declarations, theorems, undocumented, undocumentedTheorems, unattachedExamples}`, and `total` (each declaration once; only with more than one namespace). Each also has `target`: true for the library, false for a project's namespaces (and for a `total` that includes one); the lists are always there. `declarations` is `{total, documented, withExample}`; `theorems` has no `withExample`. An `undocumented` entry is `{name, kind, file, line, reason}`. The text lists the undocumented declarations of the library (a project's with `--list`); the theorems' are in the JSON.

### Renaming, `stitchwort rename`

`stitchwort rename TARGET NEW-NAME` renames a local, hypothesis, function or theorem everywhere in the project (SW-2630, docs/proposals/refactoring.md). Fields, constructors, types and namespaces are refused for now, as is anything in the standard library.

- **TARGET** is a declaration's full name (`Shop.step`), or a position in a project file, `src/shop.sw:12:5` (line and column from 1): a declaration's name, a use of it, or a local's binder or use. **NEW-NAME** is one lowercase identifier that is not a keyword.
- The renamed project is checked first, and compared with the project now: new diagnostics (errors and warnings) and declarations whose meaning (content hash) changed, such as a new name that captures a global. Clean, the files are written. With problems nothing is written and they are listed.
- `--anyway` writes the files even with problems and lists them as what is left to fix by hand. `--dry-run` writes nothing and lists the edits (`file:line:column`) and the problems. `--json` prints version 1 of the result: `status` (`applied`, `applied-with-problems`, `not-applied`, `dry-run` or `refused`), `applied`, `edits` (`file`, `line`, `column`, `endLine`, `endColumn`, `newText`, from 1), `problems` (`kind` of `error`, `warning` or `changed-meaning`, with `file`, `line`, `declaration` and `message`) and `refusals` (`message`). `--project`, `--no-cache` and `--cache-dir` are as for `check`.
- **In the editor** (F2, in VS Code and the playground; the same edits and trial): `prepareRename` gives the name's range or the refusal in words; `rename` answers the `WorkspaceEdit` when the trial is clean, and otherwise an error listing the first five problems and "and N more", with `data: {"renameAnyway": true}`. The server remembers the refused plan; `workspace/executeCommand` of `stitchwort.renameAnyway` answers its edit (the playground applies it itself), and a client that advertises `window.showMessage` is also sent a `window/showMessageRequest` with a "Rename anyway" button, on which the server asks it to `workspace/applyEdit` (VS Code). Declarations whose meaning changed get the warning "meaning changed by rename: check this" until their file is edited to other text than the rename left.
- **Exit status:** 0 renamed cleanly (with `--dry-run`: would be); 1 problems found and nothing written; 2 refused or not understood (no such name, a library name, an unsupported kind, a bad new name, a file that does not parse, a project still unchecked or that cannot be checked), nothing written, and `--anyway` does not change this; 3 written with problems left to fix (`--anyway`).
- Only the last component of a name is edited at each use, and only where the text there ends with the old name, so an import alias (`import List (map as each)`) keeps its alias.

## Declarations

```
-- Data type. The universe defaults to `Type`.
type List (a: Type): Type =
  | Nil
  | Cons (head: a) (tail: List a)

type False: Prop            -- no constructors

-- Definition: a header, then a `:=` body or arms. `a` is only used as a
-- type, so it's bound automatically as an implicit parameter: `[a: Type] -> …`.
def length: List a -> Nat
  | []        => 0
  | [x, ..xs] => Succ (length xs)

-- Implicit parameters can also be written out, and are in scope by name.
theorem cong (f: a -> b) [x y: a] (p: x = y): f x = f y := J (y' p' => f x = f y') rfl p

-- A theorem's type must be a proposition
theorem zeroPlus (n: Nat): 0 + n = n := rfl

-- A test: a runtime check, run by `stitchwort test`, that a `Bool` (or a decidable proposition, as `if` takes) is `True`; it may call `Partial` code
test "lengths add up" := length ([1] ++ [2, 3]) <= 3

-- Exported to JavaScript by `stitchwort build --js`
export def total: List Nat -> Nat
  | []        => 0
  | [x, ..xs] => x + total xs
```

`stitchwort test` also takes `--only "name"`, to run the one test of that name, and `--json`, to print the results as one JSON object (`ok`, which is false if any test failed or ran out of resources, or if `--only` or the target matched no test (also a warning, exit 1): per test `namespace`, `name`, `outcome` (`passed`, `failed` or `unfinished`), `cached`, `file`, `line`, `column`, `message`, `assuming` (what a test that ran relies on: each with the `declaration` it is in, in full, `kind`, `goal` for an open goal or `error` for a declaration with an error standing in for its statement, and the `file`, `line` and `column` of its `?` or error, as in `stitchwort audit --json`'s `openGoals`; empty when there are none), and for a failure `failure`: `{part, comparison}`, with `comparison` as `{op, left, right, difference}`) for editors: the VS Code run icons above each `test` and `main`, and its Testing panel, use them.

Without `--json`, it prints a line for each test (`✓ … ran`, `✗ … ran (…)` with why it failed, or `✗ … not run (…)` when it failed without running, such as ``not run  (`half` isn't written yet: its body is `?` (src/Demo/Demo.sw:11:17))`` for a test whose code reaches an open goal; a passing test that relies only on proofs or types with open goals runs, and its line says what it assumes, the first three names and then `and N more`: ``✓ … ran  (assuming `exercise`)``), then `N test(s): P passed, F failed (C from the cache)`, and exits 0 if no test failed or ran out of resources, or 1 otherwise (also when `--only` or the target matched no test). A declaration with an error doesn't stop the run (D3523, Matt, 11 Nov 2026): the errors are printed as `check` prints them, every test whose code uses only declarations that check runs on its merits, and a test whose code uses one with an error (directly or through what it calls) fails with ``it uses `paperLosesToScissors`, which has an error (src/01-computing.sw:140:61)`` as its reason (``it uses `f`, which depends on `g`, which has an error (…)`` when it is through another declaration), and its line says `not run`. A `def` or `theorem` whose statement checked but whose body didn't stands in for its statement, as a `?` does (D3527), so a test that only passes a broken theorem as a proof runs, and its line says so: ``✓ … ran  (assuming `doubleTwo`, which has an error (src/a.sw:9:36))`` (D3525). A failed line says what it assumed too. A statement that stands in may be false, so a test whose run casts a value along such a proof (a cast with `J`) isn't run: ``✗ … not run  (it computes with a proof, and relies on `natIsBool`, which has an error (src/a.sw:1:34))``; the same goes for a proof with a `?`. The run exits 1 whatever the tests do, and `--json` has `ok: false`, with the failed test's `message` and place; each test's `assuming` lists what it assumed, each with its `declaration`, `kind` (`goal` or `error`), `file`, `line` and `column`. A test whose own body has an error is a failed result too, so the number of tests doesn't change as errors come and go: ``✗ … not run  (it has an error (src/a.sw:15:21))``, with the error printed as usual. `--json` has a top-level `errors`, the number of declarations with an error (tests included), beside `tests`, and `ok` is the exit status. A namespace that imports one with errors is checked like any other (D3524): what in it only refers to a broken declaration is checked against its statement, and what has to compute with it, or uses one whose statement is broken, waits, said once per broken name per file on its import (``[E-USES-FAILED] `broken` has an error, so 2 declarations here can't be checked until it's fixed``, with a note listing them); its other tests run. A test fails for an open goal only in a project with `check: open-goals: warn` (see [Goals](#goals-)); elsewhere the open goals already fail the run.

When a test fails, `stitchwort test` and the playground's Tests tab say why, as far as they can (D601). If the test is a comparison (`==`, `!=`, `=`, `<`, `<=`, `>`, `>=`), they show the values of its two sides, in the order written; for two lists or two texts that aren't equal, also where they first differ (counting from 0):

```
  ✗ parses the example  ran  (`==` is False)
      left:  [1, 2, 4]
      right: [1, 2, 3]
      first difference at [2]: 4 vs 3
```

The comparison can be the last line of a block of `let`s, or an operand of `&&`: the first operand that is false is the one shown, with its text and where it is:

```
  ✗ both parts  ran  (`==` is False)
      left:  3
      right: 4
      in: part1 2 == 4  (day1.sw:14:31)
```

A false operand that isn't a comparison (`isSorted xs`) is named with `in:` alone. The sides are evaluated again only when the test fails (also when the failure comes from the cache, which keeps just the outcome), so a passing test never pays for it, and nothing here changes whether a test passes: the run found `False` first. A value is cut off with `…` after about 200 characters, and one too large to quote is shown as `… (too large to show)`. A test that is neither (`List.all p xs`, `a || b`, `not (a == b)`) reports `evaluated to False`.

Definitions may be named in either case: `length`, or `Not` for a function returning a type.

**Automatic implicits.** An unknown lowercase name in a signature (the whole signature, header parameters included) is bound as an implicit parameter at the front if every use of it is either where a type is expected (`List a`, `a -> b`, `[x: a]`) or the whole argument of a type for a parameter that's a value (Idris's way). So with `type Dial (highest: Nat) = …`, `def part1 (start: Dial highest) (turns: List Turn): Nat` means `def part1 [highest: Nat] (start: Dial highest) …`: its type is the parameter's. "A type" here is a data type, an ability, or a definition whose result is a type (`def Below (n: Nat): Type`). Several are bound in the order of their first uses, and one may depend on another (`(t: Tagged a x)` for `type Tagged (a: Type) (tag: a)` binds `[a: Type] [x: a]`). Uses needing different types are `E-TYPE-MISMATCH` at the later one, with a note. Any other use keeps it an unknown name, so a misspelling doesn't quietly become a parameter: `Dial (highest + 1)` or `… <= highest` in the signature needs `[highest: Nat]` written out. Bound names are in scope by name in the body, as written-out implicits are.

Patterns are variables, `_`, numbers, constructors applied to patterns (nested to any depth, as in `half (Succ (Succ n))`), record patterns ([Records](#records)), or `()`. A number pattern tests for that number, of any size. A character pattern `'L'` is `MkChar 76 _` (the code as a number pattern, the proof as `_`), so it groups and falls through like numbers, and can be nested in other patterns. In an arm with a variable or `_` where other arms have numbers, the argument is known to be none of those numbers, and nothing more: not that it's a `Succ` (so with `def make: (n: Nat) -> ResultType n`, where `ResultType` matches `Zero` and `Succ`, the arms `| 0 => …` and `| n => …` check the second arm with `ResultType n` not computing). What it is known not to be is used where another match on the same numbers (or some of them) meets it: that match takes its own catch-all arm (docs/proposals/literal-match-facts.md). So a proof by the same `match` as a program's reaches the program's `_` arm in its own: with `commandOf` matching `'k'`, `'j'` and `_ => None`, a theorem that only `'k'` and `'j'` are commands is `match char with | 'k' => … | 'j' => … | _ => …`, and in the last arm `commandOf char` is `None` (`examples/accept/literal-match-facts.sw`). From hypotheses `n ≠ 3` and `n ≠ 7`, match `n` on `3`, `7` and `_`, rule out the first two with the hypotheses, and the `_` arm knows the rest. This works for `Nat`, `Char` and `Int` patterns (on an `Int`, for the size within each sign), and through `k +` (`f (Succ (Succ n))` takes `f`'s catch-all when `n` is known to be none of `f`'s numbers less 2), but not through other arithmetic, and the facts aren't hypotheses with names: a proof that needs `n ≠ 3` as a value proves it as usual. To use the shape of a number, match on `Zero` and `Succ` instead; a number pattern in a column that also has `Zero` or `Succ` patterns counts down like `Succ`s. On an `Int`, number patterns can be negative, `(-1)`: a match on `Int` numbers splits on the sign (`OfNat` or `NegSucc`) first, so an arm with a variable or `_` knows the sign of the argument in the branch where it is all that matches, but still nothing about its size. On a `Fin n`, a number pattern is `FZero` or `FSucc` around the one below (`2` is `FSucc (FSucc FZero)`), so it mixes with those patterns and a match on `0`, `1` and `2` of a `Fin 3` is complete (leave out `1` and the error names it: "no arm matches 1"); one not below a known n is `E-FIN-LITERAL` ([`Fin` literals](#fin-literals)). Arms are tried from top to bottom. `()` with a right-hand side matches the unit value; without one, it says the argument's type has no values, and the arm needs no right-hand side. Inside another pattern (`let ((), n) := …`, `| (x, ()) => …`, nested), `()` in an arm with a right-hand side is the unit pattern where what it matches is known to be `()`, and is otherwise absurd; at a type with values that isn't `()` it is `E-NOT-EMPTY`, and `_` ignores the part (`examples/accept/unit-pattern-in-tuple.sw`, `examples/reject/unit-pattern-in-tuple-not-unit.sw`):

```
def absurd: Void -> a
  | ()
```

An equation of two different constructors has no values either, so `()` matches it too: `theorem robotNotBox: Robot = BoxLeft -> Void` is `| ()`, as Lean's `nomatch h` and Agda's absurd pattern. Where the equation is a hypothesis already in scope (a lambda's parameter, or refined by a `match`), `cases` proves any goal from it in one word (see [`cases`](#cases), "Closing a case"). `Robot = Robot` has a value, so `()` there is `E-NOT-EMPTY` (`examples/accept/absurd-distinct-constructors.sw`, `examples/reject/absurd-same-constructor.sw`).

The type is the one the argument has in that arm, after the arm's other patterns and computing: with `beats Rock Rock` computing to `False`, `h: beats Rock theirs` is `False = True` in an arm for `Rock`, so `| Rock, ()` needs no right-hand side. A row's constructor patterns are matched before its `()`, wherever it comes, unless the `()`'s type is empty as it stands (`Void`, an indexed family such as `Fin 0`, or an equation of different constructors), which is refuted at once. On one line, `| Rock, () | Paper, ()` reads `() | Paper` as an or-pattern, and the error says to start the next `|` on a new line. A `match` alternative takes `()` with no `=>` the same way, with one scrutinee or several (D3534, `examples/accept/absurd-match-arms.sw`):

```
theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs, h with
    | Rock, ()
    | Paper, ()
    | Scissors, _ => rfl
```

An arm for such a case can also be left out: see "Impossible cases" under [`match`](#match).

Implicit and auto parameters are in scope by name in every arm, wherever they appear in the signature:

```
def get: (xs: List a) -> (i: Nat) -> [auto ok: i < List.length xs] -> a
  | [], i => Void.absurd (Bool.falseNotTrue ok)    -- ok: i < 0, which computes to False = True
…
```

List patterns: `[]` is `Nil`, and `[p, q, r]` is `Cons p (Cons q (Cons r Nil))`, by identity with the library's `List` (a user's own `Cons` doesn't change it), wherever a pattern is allowed (arms, `match`, `let`, lambdas). Each element is a pattern; a constructor element takes its arguments without brackets (`[Some a, None]`), and `(-k)` works as in tuples. A list pattern may end in a rest: `[x, y, ..rest]` is `Cons x (Cons y rest)`, where `rest` is any pattern (`..rest`, `.._`); `..` must be last and appears once, and `[..p]` is just `p` (`examples/accept/list-rest-patterns.sw`). Patterns take `..` only last (`[..init, last]` is `E-PARSE`: use `List.last` or `List.reverse`). There is no `x :: xs` form, in patterns or expressions. A list pattern is refutable like `Cons`, so in `let` the pattern must still cover the type (`let [a, b] := xs` is `E-LET-REFUTABLE`). A missing case is reported as the constructor that lacks it (see `examples/reject/list-pattern-missing-longer.sw`).

List spreads: in a list expression, `..xs` joins the list `xs` in at that place. `[a, b, ..xs]` is `Cons a (Cons b xs)`, the same as the pattern; `[..xs, y]` is `xs ++ [y]`, `[..xs, ..ys]` is `xs ++ ys`, and `[a, ..xs, b, ..ys]` is `Cons a (xs ++ Cons b ys)`. `..` may come in any position and any number of times; everything after it up to the next `,` or `]` is its list (`[x, ..f y z]`, `[x, ..ys ++ zs]`), and `[..xs]` is `xs`. A final spread is a plain `Cons` chain (no `++ []`), so `rfl` and equations see through it; a spread elsewhere is a call of `List.append` (the library's, by identity, as list literals use the library's `Cons`), which is stuck on an unknown `xs`. Abilities in the elements and spreads run left to right as written. A tail that isn't a list is `E-TYPE-MISMATCH` with a note that an element is written without `..`. The facts of `omega [..]` and `ring [..]` take no spread. Goals and messages print an open `Cons` chain the same way, `[x, ..xs]`, and a closed one as `[1, 2, 3]`; `++` stays `++` (`examples/accept/list-spread.sw`, `docs/proposals/list-spread.md`).

`NonEmptyList` brackets: where the type a list literal is checked against is a `NonEmptyList a` (`import Std (NonEmptyList)`), the brackets build one, and on a `NonEmptyList` the list patterns match one (D2396, docs/proposals/non-empty-lists.md §7; `examples/accept/non-empty-list-brackets.sw`). The first item that isn't a spread is the `head` and the items after it are the `tail`, a `List` literal: `[1, 2, 3]` is `{ head = 1, tail = [2, 3] }`, `[x, ..xs]` is `{ head = x, tail = xs }`, and spreads before the first item are put in front with `NonEmptyList.prependList` (`[..xs, y]` is `NonEmptyList.prependList xs { head = y, tail = [] }`). The term is that record, the same as writing it in braces. `[]` there is `E-NONEMPTY-EMPTY` ("a `NonEmptyList` can't be empty"), and a literal of spreads only (`[..xs]`) is `E-TYPE-MISMATCH`, since every list spread may be empty, with a note to write `xs.toNonEmpty`. A spread is a `List`; to spread a `NonEmptyList`, write `..ys.toList`. In a pattern, `[p, ..q]` on a `NonEmptyList` is `{ head = p, tail = q }`, with `q` a list pattern on the tail: `[x]` is `{ head = x, tail = [] }` and `[x, y, ..rest]` is `{ head = x, tail = [y, ..rest] }`, so `[x, ..rest]` alone covers every value, and an arm `[]` is `E-NONEMPTY-EMPTY`. A missing case is named in brackets too (`[_]`), and goals and messages print a `NonEmptyList` as brackets. Only the expected type decides: with nothing expected, a literal is a `List` (`let xs := [1, 2]` is a `List Nat`; `[3, 1].maximum` is `List.maximum`, an `Option`), and a pattern's type must be known where it is matched, as for record patterns.

Or-patterns: `p | q | …` matches if any alternative does, in arms and `match` alike.

```
def commandOfChar (char: Char): Option Command :=
  match char with
    | 'k' | 'w' => Some (Move North)
    | 'j' | 's' => Some (Move South)
    | _ => None

def warm: Colour -> Bool
  | Red | Yellow => True
  | Green | Blue => False
```

The alternatives are on one line: a `|` that starts a line starts the next arm. With several patterns, `|` binds tighter than `,`, so `| 0 | 1, Red => …` is `(0 | 1), Red`; brackets put an or-pattern inside another pattern, `Some ('a' | 'b')`, `(0 | 1, x)`, `[_, 'a' | 'b']`. An alternative can't bind a variable (`_` is fine), as in Scala: `| Some x | None => …` is `E-OR-PATTERN-BINDS`; match the alternatives in arms of their own instead. An arm with an or-pattern is checked as one arm per alternative, in order, with the same body: so coverage counts each alternative, and a `_` arm after `| 'k' | 'w'` knows the value is neither (`examples/accept/or-patterns.sw`, `examples/reject/or-pattern-binds.sw`).

### Declaration order

Declarations can be written in any order: every top-level name (definitions, data types and their constructors, abilities and their operations) is visible throughout its module. So `main` can come first and its helpers below it. The compiler checks each declaration after the ones it refers to, and otherwise in source order; errors are reported, and tests run, in source order. Definitions that refer to each other are checked together, and their termination is decided together (docs/proposals/mutual-recursion.md):

```
def isEven: Nat -> Bool
  | 0      => True
  | Succ n => isOdd n

def isOdd: Nat -> Bool
  | 0      => False
  | Succ n => isEven n
```

- **A type can't mention a definition it's checked together with** (`E-MUTUAL-SIGNATURE`): the definitions in a cycle are finished all at once, and a type may only use what's finished. A proof about `isEven` belongs outside the cycle, where its type computes.
- **Inside a cycle, a definition must be given at least one argument** wherever it's used, so the termination checker sees what each call passes: `map isOdd xs` inside `isEven` is refused (`E-TERMINATION`, "used here without all its arguments"), `map (n => isOdd n) xs` isn't. Given some but not all of its arguments, it stands for a function of the rest, `f a b` for `x y => f a b x y`, and every call made through it passes the same `a` and `b`, while nothing is known about `x` and `y`. So it's accepted when an argument that gets smaller is among those given: `applyTo (sumWith n) acc` inside `sumWith`, which recurses on `n` (`examples/accept/partial-recursive-call.sw`). When the argument that gets smaller isn't given, it's `E-TERMINATION`, with a note saying so (`examples/reject/partial-recursive-call.sw`). Lean does the same for structural recursion: a recursive call needs its arguments up to the one it recurses on, and may leave out those after it. Outside the cycle, anything goes.
- **A `match` on a tuple of the parameters hides their parts from the termination checker**: in `match (xs, n) with | (_, Succ m) => f m xs`, `m` is a part of the tuple, not seen as a part of `n`, so the call is `E-TERMINATION`, with a note saying why. Match the parameters themselves, `match xs, n with | _, Succ m => f m xs`, or write clauses on them (`examples/reject/termination-tuple-match.sw`).
- **Data types that refer to each other are checked together**, like a tree whose children are a forest:

  ```
  type Tree: Type =
    | Node (label: Nat) (kids: Forest)

  type Forest: Type =
    | FNil
    | FCons (first: Tree) (rest: Forest)
  ```

  They must have the same parameters, with the same names, and the same universe (`E-MUTUAL-PARAMETERS`), and their parameters can't mention each other (`E-MUTUAL-SIGNATURE`). Their fields can mention any of the types, but not their constructors (`E-MUTUAL-CONSTRUCTOR`): `(ok: kids = FNil)` in `Tree` is refused. None of them may occur to the left of an arrow in any of their fields (`E-POSITIVITY`), or inside another type except at a parameter that type only stores (see nested types, below). Propositions defined together can only be matched on to produce other proofs (`E-PROP-ELIM`). Functions over them are ordinary definitions that call each other: `size (Node n kids) = Succ (sizeForest kids)` is a smaller call, since `kids` is part of the tree.
- **A data type may contain itself inside an earlier data type** (a nested type), at a parameter that type only stores, as `List` stores its elements:

  ```
  type Packet: Type =
    | Number (value: Nat)
    | Packets (items: List Packet)
  ```

  `List Packet`, `List (List Packet)`, `Option (Packet, Nat)`, `Vec Packet n`, `All (t => Typed t r) bs`, and a member of an earlier group such as `Tree Packet` (with `Tree` and `Forest` defined together) are all allowed. Refused (`E-POSITIVITY`), with the reason named: a type whose parameter is a function's input (`Neg (a) = MkNeg (consume: a → Nat)`), in an index, in another parameter's type (`List.Member a xs`), or inside an equation or a definition; a definition standing for a type (`Children := List`), which isn't looked into; a quotient (`Map`, `Set`); and a field whose type mentions an earlier field that holds the type (`(n: Fnat) (m: Fnat) (same: n = m)`, `(kids: List T) (ok: kids.length = 2)`). Functions over a nested type recurse structurally through a helper for the container, defined together with them: `size (Packets items) = Succ (sizeList items)`, `sizeList (Cons p rest) = size p + sizeList rest`. A proposition with a nested field can only be matched on to produce other proofs (`E-PROP-ELIM`). Derived `==`, `<` and `${…}` are generated for a type nested in `List`, `Option` and pairs (and those inside each other, `List (List T)`, `Option (T, Nat)`), with a helper for each container defined together with the type's function, as `sizeList` is with `size`: `Packets [Number 1] == Packets [Number 1]`, `Number 9 < Packets []`, `"${Packets [Number 1, Packets []]}"` is `Packets [Number 1, Packets []]`. Through another container (`Vec`, a type of the program, an earlier group) there are none, and the note names the container (`examples/accept/nested-data-derived.sw`, `examples/reject/nested-data-derived-vec.sw`).

  **Generated size and induction** (`examples/accept/nested-data-induction.sw`). A nested type `T` in `Type`, not defined together with others, that holds itself (at its own parameters) inside `List`, `Option`, pairs, or another data type that isn't defined together with others and isn't nested itself (`Vec`, a type of the program), at any depth, gets these, unless the module declares the name itself:

  - `T.size`: one more than the sizes of the fields that hold `T`, counting a container's constructors too, so `Packet.size (Packets [Number 1])` is 4 (`Packets`, `Cons`, `Number`, `Nil`).
  - `T.induct`: one case per constructor, named after it in lower case, taking the fields and then a hypothesis for each field that holds `T`: `motive x` for a field `x: T`, the container's `All` of the motive for a field inside one, composed for nesting (`List.All (List.All motive) rows`, `Option.All (Pair.All motive (x => Unit)) next`). For `Packet`: `(motive: Packet → Prop) → ((value: Nat) → motive (Number value)) → ((items: List Packet) → List.All motive items → motive (Packets items)) → (x: Packet) → motive x`. Indices go to the motive: `(motive: (i0: Nat) → Ranked i0 → Prop) → …`.
  - `T.inductMem`, when a field is a `List T` or an `Option T` itself: the same, with that field's hypothesis for every member, `(q: Packet) → List.Mem q items → motive q`, or `(q: T) → next = Some q → motive q` for an option.
  - `D.All` for a container `D` declared in the same module that has no `D.All` of its own: `Bag.All: [a: Type] → (a → Prop) → Bag a → Prop`, a predicate for each parameter that the type only stores and that is a `Type`, true when every value of that parameter in it satisfies it. It can be used above the type that makes it. A container from elsewhere (`Vec`, a library type) gets a hidden one, which `T.induct`'s type shows as `T.%Vec%All`. The library's are `List.All`, `Option.All` and `Pair.All`, with `List.memOfAll` and `Option.memOfAll` to turn them into membership.

  With `decreasing T.size x`, a recursive call on an element of a `List T` field, brought into scope by `attach`, needs no proof: `auto` finds the element's `isIn` (or a hypothesis `List.Mem y xs`) and the lemma generated for that field (`| Packets items => 1 + (items.attach.map (e => Packet.depth e.value) |> .foldLeft 0 Nat.max)`). An `[auto]` argument is proved the same way: `[auto lt: Packet.size q < Packet.size (Packets items)]`, with `h: List.Mem q items` (or `q ∈ items`) in scope. When it can't be, the message shows the goal as it computes, which mentions a helper the compiler generates (`Packet.%m1%size items`), and a note says so. For an element of an `Option T`, `List (List T)` or another container there's no such lemma; write it by hand (`examples/accept/nested-data.sw`). Nothing is generated, without a message, for types defined together, a type inside a member of a group (`Tree Big`), a type in a container that is nested itself, or in a function's result, a parameter that isn't a `Type` (`All (t => Typed t r) bs`), or an index. The details: [the proposal, As built (stage 3)](proposals/nested-data-types.md#as-built-stage-3).

  The rule and why it's sound: [docs/core.md](core.md#nestable-parameters), [the proposal](proposals/nested-data-types.md). Examples: `examples/accept/nested-data.sw`, `nested-data-shapes.sw`, `examples/soundness/nested-*.sw`.
- **A data type can't be in a cycle with a definition, and an ability can't be in a cycle at all** (`E-MUTUAL-KIND`): that would be induction-recursion, or Landin's knot.
- **A name in the module takes priority over a type variable.** In `def length: List a -> Nat`, `a` is a type variable only if nothing in the module (or an import) is called `a`; otherwise it means that declaration, wherever it is, with a warning (`W-MODULE-NAME`) pointing at both. Write `[a: Type] -> List a -> Nat` to make it a type variable regardless.
- **`auto` only uses decision procedures (definitions marked `instance` returning `Decidable …`) that are already checked and written above the use.** One written above that's still waiting for something below to be checked isn't available yet; `E-AUTO-NONE` says which case applies. Passing the procedure explicitly makes it an ordinary dependency, checked first.
- **`auto` limits how deeply decision procedures depend on each other.** A procedure that needs other decisions (`Decidable.or` needs one for each side) uses one level of depth for each, and the search stops after eight (`E-AUTO-NONE`). A decision of a smaller part of the same proposition costs only a fraction of a level, so a long chain of them is not limited by the eight: `n ∈ [1, 2, …]` unfolds to `1 = n ∨ 2 = n ∨ …`, and `auto` proves it for a literal list of 100 elements as quickly as for 9, and says `E-AUTO-FALSE` when `n` isn't in it. The chain is bounded at a couple of thousand steps. Examples: `examples/accept/auto-membership-long-list.sw`, `examples/reject/auto-membership-absent.sw`.

## Definitions in detail

The design is in [the proposal](proposals/declaration-syntax.md). Until 18 October 2026 definitions were a signature line followed by equations (`length : List a -> Nat`, then `length Nil = 0` …), with `->` in lambdas and arms and `let x = e`; that syntax is gone. Some older documents still use it. A header with no body (`def f : T`) is allowed only for the prelude's primitives; anywhere else it is `E-MISSING-DEFINITION`.

```
definition ::= "export"? ("def" | "theorem" | "instance") name binder* ":" type body
body       ::= ":=" expr | arm+
arm        ::= "|" pattern ("," pattern)* ("=>" expr)?
binder     ::= "(" name+ ":" type ")" | "[" name+ ":" type "]"
             | "[" "auto" name ":" type "]" | "[" "auto" type "]" | "(" ")"
interface  ::= "interface" Name binder ("=" "{" fields "}")
test       ::= "test" string ":=" expr
```

```
def total (k: Nat) (lines: List Text): Nat := lines.map (joltage k) |> .sum

def length: List a -> Nat          -- arms: one pattern per argument after the colon
  | []        => 0
  | [x, ..xs] => Succ (length xs)

def total (k: Nat): List Text -> Nat    -- named parameters, then arms
  | []        => 0
  | [l, ..ls] => joltage k l + total k ls

def main(): {IO} () := report (solve IO.readAllLines())

test "parse" := parseBank "102" == [1, 0, 2]
export def identityNat (n: Nat): Nat := n

let x := 1 + 2                       -- in a block
(let x := 1 + 2; x * x)              -- an expression
x => x + 1                          -- a lambda
(x: Nat) (y: Nat) => x + y          -- a lambda with typed parameters
[a: Type] (x: a) => x               -- a lambda with an implicit parameter
match xs with
  | [] => 0
  | [x, .._] => x
handle prog() with
  | return x    => [x]
  | choose u, k => List.append (k True) (k False)
```

- `->` is only the function type. `=>` separates a pattern or parameter from what follows (arms, `match`, handlers, lambdas). `=` is only equality; `:=` gives a body or a `let` its value. Using `=` there is `E-DEF-EQUALS`.
- Parameters before the colon have the same name in every arm and can't be matched. Parameters after the colon are matched by the arms. `()` before the colon is an unused unit parameter (it becomes `_`).
- A lambda's parameters are names, patterns, or typed parameters written as a definition's are: `(x: Nat) => …`, `(x y: Nat) => …`, mixed freely (`x (y: Nat) => …`). A typed parameter takes its type from the annotation, which in a checked lambda must agree with the expected parameter type (else `E-TYPE-MISMATCH`, pointing at the annotation), and which lets a lambda with no expected type be inferred: `(p: Person) => p.name` has type `Person -> Text`. A typed parameter can't also be a pattern, but a pattern can be given a type: `((index, shape): (Nat, Shape)) => index + shape.size` is an explicit parameter of the written type, taken apart by the pattern (tuple, record, constructor, list or nested), so the variables it binds have known types for dot notation. The annotation goes inside the brackets after the whole pattern, and a pattern that doesn't fit the type is an error at the pattern (`examples/accept/lambda-pattern-annotations.sw`, `examples/reject/lambda-pattern-annotation-shape.sw`). Examples: `examples/accept/lambda-annotations.sw`. A lambda with no expected type whose body may perform abilities returns a computation in the row its body works out, closed at the abilities it performs, as if written: in a `{Random}` function, `let later := () => roll 4` is `() -> {Random} Nat`, and `n => (log n; roll n)` is `Nat -> {Log, Random} Nat`. Calling it where those abilities aren't allowed is `E-ABILITY` at the call; passing it where a pure function is expected is `E-TYPE-MISMATCH`. One bound by `let` whose body performs nothing (`let pick := (n: Nat) => xs.filter (x => x == n)`, whose callback is pure) is a pure function, and its calls are plain calls wherever they are (`examples/accept/let-lambda-pure-call.sw`). Examples: `examples/accept/lambda-inferred-effects.sw`, `examples/reject/lambda-inferred-ability-not-allowed.sw`, `examples/reject/lambda-inferred-effectful-as-pure.sw`.
- A lambda may bind implicit and `auto` parameters, written as a header writes them: `[a: Type] (x: a) => x`, `[a b: Type] => …`, `[auto h: Ord a] => …`, `[auto Ord a] => …` (docs/proposals/lambda-syntax.md §4.3, D91). Each parameter has a mode, explicit, implicit or auto, matching the three kinds of function type. Checked against a function type, a `[a: T]` parameter takes the type's leading implicit parameter (an `[auto h: P]` one its leading auto parameter), binding it by its own name so the body can use it; the written type must agree with the expected one. It never has a parameter introduced in front of it: against anything else (an explicit function type, an auto parameter where an implicit one is written or the reverse, a type that isn't a function) it's `E-TYPE-MISMATCH`, "this lambda takes an implicit parameter first, but the expected type `Nat -> Nat` takes an explicit one". Inferred with no expected type, it has an implicit (or auto) function type: `let pick := [a: Type] (x: a) (y: a) => x` is `[a: Type] -> a -> a -> a`, and each use of `pick` fills in `a`; such a lambda isn't applied to an unknown where it's written, only where it's called. As a definition's whole right-hand side (every arm's), it takes the signature's implicit parameters after the last pattern itself, rather than the signature putting them in scope: `def idf: [a: Type] -> a -> a := [a: Type] => (x: a) => x`. A lambda without `[…]` parameters is unchanged: checked against `[a: Type] -> a -> a`, `x => x` has the implicit parameter introduced for it, under a name it can't use. `[a] => …` (no type) is `E-PARSE`, "a parameter needs a type". Examples: `examples/accept/lambda-implicit-parameters.sw`, `examples/reject/lambda-implicit-mode-mismatch.sw`, `examples/reject/lambda-auto-mode-mismatch.sw`.
- A lambda is a run of parameters followed by `=>`: `x => e`, `x y => e` (curried), `_ => e`. `x => y => e` is the same function as `x y => e`, also where there is no expected type: a `let`-bound `x => y => x + y` is inferred as `x y => x + y` is (SW-910, `examples/accept/lambda-nested-arrows.sw`). A parameter is a lower-case name, `_`, a typed group (`(x: A)`, or `[a: A]`, `[auto h: P]`), or a pattern in brackets (`(a, b)`, `(MkPair a b)`, `{ name, .. }`); `(a, b) => e` is one pair taken apart, not two parameters (for two, write `a b => e`). A constructor or number parameter needs brackets too: `(Trivial) => …`. A lambda is a whole expression only: after `:=`, `=>`, `then`, `else`, `|>`, an opening bracket or a comma, a record field's `=`, or at the start of a block line. As an argument or an operand it needs brackets. There is no backslash form. A lambda takes no result type: `(x: A): B => e` is `E-PARSE`, "a lambda doesn't take a result type"; annotate the body, `(x: A) => (e: B)`, or the `let`, `let f: A → B := x => e` (`examples/reject/lambda-result-type.sw`, `examples/accept/lambda-result-annotation.sw`).

> **Lambdas used as arguments need brackets:** `map (x => x + 1) xs`. Without them, `map x => …` is a two-parameter lambda whose first parameter is named `map`. A lambda with two or more parameters whose first parameter hides a function in scope gets the warning `W-LAMBDA-SHADOW`, and an error inside it gets a note saying to bracket the lambda. Example: `examples/accept/lambda-shadow.sw`, `examples/reject/lambda-forgotten-brackets.sw`.

- A handler clause is `| op x, k => body`: the operation's argument, then the continuation's name. The argument is one atomic pattern, so bracket a tuple: `| op (a, b), k => …`.

**Layout.** Let *D* be the column of the declaration's `def`, `theorem` or `export`.

1. Comments and blank lines never matter for layout.
2. The header may continue on later lines, each indented more than *D*.
3. A `:=` body is on the header's line, or a block on the next line indented more than *D*.
4. Arms start on their own lines, not on the header's line. Each arm's `|` starts a line, and all of them are at one column *A*, more than *D*. A `|` between *D* and *A* is an error.
5. An arm's body can continue on lines indented more than *A*. A line at column *A* or less ends the arm. So a `match` or `handle` inside an arm must indent its own `|`s more than *A*; a `|` at column *A* is always the definition's next arm.
6. The definition ends at the first line at column *D* or less. Any other token at column *A*, or between *D* and *A*, is an error.
7. Inside `( )`, `[ ]` and `{ }`, layout ends nothing. A `|` in `{State s | e} B` belongs to the row.

### Local definitions

A `def` or `theorem` may stand in a block wherever a `let` may (the body of a definition, an arm, a `match` alternative, a lambda body, a `test`). It has the same form as at top level, arms and all:

```
def sumTo (n: Nat): Nat :=
  let start := 0
  def go: Nat -> Nat -> Nat
    | Zero, acc => acc
    | Succ k, acc => go k (acc + Succ k)
  go n start
```

- **Scope is top-down.** A local definition sees the parameters, pattern variables and earlier `let`s above it, and is visible to the lines below it. A later local definition or `let` of the same name shadows it, as a `let` does.
- **Consecutive local definitions form a group**: each may use the others in the group (and itself), so `isEven` and `isOdd` can be written one after the other.
- **Each is lifted** to a top-level definition `sumTo.go`. It takes as leading parameters the outer variables it uses, and the ones their types mention (a proof `ok: i < 5` is captured together with `i`). A captured implicit or auto parameter stays implicit or auto. A local definition and its owner may call each other, and termination is checked on the lifted program, as for any definitions that call each other.
- **Parameter order.** The captured variables come in the order they are written: the header's parameters (before the colon), then the arm's pattern variables from left to right, then `let`s and earlier local definitions, each moved later only when a type needs a variable that comes after it. So in `| Cons line rest, c, Succ k, d => def left: Nat -> Bool | …` a `left` that uses `rest`, `k` and `d` is `reach.left rest k d`, then its own argument (`reach.left rest k d c`), whatever order the compiler splits the arguments in. Lifted `match`es take their variables in the same order. A call with a wrong argument shows the definition's whole signature (`examples/reject/local-def-wrong-order.sw`). Examples: `examples/accept/local-def-capture-order.sw`.
- **Naming from outside:** `sumTo.go`, and `f.go.inner` for a definition inside `go`. Names are unique within one top-level definition (`E-DUPLICATE`), even if a later one shadows an earlier one, because the lifted names are all `f.name`.
- **Lemmas:** a local `theorem goZero (a: Nat): go 0 a = a := rfl` about a local function works when that function doesn't call its owner (it must be finished for the lemma's type to compute). If the function calls its owner, it isn't finished while the owner is checked: a proof that needs it to compute fails (with a note suggesting a top-level theorem about `f.go`), and a lemma whose type mentions it is `E-MUTUAL-SIGNATURE`.
- **Limits:** a recursive local definition can't be `{Partial}` (`E-LOCAL-DEFINITION`; define it at top level). A local definition in a cycle with its owner, passed unapplied, is given only what it captures, so it's refused (`E-TERMINATION`) unless that includes something that gets smaller (`examples/accept/partial-recursive-call.sw`). A block must end with an expression (`E-PARSE`).
- There is no `where` clause: after a body or the last arm it is `E-WHERE`, which points to local definitions.

Examples: `examples/accept/local-defs.sw`, `examples/accept/local-defs-effects.sw`, `examples/extract/local-defs.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 3.

**Exact arity.** Every arm has exactly one pattern for each explicit argument after the colon. These are counted after unfolding definitions, up to the first thing that isn't a function type (such as an ability row). So `def f: Nat -> Nat -> Nat` needs `| Zero, y => y`, not `| Zero => y => y`. Fewer patterns is `E-ARITY`, as is a different number in different arms. A `:=` body has no arity rule. Implicit and auto arguments after the colon aren't matched; they're in scope by name.

**`E-DUPLICATE-PARAMETER`.** The names of the header's parameters, and of the implicit and auto parameters after the colon, must all be different.

## Namespaces and imports

Names are grouped into namespaces (docs/proposals/namespaces.md). The library is `Std`. A program sees its **prelude** without asking (docs/proposals/prelude-slim.md §3): the types built-in syntax needs, `Nat`, `Int`, `Bool`, `Char`, `Text`, `List`, `Pair`, `Unit`, `Void`, `Not`, `And`, `Or`, `Exists`, `Decidable`, plus `Option`, `Result` and `Ordering`; the interfaces `DecEq`, `Ord`, `Add`, `Mul` and `Show`; the ability `IO`; and `not`. A prelude type comes with its own declaration: its constructors (`Cons`, `List.Cons`), its record fields, an ability's operations (`IO.print`, `IO.readLine`, `IO.readAll`) and an interface's methods (`Ord.compare`). **The rest of its namespace needs an import**: `List.map`, `Nat.addComm` and `IO.readAllLines` need `import Std (List, Nat, IO)`, and without it the error says so ("`List.map` needs `import Std (List)`"). `Std.List.map`, written in full, always works. **Dot notation and pipes need no import**: in `xs.map f` and `xs |> .map f` the value's type picks the namespace. Other library types (`Map`, `Set`, `Vec`, `Array`, `Fin`) aren't in the prelude: even the type's name needs `import Std (Map)`. `auto` and instance search see the whole library, whatever is imported.

**`Array a`** (`import Std (Array)`, D2508; docs/proposals/arrays.md) is a sequence with constant-time `get`, `getOr`, `getLt` (with an `auto` proof that the index is in range), `set`, `push` and `size` when run, for indexed state updated in a loop; to proofs it is its list, `toList`. `xs.toArray` needs no import (dot notation). `set`, `push` and `pop` work in place when nothing else holds the array and copy otherwise; a run that makes many large copies says so at its end. See the guide, chapter 6, "Array".

```
import Std (List)
import Text (split, join)

def words (line: Text): List Text := split line ' '

def count (xs: List Nat): Nat := List.length xs     -- needs `import Std (List)`

def total (xs: List Nat): Nat := xs.sum              -- needs nothing
```

- **`namespace Day05`** is the first line of a file (only comments may come before it). It puts everything the file declares in the namespace `Day05`: `Day05.main`, `Day05.Range.size`, and the file is checked and run as that namespace (`stitchwort run` runs `Day05.main`). A file has at most one namespace line, and `Std` and the library's namespaces (`List`, `Text`, …) can't be used for it (`E-STD-NAMESPACE`, `E-NAMESPACE-RESERVED`). Without a namespace line, names have no prefix, as before. Design: [multi-file.md](proposals/multi-file.md).
- **A qualified name** is written without spaces: `List.length`, `Std.List.Cons`. Its first component is found like any name, or as a namespace (the file's own, then one imported by name, then a project's root namespace); `Std.…` always means the library. A prelude type used as a qualifier without an import reaches only its own declaration (`List.Cons`, `IO.print`); anything else in a library namespace (`List.map`, `Eq.sym`, `Map.insert`) needs `import Std (List)`, `import Std (Eq)` and so on, or the full `Std.Eq.sym`; dot notation (`p.sym`) needs neither.
- **A type owns a namespace** holding its constructors (`Shape.Square`), and so does an ability, holding its operations (`State.get`). Anything declared with a qualified name goes in that namespace: `Shape.area: Shape -> Nat`. A qualifier that names nothing makes a namespace of the file's own (`Geometry.double`). The library's namespaces can't be added to (`E-STD-NAMESPACE`), however they're written: `List.sum` and `Std.List.sum` are both refused. In a project, a namespace may add a function to another project namespace's type (`def Grid.probe` in `P.Spec` for `P`'s `Grid`): it is `P.Spec.Grid.probe`, and `grid.probe` finds it only in `P.Spec` and in files that `import P.Spec (..)` ([projects.md](projects.md#namespaces), [extending-types.md](proposals/extending-types.md)).
- **`import N (a, b)`** goes at the top of the file and makes `a` and `b` from namespace `N` usable without `N.`. Importing a type brings its constructors (or an ability its operations). A constructor may also be named itself: listed beside its type, `import N (Nat, O, S)`, it adds nothing, since the type already brings it; listed alone, `import N (S)`, it imports just that constructor, and neither its type nor the type's other constructors. An unknown namespace or name is `E-IMPORT-UNKNOWN`; importing a name the file also declares is `E-IMPORT-CLASH`.
- **An import item may be a namespace** (docs/proposals/import-aliases.md): `import Std (Eq)`, then `Eq.sym`; in a project, `import Aoc.Year2024.Day13 (Spec)`, then `Spec.fewestTokens` for `Aoc.Year2024.Day13.Spec.fewestTokens`. The item makes its last name a qualifier for that namespace and brings none of the names in it (that is `import Aoc.Year2024.Day13.Spec (..)`); `Spec` alone names nothing (`E-UNKNOWN-NAME`, with a note). Importing a project namespace counts as using it, so it is checked first. The module's own names come first: an item hidden by a declaration of the module's (`def Spec`) or by a namespace of its own (`def Spec.f`) is `E-IMPORT-CLASH`. An imported namespace never hides anything else silently: if its name also means something else here (another imported `Spec`, a type `Spec` from an import or a `(..)`, a project's root namespace, the prelude's `List`), each use is `E-AMBIGUOUS`, which lists the full names to write. Goals print the short form where it means the same declaration (`Spec.fewestTokens`). There is no `import M as A`: it is `E-PARSE`, with a note giving the item form.
- **`import M (x as y)`** imports `M.x` under the name `y` in this file; that item doesn't bring `x` (`import M (x, x as y)` brings both). It works for every kind of item: a definition or theorem (`import Std.List (length as count)`), a type or ability (`import Shop.Spec (Status as Owing)`: `Owing` is the type and `Owing.f` its namespace, and its constructors keep their own names, `Paid`, `Owing.Paid`), and a namespace (`import Shop (Spec as S)`, then `S.total`). The new name starts with a capital letter exactly when the old one does (`E-PARSE`). The rules are an ordinary import's: a declaration of the file's with the new name is `E-IMPORT-CLASH`; two items with the same new name are `E-AMBIGUOUS` where it's used; writing the old name gets a note giving the new one. Goals and messages write the new name where it means the declaration, so a printed goal pastes back; hover and go to definition on the new name, or on either name in the import, show the declaration itself. Hashes don't depend on the name used. `(..)` takes no `as`. `import N (..)` brings every name declared directly in `N`, below the names imported by name (`import List (..)`, then `map`, `filter`, …); it can't name the file's own namespace, `Std` itself, or a type of a project namespace (`E-IMPORT-WILDCARD`). An import's namespace is found without looking at the other imports, so a library namespace whose name isn't in the prelude is written in full: `import Std.Effect (Comp)`, `import Std.Map (insert)` (while `import List (map)` works, `List` being a prelude name). `import Std (List)` is how a file asks for a prelude type's namespace; it isn't a duplicate of the prelude.
- **In the editor**, an `E-UNKNOWN-NAME` that an import would fix carries it as data (the diagnostic's `data.import`, `{path, item}`), and the language server offers the quick fix "Add `import Std (Map)`": the item is appended to the file's `import` of that namespace if it has one, else a new line goes after the last `import` (or the `namespace` line).
- **In the editor**, an `E-NONEXHAUSTIVE` carries its missing cases as data (`data.missing`, `{arms, more}`: each arm's patterns as in "Missing cases", with `‹name›` where a constructor field has a declared name), and the language server offers the quick fix "Add the missing arms": one `| patterns => ?` line per case after the last arm of the `match` or equations, in the column of the arms, with variables the declaration doesn't already use.
- **Case split in the editor**: a code action with the cursor on a variable between an arm's `|` and `=>` (a function's equation or a `match` arm) whose right-hand side doesn't mention it: "Split `x` into its cases" replaces the arm with one copy per constructor of the variable's type, the variable written as the constructor's pattern (a list as `[]` and `[x, ..xs]`, a pair as `(a, b)`) with fresh variable names. The type comes from the checker's context at the arm's right-hand side; types without data constructors (functions, indexed families) offer nothing.
- **Split from a `?` in the editor**: a code action with the cursor on a `?` (or on a parameter's name in the header of a declaration whose body is a single `?`): "Split on `x`" for each variable in scope whose type is a data type without indices, not a proposition. It replaces the `?` with `match x with` and one arm per constructor (`| Succ n => ?`, `| [x, ..xs] => ?`), its arms indented under the line. If the `?` is the whole right-hand side of an arm of a `match` that doesn't match `x` yet and the arm doesn't bind `x`, `x` becomes a new scrutinee: the arm becomes one arm per constructor and each other arm gets `_` in the new column.
- **A short name** means, in order: a local variable, the file's own declaration (or a constructor or operation of the file's own type or ability), an import by name, a name from an `import N (..)`, or the default. The first that has it decides, so a file can define its own `length` or `Option`; hiding `Option` hides its `Some` and `None` too (they're still `Std.Option.Some`). Two different things at the same level are an error only where the name is used (`E-AMBIGUOUS`): write the full name.
- **A project** is a folder with a `stitchwort.yaml` (empty is fine; `sources: [src, lib]` lists the folders to read, default `src`; `audit: allowed-axioms:` and `check: open-goals:` are the other keys, see [Auditing theorems](#auditing-theorems-stitchwort-audit) and [Goals](#goals-)). Every `.sw` file under them starts with a `namespace` line, and files with the same namespace are one module: their declarations are all visible to each other, in any order, but each file has its own imports. Namespaces use each other by `import` or by writing the name in full (`Lib.Range.size`, no import needed); a cycle between namespaces is `E-NAMESPACE-CYCLE`. `stitchwort check`, `test` and `run NAME` look for the project from the current folder up (or take `--project DIR`); a file given by path (`stitchwort run hello.sw`) is checked on its own, using only the library.
- **Syntax always means the library's**: `+`, `==`, `++`, `if`, literals and `()` don't depend on what names a file declares.

## Type synonyms and bracket layout

**Type synonyms.** `type Grid = List (List Nat)` is `def Grid: Type := List (List Nat)`: a transparent name, interchangeable with what it stands for, with its own namespace (`def Grid.rolls (g: Grid) …`, then `g.rolls`). Parameters are written as binders, `type Matrix (a: Type) = List (List a)`, and the type can be a tuple, `type Point = (Nat, Nat)`. After `=`, `{` starts a record and `|` a sum type's constructors (each constructor starts with its own `|`, even a single one: `type T = | Foo (x: Nat)`); anything else is the type. `type T = A | B` and `type T = Foo (x: Nat)` look like sums without their `|`, so they're `E-PARSE` with a note saying so (`examples/accept/type-synonyms.sw`, `examples/reject/type-synonym-*.sw`). A synonym can't be recursive: `type A = B` with `type B = A` leaves neither with a type to stand for (`E-SYNONYM-CYCLE`, `examples/reject/synonym-*.sw`).

**Brackets continue lines.** Inside `[ ]`, `( )` and `{ }`, a line starting with `,` or a closing bracket continues the bracket however far left it starts, so a list can be laid out with leading commas (`examples/accept/list-literal-layout.sw`). A trailing comma is allowed in list, tuple and record expressions and patterns, and in a record declaration's fields. Even in column 0, such a `,` or closer continues the bracket rather than starting a declaration; a declaration keyword (`def`, `type`, …) in column 0 still starts one, so a missing closer is reported where it should be. The house style for a bracket that spans lines is a comma at the end of each line, no trailing comma after the last item, and the closer on its own line in column 0:

```
type Person = {
  name: Text,
  age: Nat
}
```

## Indexed data types

docs/proposals/indexed-families.md §7; `examples/accept/indexed-families.sw`.

- **Indices go after the header's colon**, parameters before it: `type Vec (a: Type): Nat -> Type =`. They can be named, `(len: Nat) -> Type`, and a later one's type can mention an earlier one, `(n: Nat) -> Fin n -> Type`. An index's type must fit in the type's universe, as a field's must, so a type indexed by types is written `Ty: Type -> Type 1` (`E-UNIVERSE` otherwise). Records and synonyms have no indices (`E-RECORD-INDICES`, `E-PARSE`).
- **Each constructor states its result type** after `:`, the type applied to its parameters exactly as declared, then indices: `| VCons (x: a) (xs: Vec a n): Vec a (Succ n)`. `Vec Nat 0` in `Vec (a: Type)` is `E-TYPE-MISMATCH`. Without indices the result type is optional.
- **Implicit fields.** `[n: Nat]` among a constructor's fields is an implicit field. In a constructor of a type with indices, an undeclared lowercase name (`n` above) becomes an automatic implicit field, as in a signature; a use in an index counts (`FZero: Fin (Succ n)` binds `n: Nat`). Automatic fields go first, ordered by their dependencies; one whose type would mention a written field must be written out, after it (`E-IMPLICIT-FIELD`). Implicit fields are filled in by unification when building a value, or named: `VCons [n := k] x xs`.
- **`n + 1` and `Succ n` are the same index**: `+` computes on either side that is a number or a `Succ` (docs/core.md, "Numbers"), so `Vec a (n + 1)` is `Vec a (Succ n)`. A sum of two unknowns, `Vec a (n + m)`, doesn't compute: matching on it is stuck until `n` or `m` is matched (`E-INDEX-STUCK`).
- **In a signature**, a name used in an index is bound automatically even where it's also used as a value: `def head: Vec a (Succ n) -> a`, `theorem leToLeq: Le m n -> m <= n`.
- **Matching** needs no new syntax. Implicit fields are skipped in patterns, or matched by name, `VCons [n := k] _ _` (positional `[k]` isn't allowed). An arm may be left out only when its constructor can't be there (`head` has no `VNil` arm), or when another argument then has no possible constructor (`get: Vec a n -> Fin n -> a` has no `VNil` arm: there, `i: Fin 0`). A left-out arm that can be there is `E-NONEXHAUSTIVE`. It lists every such constructor, as arms to paste (see "Missing cases" under `match`). When the compiler can't tell (an index like `n + m` with `n` unknown, or a type to take apart), it's `E-INDEX-STUCK`: match on `n` first, or use a variable index. `()` works for a family with no possible constructor (`Even 1`). An arm that can never match is the warning `W-UNREACHABLE`, and isn't checked.
- **Running and exporting.** A family's values run like any data type's; its forced fields are stored, and its proof fields are erased. An `export` can't have a family anywhere in its inputs or result, directly, through a synonym, in a container or in a record field (`E-EXPORT`); a function may use one inside (`examples/extract/vec-inside.sw`).

## Records

A record declaration makes a new type with named fields (docs/proposals/records.md, stage 1). Two record types with the same fields are different types. An alias is a type synonym instead (above).

```
type Person = { name: Text, age: Nat }

-- Parameters, universes and dependent fields as for data types: a field's
-- type may mention earlier fields. Proof fields are erased.
type Sized (a: Type) =
  { items: List a
  , size: Nat
  , ok: List.length items = size
  }

def alice: Person := { name = "Alice", age = 30 }       -- every field once, in any order

def newborn (name: Text): Person := { age = 0, name }           -- `name` alone is `name = name`

def birthday (p: Person): Person := { p | age = p.age + 1 }       -- update: a new record

def describe: Person -> Text
  | { name, age } => name ++ " is " ++ Nat.toText age

def nameOf: Person -> Text
  | { name, .. } => name                 -- `..` ignores the other fields
```

- **A literal's type** is the expected one where there is one: a signature, an argument's type, or an annotation, `({ x = 0, y = 0 }: Point)`. Where its type isn't known yet where it's written (a `let` with no type, an argument whose parameter type is still to be inferred, as in `Some ({ … })` or `ns.foldLeft { enabled = True, total = 0 } step`), the literal **waits**, and is checked once something later in the declaration says its type: a later argument (`step: Tally -> Nat -> Tally` makes the accumulator a `Tally`), the other side of a comparison (`==`, `!=`, `=`, `<` and the rest; in `f 1 == Some ({ value = v })`, `f 1` says the type), the other operand of `++`, a `calc`'s goal, or how a `let` is used (docs/proposals/postponement.md, stage 2; `examples/accept/postpone-record-literal-argument.sw`, `examples/accept/postpone-effectful-record.sw`). **Only where nothing in the declaration says it** is the type the one record type in scope by its short name whose fields are exactly the literal's, in any order, with its parameters inferred from the fields (`let p := { row = 1, column = 2 }`, used only as a `Position`'s fields are): the field-name rule, applied at the end of the declaration. None, or more than one, is `E-CANNOT-INFER`, naming the candidates (`examples/accept/record-literal-inferred.sw`, `examples/reject/record-literal-without-type.sw`). The rule looks only at the literal's field names and the names in scope, never at types inferred elsewhere, so which type it picks doesn't depend on the order things are checked in (docs/proposals/records.md U6, "As built"). A number literal whose type isn't known yet waits too (postponement.md, stage 4), so in `[{ row = 1, column = 2 }].map (p => p.row) == [1]` with `row: Int`, `[1]` is a `List Int` once the rule makes `p` a `Position`. Something that needed the type before the end (a `match` on what is found in one of its fields, with a tuple pattern) can't wait for the rule: an implicit argument it left unsolved is `E-UNSOLVED` at the literal, naming the type the rule chose and saying to give it there or on the `let` (SW-946, `examples/reject/record-literal-type-late.sw`).
- **`e.name`** reads a field, or calls a function by dot notation: it looks `name` up in the namespace of `e`'s type `T`, finding the field or `T.name`, and passes `e` as `T.name`'s **first explicit argument** (`line.split ','` is `Text.split line ','`; `t.split` alone is `Text.split t`, plain partial application). Nothing is searched: if `T.name`'s first explicit parameter isn't a `T`, the call is `E-DOT-NO-RECEIVER` ("`Nat.firstFrom` doesn't take a `Nat` first, so `n.firstFrom` can't put `n` there"), with a note to call it in full. So a function meant for dot notation takes its main value first (see the [library convention](#pipe-forward-)). The definition of a function in `T`'s namespace that takes a `T`, but not first, gets the warning `W-RECEIVER-NOT-FIRST` (in a library file it is an error); `@[noReceiver]` before the `def` opts a helper out, for a function not meant to be called with `.` or `|>`. Implicit and `auto` parameters before the first explicit one are inserted as usual. A nickname's namespace is tried before what it stands for (`p: Price` tries `Price.show`, then `Nat.show`), also when the receiver is a call whose declared result type is the nickname (`(mk n).double` with `mk: Nat -> Meters` tries `Meters.double` first), and also when the receiver's type was inferred from one (with `codes: List Code`, `codes.map (code => code.numericPart)` finds `Code.numericPart`); a nickname's functions are found only where the value's type mentions the nickname, so a hand-written `digits: List Nat` or a literal `[1, 2]` looks in `List` only, and the error's note says so. `p.sym` on an equation finds `Eq.sym`. It's written without spaces around the `.`, binds tighter than application (`f p.name` is `f (p.name)`), and chains (`t.lead.name`, `(f x).age`). `e.f a` is elaborated as the prefix call `T.f e a` is: where nothing needs to run first, the call's result is compared with the expected type before `e` is checked in its parameter's place, so `def c: List Int := [1, 2].map (x => x)` checks, as `List.map [1, 2] (x => x)` does, and a literal receiver takes its type from the call. Dot notation needs `e`'s type only for the head that names the namespace (`List` for a list literal, whatever its elements), found by inferring `e` once and undoing that; the exceptions, which keep the dot reading (receiver first, its type fixed before the arguments are checked), are a receiver that can't be inferred on its own (`[1, 2].map (x => x).map f`: its lambda needs the expected type), a named argument, a call that performs operations (the receiver runs first, then the arguments as written), and `x |> .f`. Where `e`'s type isn't known yet, `e.name` **waits** until something later in the declaration says it, and is then elaborated as it would have been with the type known at once (docs/proposals/postponement.md, stage 2): `let value := ((index, item)) => item.value` followed by `List.sumBy pairs value` works, since the `let`'s use says what `item` is (`examples/accept/postpone-let-lambda-field.sw`), and so does a chain on it, `f => ((f.x 1).x 2).x 3`. A wait ends at the end of the application it was written in, or of the declaration; only if nothing in the declaration says the type is it `E-CANNOT-INFER` ("can't tell what `p` is, so can't look up `.name`"), and if the type turns out not to have `name`, the error is the one for that type, at `name`. What is decided from `e.name`'s type in the meantime is decided as for any value of unknown type: a number literal beside it (`p.x + 1`) waits too (stage 4). `people.map (p => p.name)` works without waiting, since `people` is checked first; so does `List.map people (p => p.name)`, which checks `people` first. In an application, a lambda written before the argument that gives its parameter type, and that can't be checked without it, is checked after the later arguments, also when a later argument's type mentions it (that argument may say what the lambda is); the library puts function arguments last, so this rarely matters. Only the checking order changes, not the order arguments are passed or run in). `name()` with no space is a call (see the call style above), and the dot applies to its result: `IO.readAll().lines` is `(IO.readAll()).lines`, and `f().g y` is `(f()).g y`. `f p .name`, with a space, is a method section instead ([Method sections](#method-sections)). See docs/proposals/namespaces.md §4.8.
- **An update** `{ e | f = …, … }` replaces some fields. A later field whose type mentions a replaced one must be replaced too (`E-RECORD-UPDATE`): `{ s | items = xs }` isn't allowed for `s: Sized a`, `{ s | items = xs, size = n, ok = proof }` is. An update may also change the record's type parameters, as Haskell's does: a parameter can change only if every field whose type mentions it is replaced. With `type Timed (a: Type) = { start: a, end: a, label: Text }`, `{ t | start = Int.toNat t.start, end = Int.toNat t.end }` turns a `Timed Int` into a `Timed Nat`, while replacing `start` alone is `E-RECORD-UPDATE`, naming the kept field `end` that fixes `a`. Where the update's type is inferred (a `let`), the update is first checked as written, so `{ t | start = 5 }` stays a `Timed Int`; only if that fails does a parameter only the new fields mention become a new unknown. A parameter that no replaced field mentions never changes (`examples/accept/record-update-type-change.sw`).
- **Record patterns** `{ f = p, g, .. }` work wherever patterns do, nested in constructors and other records, when the type of what they match is known (a parameter's from the signature, or a field's from the constructor around it). After `=`, a constructor pattern takes its arguments without parentheses: `{ items = Cons x xs, .. }`. As a constructor's argument a record pattern is written in brackets, `Cons ({ name, .. }) rest`, or, for a constructor declared with brackets, directly after it, `Some { name, .. }` (next).
- **Braces after a constructor: the declaration decides.** A constructor is declared in one of two styles, and its style says what braces after it mean, in expressions and patterns alike (docs/proposals/brace-syntax-review.md §5; D2481–D2485). It is never decided by field names or types, so no edit to a type's fields changes what working code means; only switching a declaration between the styles does.
  - **Declared with its fields in braces**, `| Meeting { title: Text, minutes: Nat := 30, room: Text }` (defaults after `:=`; implicit fields stay in square brackets before the braces, `| VCons [n: Nat] { x: a, xs: Vec a n }: Vec a (Succ n)`), the braces after `Meeting` name its fields (the next two bullets). Its explicit fields are all in braces or all in brackets: `| C (a: Nat) { b: Nat }` is `E-PARSE`. It can still be applied positionally, `Meeting "a" 30 "r"`, and with named arguments, `Meeting (title := "a") (room := "r")`.
  - **Declared with brackets**, `| Some (value: a)`, `| Cons (head: a) (tail: List a)`, `| Filling`, the braces after it are an ordinary record argument, as after a function: `Some { name = "tea", price = 3 }`, `Some { item | price = 4 }`, `Tagged { name = "tea", price = 3 } "hot"` (more arguments may follow), `readPackets Filling { unread = … }` (the next argument of `readPackets`), and the pattern `| Some { name, .. } => name`. They are `C ({ … })` without the brackets, which still works. Braces that name the constructor's fields (`Circle { id = "a", radius = 1 }` for a bracket-declared `Circle`) fail as a record literal does where a non-record is expected: `E-NOT-A-RECORD` when the first field's type is a known data type ("braces after `Circle` are its first argument, a `Text`, not its fields"), otherwise a type error at the call, `E-CANNOT-INFER` or `E-TYPE-MISMATCH`, with a note to write `Circle (id := …) (radius := …)` or to declare it with braces. A pattern's braces take no further arguments: `Cons ({ name, .. }) rest`.
  - **In argument position** a brace-declared constructor's braces stay an error (`f Circle { … }` is `E-PARSE`: write `f (Circle { … })`), and so does `Circle { … } x` (`E-PARSE`), while a bracket-declared one passes them on to the function or the constructor.
  - A function or type whose name is uppercase keeps its braces as a record argument (`AtR { q = …, n = 0 }`); a record type's own name isn't a constructor (`Item { … }` is `E-NOT-A-CONSTRUCTOR`; a record literal is written without its name).
  - `show` (and the derived `Show`) prints a brace-declared constructor by field name, `Meeting { title = "Standup", minutes = 30, room = "Blue" }`, and a record argument of a bracket-declared one without brackets, `Some { name = "tea", price = 3 }`, so its output is valid source. (A brace-declared constructor with implicit fields is printed positionally.)
- **Named-field constructor patterns** `C { f = p, g, .. }` on a constructor declared with braces match a `C`, naming its fields as a record pattern names a record's: `| Circle { id, .. } => id`, `| Circle { text = t, start = 0, .. } => t`, `| Dot { ref, id, start } => …`, `| Polygon { .. } => …` (docs/proposals/variant-fields.md §4). A field alone binds a variable of its name; fields come in any order, each once; without `..` every explicit field is named (`E-RECORD-FIELD`); a name `C` doesn't have is `E-UNKNOWN-FIELD`, listing its fields. It's the positional pattern with `_` for the fields left out, so it works wherever a pattern does (arms, `match`, `let`, bracketed lambda parameters, nested in other patterns) and coverage is the positional pattern's. Braces take no further arguments (`C { … } p` is `E-PARSE`); a record as the constructor's argument is `W ({ name, .. })`, or by field, `W { person = { name, .. }, .. }`. Implicit fields aren't named in braces (match them positionally, `VCons [n := k] _ _`). When a one-field constructor's field holds a record that has the field names given too (`Wrap { value = n, .. }` where `Wrap`'s one field holds an `Item` that has a `value`), the pattern still names the constructor's field, with the warning `W-RECORD-ARGUMENT`. In expressions, braces after a constructor declared with braces name its fields too (next bullet). Examples: `examples/accept/ctor-field-patterns.sw`, `examples/accept/ctor-braces-record-argument.sw`, `examples/reject/ctor-fields-*.sw`, `examples/reject/ctor-braces-*.sw`.
- **Named construction** `C { f = e, g }` builds a `C` declared with braces by its fields, wherever an expression goes (`Circle { ref = 1, id = "a", text = "t" }`, `Dot { id, ref = 2 }`; docs/proposals/variant-fields.md §4.5). Fields come in any order, a bare `f` is `f = f`, and every explicit field without a default is given once: an unknown name is `E-UNKNOWN-FIELD` (listing the constructor's fields), a missing one `E-RECORD-FIELD` ("this `Circle` is missing `text`"), one given twice `E-RECORD-FIELD`. It is the positional application with the explicit fields in declaration order (`Circle 1 "a" "t"`), so the term is the same. Implicit fields are filled by unification as in a positional application (`VCons { x = 1, xs = VNil }`); naming one is `E-UNKNOWN-FIELD` with a note to write `VCons [n := e] …`. A proof field is an explicit field and is given (`MkPos { n = 3, ok = omega }`). When the constructor's one field holds a record, `Tea { name = "tea", price = 3 }` is `E-UNKNOWN-FIELD` with a note to bracket the record, `Tea ({ … })`, or to name the field, `Tea { item = { … } }`. In a computation the field expressions run in the order written, as for record literals. Examples: `examples/accept/ctor-field-construction.sw`, `examples/reject/ctor-construction-*.sw`.
- **Shared fields**: a field name `f` is shared by a data type `T` when every constructor has an explicit field `f` of the same type, a type that mentions only `T`'s parameters and other shared fields (syntactically, on the declared type; an implicit field never counts). `T.f : [params] [indices] -> T … -> F` is then generated (one `case`, a branch per constructor) in `T`'s namespace, so `a.f`, `.f` sections (`xs.map .id`), pipes (`a |> .id`), `T.f a` written in full and proofs (`(Circle 1 "a").id = "a" := rfl`, or by cases) all work. It applies to every non-record data type, one-constructor ones and indexed families included (`Pair.fst`, `And.left`, `Char.code`). A written `def T.f` when `f` is shared is `E-DUPLICATE` (the note says to delete it and use the field); when `f` isn't shared it's allowed, and dot notation finds it. When `f` isn't shared, `a.f` is `E-UNKNOWN-FIELD` ("`Shape` has no shared field `text`") with a note saying why: only some constructors have it (match on `a` to read it, `| Circle { text, .. } => …`), its type differs (`id` is `Text` in `Dot` but `Nat` in `Polygon`), its type mentions a field only some constructors have, two fields' order is cyclic across constructors, it's implicit, or (in a proposition) its type mentions data that can't be taken out of a proof. Examples: `examples/accept/shared-fields.sw`, `examples/reject/shared-field-*.sw`; docs/proposals/variant-fields.md §5.
- **Shared-field update**: `{ c | id = x }` on a value of a non-record data type (any number of constructors) rebuilds whichever constructor `c` is, with the named fields replaced. Every named field must be shared; several may be given, in any written order. New values are checked in the shared fields' dependency order; in a computation the base runs first, then the replacements in the order written. In every constructor, a field (explicit or implicit, data or proof) whose type mentions a replaced field must be named too: if it's shared, that's `E-RECORD-UPDATE` ("updating `n` needs `xs` updated too"); if it's implicit or one constructor's own, `E-RECORD-UPDATE` ("`n` can't be updated on every `Labelled`", with a note naming the constructor and field). A field that isn't shared is `E-UNKNOWN-FIELD` ("`Shape` has no shared field `text`"), one no constructor has is "`Shape` has no field `colour`", and one given twice is `E-RECORD-FIELD`. Indexed families are refused (`E-RECORD-UPDATE`). It's elaborated as `let`s and a `match` on the base, so `{ a | xs = ys }` with `ys: Vec Nat (Sized.n a)` checks, and the base may be any expression. Record updates are unchanged. In a theorem's statement, bracket the update (`({ c | id = x }).id = x`), since `{` there starts an effect row. Examples: `examples/accept/shared-field-update.sw`, `examples/reject/shared-field-update-*.sw`; docs/proposals/variant-fields.md §6.
- **Update lemmas.** On an unknown value an update doesn't compute (it's a `match` on the value), so `({ c | id = x }).id = x` isn't `rfl`. Instead, each shared field `f` that an update can replace gets, for each shared field `g`, the theorem `T.f.update.g`, reading `g` after `f` is updated: with `type Shape = | Dot (ref: Nat) (id: Text) | Circle (ref: Nat) (id: Text) (text: Text)`,

  ```
  theorem Shape.ref.update.ref (x: Shape) (ref: Nat): ({ x | ref = ref }).ref = ref
  theorem Shape.ref.update.id (x: Shape) (ref: Nat): ({ x | ref = ref }).id = x.id
  ```

  and likewise `Shape.id.update.ref` and `Shape.id.update.id`; a type's parameters are implicit (`[a: Type] → (x: Tagged a) → (tag: a) → …`). `rewrite Shape.ref.update.id in rfl` proves `({ s | ref = s.ref + 1 }).id = s.id`, finding any update of `ref` written anywhere (two updates of the same fields are equal, docs/proposals/variant-fields.md §6.5), and nested updates `{ { s | ref = 0 } | id = t }` take one lemma each. An update of several fields at once, `{ s | ref = 0, id = t }`, is a different term, which these don't match (`E-REWRITE-NOTHING`); split on the value (`cases`) there. When updating `f` forces other shared fields (`xs: Vec Nat n` for `n`), `T.n.update.g` updates them all, `({ x | n = n, xs = xs }).g`. Only a data field whose type mentions no field is read back: after `{ x | xs = ys }`, `xs` has type `Vec Nat ({ x | xs = ys }).n`, not `Vec Nat x.n`, so there's no `T.xs.update.xs`; a proof field, which isn't unfolded, isn't read either. There are none when updating `f` would need an implicit field or one constructor's own field replaced, nor for records (`({ p | x = 1 }).x = 1` is `rfl`), indexed families (which can't be updated) or propositions. They're generated with the type, checked by the kernel like any theorem, and hover shows them; the names can't be written as declarations (`theorem Shape.ref.update.id` is `E-PARSE`). Example: `examples/accept/shared-field-update-lemmas.sw`; docs/proposals/variant-fields.md §6.6.
- **Order of effects**: in a computation, field expressions run in the order written, then the record is built; an update's base runs once, first.
- **`==`** works on a record whose fields are all data with `DecEq` (none depending on another), or proofs of equations in types with `DecEq` (left out of the comparison: `type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }` gets `==`). A `DecEq` instance is derived when the record is declared, as for other data types (see the operator table). Otherwise it's `E-INSTANCE-NONE`, with a note saying why; declare an instance (`instance T.instDecEq: DecEq T := { decide = … }`) instead.
- **`T.ext`** is generated for a record, as a checked theorem: two values are equal when their data fields are. `theorem Dial.ext [highest: _] (x: Dial highest) (y: Dial highest) (positionEq: x.position = y.position): x = y`, with one hypothesis `fEq: x.f = y.f` for each data field `f` and none for proof fields (any two proofs of an equation in a type with `DecEq` are equal). It's there when the data fields don't depend on earlier fields (functions are fine), and each proof field proves an equation in a type with `DecEq` that doesn't mention the record or a type parameter; otherwise `T.ext` is an unknown name. A record with no data fields gets `T.ext x y: x = y`. Interfaces, propositions, records defined together with other types and indexed ones get none. The library's records (`Mod`, `Set`) have none generated; `Mod.ext` is written by hand. A `theorem T.ext` of your own in the same module is used instead, with no error (`examples/accept/record-ext.sw`).
- **A record of propositions is decided** when each of its fields can be (SW-1015): `type Small (n: Nat): Prop = { below: n < 10, notZero: n ≠ 0 }` gets a derived `instance` returning `Decidable (Small n)`, so `byDecision`, `auto`, `if h: Small n` and the counterexample search (`stitchwort audit`, a failing proof's note) decide it, as they decide `And`. Each field is decided by what `if h:` finds for its type where the record is declared: an instance above it in the module, or in a namespace it uses. A field whose proposition nothing decides for unknown arguments (one defined by recursion on a list, say) needs a decision written for it first, an `instance` returning `Decidable …`; until then the record has none, and the error where one is wanted names the proposition that stopped it. Nor is one derived when a field's type mentions an earlier field, or for a record defined together with other types (`examples/accept/derive-decidable-record.sw`; the trip journal's `WellFormed`, `examples/projects/accept/trip-journal`).
- **After a declaration's `:` or an arrow**, `{` starts an ability row when a type follows the braces (`{IO} Nat`). Otherwise it's a record, so a theorem's statement may start with a literal or an update: `theorem t (p: Person): { p | age = 3 }.age = 3`, or `(p: Person) -> { p | age = p.age } = p`. Braces holding an `=` are always a record, since a row never holds one (SW-1015, `examples/accept/record-in-statement.sw`).
- At the JS boundary a record is a plain object with its fields as keys, in declared order, and no `tag` (DESIGN.md §12); a one-field record with `@[js.unboxed]` is its field's value instead (Microtypes).

### Field defaults

A record's field, or a constructor's explicit field, may have a default value, written after `:=` (docs/proposals/named-arguments.md §5.1). A record literal, a named construction or a constructor applied with named arguments may then leave that field out.

```
type RangeOptions = {
  start: Nat := 0,
  stop: Nat,
  step: Nat := 1
}

def small: RangeOptions := { stop = 10 }                   -- start = 0, step = 1
def evens: RangeOptions := { stop = 10, step = 2 }

type Sized = {
  size: Nat := 8,
  cells: Vec Bool size := Vec.replicate size False         -- uses the actual `size`
}

type Shape =
  | Circle { radius: Nat, id: Text := "anonymous" }
  | Square (side: Nat) (id: Text := "square")

Circle { radius = 1 }      -- a Shape: id is "anonymous"
Circle 1 "a"               -- positional: every field, as before
Circle (radius := 1)       -- named arguments fill defaults too (D2485)
Square (side := 2)         -- the same for a constructor declared with brackets
```

- **What may be left out.** Only a field with a default; leaving out any other is `E-RECORD-FIELD`, with a note naming the fields that have defaults. `{}` is a literal of a record whose fields all have defaults, and `C {}` a construction of a brace-declared constructor whose fields all have defaults (an empty declaration `| C {}` is `E-PARSE`). Positional application still gives every explicit field, so no existing positional call changes meaning. Named arguments ([Named arguments](#named-arguments)) on a constructor fill the defaults, as they do for a `def`'s parameters, when they name some of the explicit fields, positional arguments fill the fields without defaults in order, and every field left out has a default (`Square (side := 2)`; with another field left out the call is a function waiting for it, as before). An update `{ r | a = 5 }` keeps the other fields' values (a default is how a value is built, not a computed property), and patterns are unchanged: without `..` they name every field.
- **What a default may use**: the type's parameters, the fields before it (implicit ones too), and anything in scope at the declaration. A later field is `E-UNKNOWN-NAME`, with a note. It must be pure, and so finish: an operation is `E-ABILITY`, and calling something `Partial` is `E-PARTIAL`. So when a default is computed, and how often, can't be seen. A default may still be a function that performs operations when called (`onDone: Nat -> {IO} () := n => IO.print "done"`).
- **Checked for any earlier values.** A default is checked once, at the declaration, for every value of the fields before it, since a literal may give them: `ok: size = 8 := rfl` after `size: Nat := 8` is `E-REFL`. A later field's type may mention a defaulted field, and the default computes there: `{ cells = Vec.replicate 8 False }` checks for `Sized`.
- **Leaving a field out commits to its default.** Nothing is inferred from the other fields: with `size: Nat := 0`, `{ cells = threeCells }` is `E-TYPE-MISMATCH`, with a note that `size` is left out and is `0`.
- **Run order.** In a computation, the fields given run once, in the order written, then the record is built, and the defaults use their results: with `type Twice = { x: Nat, twice: Nat := x + x }`, `{ x = readNat() }` reads once. In pure code, a given field that a default uses is bound by a `let` first (unless it's a variable or a literal), so it isn't computed twice.
- **Identity.** Each default is a generated definition, `RangeOptions.step%default` (for a constructor's field, `Shape.Circle.id%default`), taking the parameters and earlier fields it needs. A literal that leaves a field out calls it, so `{ stop = 10 }` equals `{ start = 0, stop = 10, step = 1 }` (`rfl` proves it), but the two have different hashes. Defaults aren't part of the type's hash: changing one changes the hashes (and reruns the tests) of exactly the literals that leave that field out. A literal that gives every field is the same term, with the same hash, as before the type had defaults. These names can't be written in source.
- **Where defaults can't go.** A function type's parameter (`(f: (step: Nat := 1) -> Nat)`), a lambda's, or an implicit or `auto` parameter is `E-PARSE` ("only a definition's parameter or a field can have a default value"); an implicit constructor field can't have one; an interface's methods can't (`E-FIELD-DEFAULT`). A definition's explicit parameters can: see [Parameter defaults](#parameter-defaults).
- **A default that names a definition of its module** makes the type depend on it, so that definition can't mention the type (`E-MUTUAL-KIND`, as for any cycle between a data type and a definition).
- **At the JS boundary**, an export's parameter may leave a defaulted field out, and the decoder fills it by running the default, in field order, from the fields before it (given or defaulted). A result always has every field. So the TypeScript declarations have two shapes (D1101): `RangeOptions`, complete, for results, and `RangeOptionsInput`, with the defaulted fields optional, for parameters. Every type that holds one, anywhere in its fields, has an input shape too (`type Job = { name: Text, options: RangeOptions }` gives `JobInput`, with `options: RangeOptionsInput`), and a type argument is written with its input shape (`BoxInput<RangeOptionsInput>`):

  ```ts
  export type RangeOptions = { readonly start: bigint; readonly stop: bigint; readonly step: bigint };
  export type RangeOptionsInput = { readonly start?: bigint; readonly stop: bigint; readonly step?: bigint };
  export declare function widen(options: RangeOptionsInput): RangeOptions;
  ```

  Only a *missing* own property asks for the default. A property that is present is decoded as given, `undefined` included: for a field that isn't an `Option`, `undefined` is refused like any wrong value (`options.step: expected a non-negative bigint`), and an inherited property is refused as for any field. A defaulted `Option` field has three meanings (D1114): with `colour: Option Text := Some "blue"`, `{}` is the default, `{ colour: undefined }` is `None`, and `{ colour: "red" }` is `Some "red"` (`null` is still refused). Its input type is `colour?: string | undefined`, and on output it is always present, `colour: string | undefined`, `None` as `undefined`, so a value passed back in keeps its `None`. An `Option` field without a default keeps the encoding below: a missing property and `undefined` are both `None`, and `None` is no property. `@[js.optional]` on a field with a default is `E-ATTRIBUTE`. An input shape's name must be free: another type at the boundary called `RangeOptionsInput` is `E-EXPORT`. A `@[js.unboxed]` record is its field's value at the boundary, so its own default never applies there.

Examples: `examples/accept/field-defaults.sw`, `examples/reject/field-default-*.sw`, `examples/extract/field-defaults.sw`. Design: [named-arguments.md](proposals/named-arguments.md) §5.1 to §5.3.

### Parameter defaults

An explicit parameter of a `def` or `theorem` header, top-level or local, may have a default value, written after `:=` (docs/proposals/signature-defaults.md):

```
def makeBooking (id: Text)
    (start: Float := 0.0)
    (duration: Float := 60.0)
    (room: Option Text := None): Booking :=
  { id, start, duration, room }

test "a short booking" := makeBooking "a" (duration := 30.0) |> .duration == 30.0
test "every booking" := ["a", "b"].map makeBooking |> .length == 2
```

- **Given by name only.** Positional arguments skip a defaulted parameter, so adding a default never moves a positional argument: `makeBooking "a" (duration := 30.0)`. A positional argument written after the header's parameters ran out, in a call that left a default out, is `E-DEFAULT-POSITIONAL` (`scaler 5 3` with `def scaler (base: Nat) (factor: Nat := 1): Nat -> Nat`), with both fixes: `scaler 5 (factor := 3)`, or `(scaler 5) 3`, whose brackets finish the call before `3` is applied.
- **Every written call fills the defaults it doesn't name**, at the end of the call: a bare name (`makeBooking` is `id => makeBooking id 0.0 60.0 None`, so `.map makeBooking` works), dot notation (`clip.trimmed`), a method section (`.trimmed`) and a pipe (`clip |> Clip.trimmed`). A required parameter left out before the last given or defaulted one makes the call a function of it, with its name (`range 0` is `stop => range 0 stop 1`); one after it stays to currying. A function's type is still the full arrow, defaults included; to pass the function with a default open, write the lambda (`start stop step => range start stop (step := step)`).
- **What a default may use**, and when it is checked, are as for fields: the parameters before it (a later one is `E-UNKNOWN-NAME`, with a note), checked once at the declaration for any values of those (`(ok: size = 8 := rfl)` after `(size: Nat := 8)` is `E-REFL`), and pure (`E-ABILITY`, `E-PARTIAL`). It can't use the definition, or one defined together with it (`E-MUTUAL-SIGNATURE`).
- **Leaving a parameter out commits to its default** before the arguments are checked: with `def sized (n: Nat := 3) (xs: Vec Nat n)`, `sized two` (`two: Vec Nat 2`) is `E-TYPE-MISMATCH`, with a note that `n` is left out and is `3`; `sized (n := 2) two` checks. A written argument a default uses is computed once: bound by a `let` first unless it's a variable, a name or a number.
- **Identity.** Each default is a generated definition, `range.step%default`, taking the earlier parameters it needs; a call that leaves the parameter out calls it, so `range 0 10` equals `range 0 10 (step := 1)` (`rfl` proves it) with a different hash. Defaults aren't part of the definition's hash: changing one changes the hashes of exactly the calls that leave it out, and a call that names every default is the term it was before the defaults were added.
- **Not yet**: an `export def` with a default is `E-EXPORT` (JS callers will get an options object).
- **Editor.** Hover shows the header as written, defaults included, and completing a parameter's name shows its default (`step := 1`).

Examples: `examples/accept/param-defaults.sw`, `examples/projects/accept/param-defaults-across-namespaces`, `examples/reject/param-default-*.sw`.

## Numbers in an `export`

An exported `Nat` or `Int` crosses the JS boundary as a `bigint`. To take or return a plain JS `number`, use the library's `SafeNat` or `SafeInt` (`std/Int/Safe.sw`, SW-337) as the parameter or result type:

```
import Std (Option, SafeNat)

export def addSafe (a: SafeNat) (b: SafeNat): Option SafeNat := SafeNat.ofNat (a.value + b.value)
```

```ts
export declare function addSafe(a: number, b: number): number | undefined;
```

- **They are records.** `type SafeNat = { value: Nat, fits: value <= 9007199254740991 }` and `type SafeInt = { value: Int, fits: Int.natAbs value <= 9007199254740991 }`: a number and a proof that it's at most 2^53 - 1 in magnitude, the largest whole number a JS `number` holds exactly (`Number.MAX_SAFE_INTEGER`). In Stitchwort they're ordinary records, so `n.value` is the `Nat` or `Int`; `SafeNat.ofNat` and `SafeInt.ofInt` give `Some` when a number is within the bounds, and the `fits` proof is what a function builds by comparing, as above.
- **Numerals.** A numeral checked against `SafeNat` or `SafeInt` is the record with that value, its bound checked by computing it, so no proof is written: `{ bytes = 10, offset = -3 }` for `{ bytes: SafeNat, offset: SafeInt }`, and `(10: SafeNat)` is `{ value = 10, fits = rfl }` (SW-354). A negative numeral is a `SafeInt` as it is an `Int`. One beyond 2^53 - 1 in magnitude (`9007199254740992`), or a negative `SafeNat`, is `E-SAFE-LITERAL`. Only an expected `SafeNat` or `SafeInt` makes a numeral one; in a comparison beside one, the numeral takes its type. They have no arithmetic: compute on `.value`. In JS such a value is a plain `number`. Examples: `examples/accept/safe-literals.sw`, `examples/reject/safe-literal-*.sw`.
- **Decoding is checked.** A JS argument must be a `number` that is a whole number from 0 to 2^53 - 1 (`SafeNat`) or from -(2^53 - 1) to 2^53 - 1 (`SafeInt`). A `bigint`, a string, `NaN`, an infinity, a fraction and a whole number out of range are refused with `StitchwortInputError`: `a: expected a number`, `a: expected a whole number`, `a: expected a whole number from 0 to 9007199254740991`. A whole `number` beyond 2^53 - 1 may have been rounded already, so it's out of range, not repaired. `-0` is read as 0.
- **Encoding is exact**, because the type bounds every value of it, so a function can't return a number a JS `number` can't hold: it has to show (`fits`) that it fits, or return `None`.
- **Everywhere a type goes**: inside lists, `Option`, data types and records, with the path to the problem as for any input. `Nat` and `Int` are unchanged and remain `bigint`.
- **Only the library's types.** A program's own record called `SafeNat` is an ordinary record. The JS codec is used only for the library's exact declarations, by content hash.

Example: `examples/extract/safe-numbers.sw`. See DESIGN.md §12.

A `Float` crosses as a `number`, any `number`: `NaN`, the infinities and `-0` included, and a `bigint` or a string is refused (D685). It needs no wrapper, since every double is a `Float`. A program that needs finite input checks it on its own types (`if h: ...`); a proof field in a record checks nothing at run time (D702). Example: `examples/extract/floats.sw`.

## `Option` in an `export`

An `Option T` crosses the JS boundary as `T | undefined` (D582):

```
import Std (Nat, Option, Text)

type Profile = { name: Text, nick: Option Text }

export def withNick (p: Profile) (n: Option Text): Profile := { p | nick = n }
export def halve: Option Nat -> Option Nat
  | None   => None
  | Some n => Some (n / 2)
```

```ts
export type Profile = { readonly name: string; readonly nick?: string };
export declare function withNick(p: Profile, n: string | undefined): Profile;
export declare function halve(arg0: bigint | undefined): bigint | undefined;
```

- **Decoding.** `undefined` is `None`; any other value is decoded as a `T` and is `Some` of it. `null` is refused (`n: expected a value or undefined, not null`), not read as `None`.
- **In a record's field** the property is optional, `nick?: string`: a missing property is `None` too. Encoding `None` leaves the property out, not set to `undefined`, so the declarations type-check under `exactOptionalPropertyTypes` as well as `--strict`. A record's other fields are still required, and an inherited property is still refused.
- **Everywhere else**, in arguments, results, list elements (`(bigint | undefined)[]`), a constructor's fields and the arguments of parameterised types, it is `T | undefined`.
- **Nested.** Only the outermost `Option` is `T | undefined`: `Option (Option Nat)` is `Option<bigint> | undefined`, where the inner `Option<bigint>` is the tagged object `{ $tag: "None" }` or `{ $tag: "Some", value }`, so `Some None` and `None` stay distinguishable.
- **Inside `Option`**, a `SafeNat` is a `number` (`number | undefined`), and a record's proof fields about an optional field are checked after it's decoded.

Example: `examples/extract/options.sw`. See DESIGN.md §12.

## `Map Text V` in an `export`

A `Map Text V` crosses the JS boundary as a plain object, a dictionary from string keys to `V` (D651, D665):

```
import Std (List, Map, Nat, Text)

type Person = { name: Text, age: Nat }

export def ages (people: Map Text Person): Map Text Nat := people.map (p => p.age)
export def bump (scores: Map Text Nat) (who: Text): Map Text Nat := scores.insertWith who 1 Nat.add
```

```ts
export type Person = { readonly name: string; readonly age: bigint };
export declare function ages(people: { readonly [k: string]: Person }): { [k: string]: bigint };
export declare function bump(scores: { readonly [k: string]: bigint }, who: string): { [k: string]: bigint };
```

- **Decoding** reads the object's own enumerable string keys (`Object.keys`) and decodes each value with `V`'s codec; the map is built with the library's own `Map.fromList`, so its keys are in order as in any map. Symbol keys, inherited properties and non-enumerable ones are not entries. A key that is a lone surrogate is refused, like any `Text`.
- **A plain object is required.** `null`, a primitive, an array, a JS `Map`, a `Date` or a class instance is refused (`scores: expected a plain object, not a Map, a class instance or another kind of object`), since reading no keys from it would silently give an empty map. An object made by `{}`, `JSON.parse` or `Object.create(null)` is plain; so is one from another realm (a `vm` context, an iframe).
- **Awkward keys are data.** `__proto__`, `constructor`, `toString` and the empty string are entries like any other, on input (an own `__proto__` property, as `JSON.parse` makes) and on output. Encoding defines each key as an ordinary data property on a fresh `{}`, so no prototype is set and no setter runs.
- **Encoding** gives a plain object (prototype `Object.prototype`) with the entries in key order, which is `Text`'s order, by code point. JS lists keys that are array indices (`"9"`, `"10"`) first, in numeric order.
- **In TypeScript** the type is an index signature, `{ readonly [k: string]: V }` as a function's parameter and `{ [k: string]: V }` in a result and inside a data type's declaration (like lists: `readonly` only where it helps a caller; `readonly` on an index signature never affects assignability, but a list inside it would), the same as `Record<string, V>`, so an app's `Record<SpeakerId, V>` (a flavoured or branded string key) is accepted as an argument and a result assigns back to it. An `interface` with known keys isn't an index signature in TypeScript; a `type` alias is.
- **Nesting**: `V` can be a record, a list, an `Option` (`{ readonly [k: string]: bigint | undefined }`) or another `Map Text _`.
- **Only `Text` keys**, ordered by `Text`'s own order, or a microtype's (a `@[js.unboxed]` record over `Text`, see Microtypes) in its derived order, which is the same. Any other `Map` in an export is `E-EXPORT`: "only maps from `Text`, or from a `js.unboxed` record over `Text`, cross, as plain objects".

Example: `examples/extract/dictionary.sw`. See DESIGN.md §12.

## Attributes

An exported data type crosses to JavaScript as `{ $tag: "Ctor", …fields }`: the property `$tag` holds the constructor's name, and each field's key is its name, with each `'` as `$`. Attributes, written `@[name "argument", …]`, set another form where the type is declared, to match a wire format an app already has (docs/proposals/attributes.md):

```
@[js.tag "type"]
type Shape =
  | @[js.name "DOT"] Dot
  | @[js.name "CIRCLE"] Circle (radius: Nat) (@[js.name "center_x"] centerX: Nat)

type Drawing = { @[js.name "type"] kind: Text, shapes: List Shape }
```

```ts
export type Shape =
  | { readonly type: "DOT" }
  | { readonly type: "CIRCLE"; readonly radius: bigint; readonly center_x: bigint };
export type Drawing = { readonly type: string; readonly shapes: Shape[] };
```

| Attribute | On | Meaning |
|---|---|---|
| `js.tag "KEY"` | a data type (not a record) | the key of the property that says which constructor an object is, instead of `$tag` |
| `js.name "NAME"` | a constructor | its tag value, instead of its name |
| `js.name "NAME"` | a constructor's or a record's field | its key, instead of its name |
| `js.optional` (no argument) | a constructor's field of type `Option T` | an optional property `f?: T`, instead of `f: T \| undefined` |
| `js.enum` (no argument) | a data type whose constructors have no fields | a plain string, one per constructor (its name, or its `js.name`), instead of an object |
| `noReceiver` (no argument) | a definition | in a type's namespace, a function that isn't called with `.` or `|>`, so it may take the type's value after another parameter without the warning `W-RECEIVER-NOT-FIRST` |
| `reading` (no argument) | a theorem `test ↔ P` (or `test = False ↔ P`) | facts about `test` are taken apart, built and read as `P` (see [Readings](#readings-reading-and-read)) |
| `tailrec` (no argument) | a definition, an exported definition or a local definition | every recursive call of it is a tail call, so it runs as a loop on every backend (see below) |
| `js.unboxed` (no argument) | a record without parameters with exactly one field that has a property | its field's own JS form (`string` for a `Text`), instead of an object; in TypeScript, `type T = string` (see Microtypes) |

- **Where they go.** Before a declaration (on the line or lines before `type`, or on the same line), after a constructor's `|`, and inside a field's brackets or before a record field's name. Several are written `@[a "x", b "y"]` or `@[a "x"] @[b "y"]`; order doesn't matter. A group may span lines, and its `]` may be at the start of a line. An attribute group always belongs to the next declaration, whatever it is.
- **Arguments** are plain strings (no `${…}`), used exactly: no `$` for primes, nothing added. Any non-empty string works, `"0"`, `"a-b"` and `"__proto__"` as a tag value included; quotes and other characters are escaped correctly in the JS and the `.d.ts`.
- **Checked.** Tag values must differ, and a constructor's keys must differ from each other and from the tag key; no key may be `__proto__` (assigning it sets an object's prototype): `E-JS-NAME-CLASH`. A type with attributes is checked where it's declared. One without is checked when an export reaches it, so a field called `__proto__` needs a `js.name` only in a type that crosses. A field called `tag` keeps the key `tag`.
- **Optional properties.** `@[js.optional]` on a constructor's field written with the type `Option T` makes it `readonly f?: T`, as a record's `Option` fields already are: a missing key or `undefined` is `None`, a present value is `Some`, `null` is refused, and an encoded `None` leaves the key out. It is `E-ATTRIBUTE` on a field of any other type (including a type parameter that is an `Option` somewhere), on a record's field (those are optional already), on a field with a default (a missing key is already its default, see [Field defaults](#field-defaults)), on a proof or type field, on a constructor, a type or anywhere else, written twice, or with an argument.
- **String unions.** `@[js.enum]` on a data type whose constructors have no fields makes it cross as a string, not an object; `@[js.name "…"]` on a constructor chooses its string (without it, the constructor's name):

  ```
  @[js.enum]
  type Label =
    | @[js.name "IMPORTANT"] Important
    | @[js.name "SLIDE_TEXT"] SlideText
  ```

  ```ts
  export type Label = "IMPORTANT" | "SLIDE_TEXT";
  ```

  Decoding accepts exactly the listed strings: any other string, a non-string, or the old object form `{ $tag: … }` is refused (`label: expected "IMPORTANT" or "SLIDE_TEXT", not "important"`). It works in every position: a record's field, inside `Option` (`f?: Label`), a list, a map, a constructor's field (with `js.optional`), a function's argument or result. Fields that have no property in JS (a proof, a type) and a type's parameters don't count. It is `E-ATTRIBUTE` on a record, on a type with no constructors, on a type with a constructor that has a field, together with `js.tag` (a string has no tag key), on a constructor or a field, with an argument, or written twice; two constructors with the same string, by name or by `js.name`, is `E-JS-NAME-CLASH`, and `@[js.name ""]` is `E-ATTRIBUTE`. **Against a TypeScript `enum`:** an app's `enum Label { IMPORTANT = "IMPORTANT", … }` member is assignable to the string union (so the app's values go straight into the exported functions), but a string, and so the generated union, is *not* assignable to the enum (tsc 7.0.2, `TS2322`: a result can't be assigned to a variable of the enum's type, and a generated record isn't assignable to the app's record whose fields are the enum). `` `${Label}` ``, the enum's template-literal type, is exactly the generated union, assignable both ways, so an app's type test compares against that (or maps its enum with it); `result as Label` is a cast that compiles.
- **Lists are mutable in declarations.** Every list in a data type's declaration is `T[]`, so an app's `{ xs: T[] }` and the generated type are assignable both ways (`readonly T[]` isn't assignable to `T[]`), and a function's list parameter is `readonly T[]`, which takes either kind. The codec copies arrays in and out, so the caller owns what it gets.
- **An `Array T` crosses as a list does**, as `readonly T[]` or `T[]`, its elements in order: the codec copies them into a new array going in and out of one coming back. Inside the generated code an array is a version array, so `set`, `push` and `pop` are O(1) on the newest version, and an older one still reads as it was (docs/proposals/arrays.md §4.3).
- **Only data fields have keys.** A proof field or a type field has no property in JS, so an attribute on one is `E-ATTRIBUTE`; so is one on a binder naming several fields, `(@[…] x y: Nat)`. The same logical field may have a different key in each constructor.
- **`@[tailrec]`** (docs/proposals/tailrec.md) before a `def`, an `export def` or a local `def` (on the line before it, or on the same line) says that the definition must run as a loop: every call it makes to itself must be a **tail call**, one whose result is the definition's result with nothing left to do after it returns. That holds through the arms of a `match` or a case tree, both branches of an `if`, `∧` and `∨` (on the right), the body of a `let`, the `match`es the compiler lifts out of the definition, a `decreasing` definition's recursion, and, in a block of effects, the last statement. Anything else that holds the call is `E-TAILREC`, and the label says what: `x + total xs` (an operand of `+`), `Nat.max x (biggest xs)` (an argument), `let r := f xs; r + 1` (a `let`), `[x, ..double xs]` (a constructor's field), `if f n == 0 then …` (a condition), `match f n with …`, `xs.map (y => f y)` (inside a function), `handle … with` (the handler waits), and in effects `let r := f n` followed by statements that use `r`. Only true tail calls count: `Cons x (map f xs)` is refused, with a note that `stitchwort run` and JavaScript build such lists without a frame per element but `@[tailrec]` doesn't promise it; carry the result in an extra parameter instead. Marking a definition that never calls itself is `E-TAILREC` too (it catches an attribute left behind when the recursion moved into a helper), and so is a call to another definition of a mutually recursive group that calls it back (not covered yet). The attribute is `E-ATTRIBUTE` on a theorem, an instance, a type synonym, a test, and on a local theorem. On `stitchwort run` and `--native` every tail call already reuses its frame; in JavaScript a marked definition becomes a `for (;;)` loop, and the generator fails with an internal error naming it if it can't, instead of using a frame per call (a body that binds effects is exempt: the effect runtime's loop runs it with no continuation pending per level). It changes no term and isn't part of any hash. Examples: `examples/accept/tailrec.sw`, `examples/extract/tailrec.sw`, `examples/reject/tailrec-*.sw`.
- **Nowhere else.** An unknown attribute is `E-ATTRIBUTE-UNKNOWN` (with a suggestion), and a known one anywhere else (a theorem with any attribute but `reading`, a `def` or an export with a `js.…` attribute or `reading` (`noReceiver` and `tailrec` apply to a `def`, `tailrec` to an export), an instance, an interface, a type synonym, a test, an ability, a function's or a type's parameter, a lambda, a local definition that isn't `tailrec`, a namespace line), twice on one target, without its argument, or on a type with a built-in JS form (`Nat`, `Int`, `SafeNat`, `SafeInt`, `Bool`, `Text`, `Char`, `List`, `Option`) is `E-ATTRIBUTE`. A number or a second string as the argument is `E-PARSE`. Nothing is silently ignored.
- **Nothing changes inside Stitchwort.** Patterns, field access, `show`, `==` and proofs use the Stitchwort names, and attributes aren't part of content hashes, so changing one reruns no test.

Examples: `examples/extract/attributes.sw`, `examples/extract/app-types.sw`, `examples/extract/string-enums.sw`, `examples/extract/microtypes.sw`. See DESIGN.md §12.

## Microtypes

A *microtype* is a type of its own around one value, so that ids of different kinds can't be mixed up: a one-field record is a different type from any other, with the same fields or not, and `@[js.unboxed]` makes it cross to JavaScript as the value itself (docs/proposals/microtypes.md):

```
import Std (Map, Option, Show, Text)

@[js.unboxed]
type UserId = { value: Text }

@[js.unboxed]
type OrderId = { value: Text }

instance UserId.instShow: Show UserId := Show.fromText (u => u.value)

export def ownerOf (orders: Map OrderId UserId) (o: OrderId): Option UserId := orders.get o
```

```ts
export type UserId = string;
export type OrderId = string;
export declare function ownerOf(orders: { readonly [k: OrderId]: UserId }, o: OrderId): UserId | undefined;
```

- **Inside Stitchwort it is a record.** Build one with `{ value = t }` (where its type is known), read it with `u.value`; passing an `OrderId` where a `UserId` is expected is `E-TYPE-MISMATCH`. `==`, `<` and `${…}` are derived as for any record; the derived `Show` prints `{ value = "u1" }`, so the one-line instance above makes `"${u}"` print `u1`. `UserId.ext` proves two equal from their `value`s. Converting a list is `ids.map (u => u.value)`: there is no `coerce` (D1069). At run time a record with one field is stored as that field (D866), so a microtype costs nothing.
- **At the boundary it is its field.** `js.unboxed` is allowed on a record without parameters that has exactly one field with a property (a proof field, like `valid: Email.isValid value = True`, doesn't count and is checked on the way in, as for any record). It crosses as the field's own JS form, both ways, everywhere a type can appear: a function's argument or result, a record's or a constructor's field, an `Option`, a list, a map's value. The old object form `{ value: "u1" }` is refused (`u: expected a string`).
- **In TypeScript it is a plain alias**, `export type UserId = string;` (or the field's type: `bigint`, `string[]`, …), used by name at every use (D1066). The alias doesn't keep `UserId` and `OrderId` apart in TypeScript; an app passes its plain strings straight in.
- **Map keys.** `Map UserId V` crosses as a plain object, `{ readonly [k: UserId]: V }`, when the record is `@[js.unboxed]` over `Text` and the map uses its derived order, which compares the field by `Text`'s and so sorts the keys as `Map Text V` does (D1068). A key's proof fields are checked. A microtype key in an order the program wrote (its own `Ord` instance, or `[ord := …]`) is `E-EXPORT`, as is a key that is a record without the attribute or a microtype over anything but `Text`.
- **Refused** (`E-ATTRIBUTE`): on a data type with constructors, a constructor or a field; on a record with type parameters, with no field with a property, or with two; on a record whose field is an `Option` (an `Option` of it couldn't tell `None` from `Some { value = None }`; an `Option` behind a synonym is `E-EXPORT` when an export reaches it); alongside `js.name` on its field; with an argument, or twice.

**The recipe**, as `examples/extract/microtype-orders.sw` does it:

1. *Declare.* `@[js.unboxed] type UserId = { value: Text }`, one per kind of id. Give it a one-line `Show` if `${u}` should print the text: `instance UserId.instShow: Show UserId := Show.fromText (u => u.value)` (the derived one prints `{ value = "u1" }`).
2. *Validate.* Put the rule in a proof field, `type Email = { value: Text, valid: Email.isValid value = True }`, so no invalid `Email` exists, and write the one way to make one from arbitrary text, a smart constructor:

   ```
   def Email.parse (t: Text): Option Email :=
     if h: Email.isValid t = True then Some { value = t, valid = h } else None
   ```

   Code that may fail says `{Fail}` instead and uses `Email.parse t |> .orFail "not an email address: ${t}"`. An export that returns `Option Email` gives JavaScript `string | undefined`; one that takes an `Email` refuses a string that fails the rule (`e: proof field `valid` ... doesn't hold`).
3. *Use as a `Map` key.* `Map OrderId UserId` needs nothing more: the derived order compares the field, so `Map.get`, `Map.insert` and the lemmas work as for `Text` keys. Keep the derived `Ord`; a key in another order can't cross (above).
4. *Export.* `export def ownerOf (owners: Map OrderId UserId) (o: OrderId): Option UserId`. In TypeScript the app passes `{ o1: "u1" }` and `"o1"`.

Examples: `examples/extract/microtypes.sw` (every position), `examples/extract/microtype-orders.sw` (the recipe).

## Interfaces

An interface describes what a type supports; an instance says how one type supports it; `auto` finds the instance by type (docs/proposals/interfaces.md, stages 1 to 5; `examples/accept/interfaces*.sw`, `examples/accept/eqeq-*.sw`, `examples/accept/operators.sw`).

```
-- A record of operations (and laws: proof fields), with one parameter, a type.
interface Pretty (a: Type) =
  { pretty: a -> Text }

-- An instance: a definition of the interface for one type, marked `instance`.
instance Item.instPretty: Pretty Item :=
  { pretty = i => "item" }

-- It may ask for instances of its type's variables.
instance Pretty.instList [auto p: Pretty a]: Pretty (List a) :=
  { pretty = xs => Text.join ',' (xs.map Pretty.pretty) }

-- Asking for one, by `auto`, named or not.
def shout [auto p: Pretty a] (x: a): Text := Pretty.pretty x ++ "!"
def whisper [auto Pretty a] (x: a): Text := Pretty.pretty x

-- A named alternative: a plain `def` of the interface's type, never found
-- by `auto`, passed by name.
def loud: Pretty Item := { pretty = i => "ITEM" }

test "by name" := shout [p := loud] MkItem == "ITEM!"
```

The library has six interfaces so far. `Ord` is a total order: `compare`, the relations `lessThan` and `lessEq` with their decisions `decLessThan` and `decLessEq`, and laws (`equal`, `flip`, `trans`, and four tying the relations to `compare`), with `DecEq` as its superclass `eq`. It has instances for `Nat` and `Int` (whose relations are `<` and `<=` themselves), `Float` (IEEE 754's total order, [Numbers](#float)), `Char`, `Text`, `Bool`, `Ordering`, lists and `Vec` (lexicographic), `Option` (`None` first) and pairs; `List.sort`, `List.maximum` and `List.minimum` use it (`List.sort [ord := descending] xs` for another order), and `Ord.fromCompare` (a comparison and its three laws) and `Ord.byKey` (a key that tells values apart; its `<` and `<=` are the key's own, so `c < x` on a `Fin` is `Fin.toNat c < Fin.toNat x`) build one. A declared data type or record gets one derived: constructors in the order they're declared, then the fields left to right, proof fields left out (`Dial` by its `position`), a list inside a nested type compared as lists are (`Packets [Number 1, Number 9] < Packets [Number 2]`), wherever it has `==` and its data fields have `Ord`. Its `eq` is the type's `DecEq` instance, derived or the module's own; with its own, `Ord` is derived once that instance is checked, so a use of `<` on the type in what that instance itself needs has none. A module's own `instance T.instOrd: Ord T` replaces it (`examples/accept/derive-ord-*.sw`). `<` and `<=` are its relations, for every type ([Numbers](#numbers)). `Add` (`zero`, `add`, and the laws `zeroAdd`, `assoc`, `comm`: things you add in any order) and `Mul` (`one`, `mul`, and `oneMul`, `mulOne`, `assoc`: not commutative) are `+` and `*`, with instances for `Nat` and `Int`; `List.sum`, `List.sumBy` and `List.product` use them, so `[(3: Int), -5, 1].sum` is `-1` and a list of a user's points adds up with its `Add` instance. `DecEq` (`decide: (x: a) -> (y: a) -> Decidable (x = y)`) is the one `==`, `!=`, `if h: x = y` and `auto` use to decide equations, with `DecEq.uniqueEq` (any two proofs of an equation in a type with `DecEq` are equal) and `DecEq.sound`. Decision procedures for anything else are instances too, but of `Decidable …` (`instance decToken: Decidable Token := …`): none of the rules below apply to them, and `auto` keeps its search for them (first fit, above the use). `Decidable p` is a record of a test and its proofs, `{ holds: Bool, sound: holds = True → p, complete: p → holds = True }` (SW-2746). Write one test first, `{ holds = Nat.equal m n, sound = …, complete = … }`, so that `==` computes to the test (on `Nat`, `a == b` is `Nat.equal a b`), or from a proof with `Decidable.yes proof` and `Decidable.no refutation`. `d.sound rfl` proves `p` when `d`'s test computes to `True`, which is the proof `auto` writes; `Decidable.refute d e` turns `e: d.holds = False` into `¬p`. A proof splits on a decision by matching on its test, `match h: d.holds with | True => … | False => …`, or on the record, `| { holds = True, sound = s, complete = _ } => … s rfl …`.

`Show` is the fifth: `toText` (what `${e}` inserts) and `toSource` (a source-like form, used for the elements of containers: text in quotes with escapes, `'a'` for a character; not promised to parse back). They agree except for `Text`, `Char` and `Float` (`3` and `3.0`, [Numbers](#float)). The library has instances for `Nat`, `Int`, `Float`, `Bool`, `Char`, `Text`, `Ordering`, lists, `Option`, tuples, `Vec`, `Fin`, `Map` and `Set`; a declared data type or record gets one derived (`Dot`, `Rect 3 4`, `Node Leaf (-1) Leaf`, `{ name = "tea", price = 3 }`; proof fields left out), unless a field is a function, a type, or depends on an earlier field, or the type is nested in a container other than `List`, `Option` and pairs. Inside a nested type, lists and pairs print as their own instances print them: `Packets [Number 1, Packets []]`. A module's own `instance T.instShow: Show T` replaces it, and `Show.fromText f` builds one from a single function: `instance Point.instShow: Show Point := Show.fromText Point.toText`. A type with none is `E-INSTANCE-NONE` at the `${…}` (`examples/accept/show.sw`).

`Finite` is the sixth: `all`, a list of every value, and `complete`, the proof that every value is on it. The library has instances for `Bool`, `Ordering`, `Option`, pairs and `Fin n`; a declared data type or record that isn't recursive and whose fields are all finite gets one derived, its constructors in declaration order. `Finite.check` checks a `Bool` statement for every value by computing it ([`Finite` and `Finite.check`](#finite-and-finitecheck)).

**`Mod n`** (`import Std (Mod)`; `examples/accept/mod-arith.sw`, docs/proposals/fin-arithmetic.md) is the numbers 0 to n - 1, where `+` and `*` wrap around, as on a clock: it has `Add` and `Mul` instances (with their laws proved for every `n`), `DecEq`, `Ord` (by value) and `Show` (the number). `Fin n` stays the type of positions in a `Vec`, with no arithmetic, so that `i + 1` at the last position can't silently wrap; `Fin.toMod` and `Mod.toFin` convert. A value is `{ value: Nat, isLt: … }` and runs as a plain number. There are no `Mod` literals: `Mod.ofNat` and `Mod.ofInt` make values, and wrap (`(Mod.ofNat 150: Mod 100)` is 50, `(Mod.ofInt (-1): Mod 100)` is 99, by the Euclidean remainder). There is no `-`: `i.sub j` and `i.neg` are named functions that wrap (`Mod.sub 5 7` is 98 in `Mod 100`). Moving by a `Nat`, `i.addNat k` and `i.subNat k` (which go through `Mod.ofInt`), has its laws: `addNatZero`, `subNatZero`, `addNatAddNat` (`(i.addNat j).addNat k = i.addNat (j + k)`), `subNatSubNat`, `addNatSubNat` and `subNatAddNat` (there and back is `i`); with `negZero`, `negNeg`, and the mirror laws `negSubNat` (`Mod.neg (i.subNat k) = (Mod.neg i).addNat k`) and `negAddNat`. `Mod.negOfInt` and `Mod.ofIntAdd` are the steps they are proved by. `Mod 0` has one value, 0, so that every `Mod n` has a zero. A dial: `turns.scanLeft (p t => p + Mod.ofInt t) (Mod.ofNat 50: Mod 100)`.

- **An interface is a record** (`type I (a: Type) = { … }`, [Records](#records)) that the compiler finds values of. It has exactly one parameter, a type, and is in `Type` (`E-INTERFACE-SHAPE`). Its fields are its operations; a field whose type is a proposition is a law, erased at runtime.
- **Methods.** Each field `f` of `I` gives `I.f: [a: Type] -> [auto i: I a] -> …`, which takes the field from the dictionary it's given: `Pretty.pretty x`. `i` is the interface's name with a lower-case first letter (`pretty`, `decEq`), so `Pretty.pretty [pretty := loud] x` passes one by name. Methods are in the interface's namespace and can be imported: `import Pretty (pretty)`. On a dictionary `d`, `d.pretty` is its field, by dot notation.
- **Instances** are definitions marked `instance`, always named; `T.instI` or `I.instT` by convention (the name can't be in a namespace of the library: `Pretty.instNat`, not `Nat.instPretty`). The type must be the interface applied to a type name and distinct variables: `Pretty Nat`, `Pretty (List a)`, `Pretty (a, b)`, `Size (Vec a n)`, after unfolding synonyms (`E-INSTANCE-HEAD`: not `Pretty (List Nat)`, not `Pretty a`, not a non-interface). Its parameters may only be those variables (implicit, usually bound automatically) and `auto` parameters asking for an interface of one of them (`E-INSTANCE-PARAMETER`, `E-INSTANCE-CONTEXT`). The body is any expression of the interface type.
- **One instance per interface and type name** (`E-INSTANCE-OVERLAP`), declared in the module that declares the interface or the type (`E-INSTANCE-ORPHAN`): in a project the namespace, in a single file the file. A synonym owns nothing: `type LocalNat = Nat` doesn't make its module an owner of `Nat`. Another choice for a type is a named alternative.
- **Finding one.** For `[auto i: I T]`: if unification already fixed it, that; otherwise the dictionaries in scope (parameters and `let`s of interface type, and the superclasses inside them), then the one instance for `T`'s type name, whose own `auto` parameters are found the same way. A dictionary in scope wins over the instance: inside `shout [p := loud]`, every `Pretty Item` is `loud`. Two different ones in scope is `E-INSTANCE-AMBIGUOUS` (pass one by name); none is `E-INSTANCE-NONE`. Nothing is guessed: while what's needed, or whether a dictionary in scope fits, depends on something not yet worked out, it waits until the rest of the declaration is, and is then `E-INSTANCE-UNKNOWN-TYPE` (annotate) or `E-INSTANCE-STUCK`. There's no depth limit, only a large step budget (`E-INSTANCE-BUDGET`, which means resolution stopped, not that there's no instance).
- **Superclasses.** A field whose type is another interface on the same parameter is a superclass: `interface Child (a: Type) = { base: Base a, law: … }`. The superclasses can't form a cycle (`E-INTERFACE-CYCLE`). A literal of an interface type may leave a superclass out: it's found like an `auto` argument, before the later fields are checked (so `law`'s type can compute with it). A dictionary in scope gives its superclasses too (`[auto c: Child a]` gives a `Base a`, `c.base`). An instance's superclass must be the instance the compiler finds for it (`E-INSTANCE-SUPER`). Asking for an interface and its own superclass on one type is `E-INSTANCE-REDUNDANT`.
- **Order.** As elsewhere, declarations can be in any order: the rest of the module is checked after its instances, and an instance after the instances of its superclasses and of the interfaces it mentions. An instance needed where it can't be checked first (it depends on the declaration that needs it) is `E-INSTANCE-NONE`, with a note saying so.
- **`auto` parameters on types.** A data type, record or synonym may have `auto` parameters among its parameters, always named: `type Map (k: Type) (v: Type) [auto ord: Ordered k] = { … }` (docs/proposals/interfaces.md §7.5; `examples/accept/data-auto.sw`). Wherever the type is written, the parameter is found as a function's `auto` argument is: `Map Text Nat` is `Map Text Nat [ord := Ordered.instText]`, and inside a function with `[auto ord: Ordered k]`, `Map k v` is the map with that `ord`. Another one is given by name, in its place: `Map Nat Nat [ord := descending]`. The dictionary is part of the type, so maps built with different ones have different types (`E-TYPE-MISMATCH`, with a note); an operation on an existing map takes the ordering from the map's type, whatever else is in scope. A variable for it, `(m: Map k v [ord := o])`, is bound automatically like a type variable, and covers maps with any ordering. In an instance's type it must be written that way, `instance Map.instPretty: Pretty (Map k v [ord := o])` (`E-INSTANCE-HEAD` otherwise): where the instance is used, `o` is the one in the type, not found again. It must ask for an interface (`E-DATA-AUTO`), and types defined together must have the same `auto` parameters. The kernel sees an ordinary parameter, and the value has no field for it.
- `[auto` followed by an uppercase name in a type is a binder: `[auto Pretty a] -> Text`. A list literal starting with a variable called `auto` applied to a constructor would need brackets.

## Abilities

```
-- An ability and its operations. Each operation takes one argument and
-- performs only its own ability.
ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

-- A function type may list the abilities calling it performs, and a row
-- variable `e` (bound automatically, like a type variable) for "whatever
-- else". `{e}` alone is just the variable (an effect-row parameter: code
-- abstract over it can't construct, inspect or branch on it). `A -> B` is pure
-- and total.
def tick(): {State Nat} Nat :=
  let n := get()
  put (n + 1)
  n

-- A handler removes one ability. Clauses run outside the handler: `k`
-- resumes the computation (with the handler still in place) and may be
-- called any number of times. A `return` clause and a clause for every
-- operation are required.
def allResults (prog: () -> {Choose | e} a): {e} List a :=
  handle prog() with
    | return x       => [x]
    | choose u, k    => List.append (k True) (k False)
```

Effectful code is written in direct style. Arguments are evaluated left to right, named ones where they are written ([Named arguments](#named-arguments)), and the lines of a block in order, as are the parts of a sequence `(a; b)`, which are block lines on one line ([Layout](#layout)). The left side of `|>` runs before its right, so `Mul (text "mul("; nat()) (char ','; nat()) |> Parse.before ")"` reads the `)` last. An argument that performs runs before the call, whether or not the function uses it: `saving.toNat |> .fold (Fail.fail usage) (least => least)` fails even when `toNat` finds a number, since `Fail.fail usage` is an argument. A default that performs belongs in a `match`, or in `Fail.need saving.toNat usage`, or behind `() =>` where the function takes one (`Parse.valueOr found (() => …)`). A handler's clauses on their own lines must line up: a `|` at another column belongs to an enclosing handler. An operation on its own (`choose`) is a function, `x => choose x`. A dot call to an effectful function is a call like any other and runs where it's written, also with no further arguments and at the end of a chain of pure calls (`1 + w.toNat.orAbort`). A signature can be a computation that isn't a function: `current: {State Nat} Nat`. Naming or calling a computation where a plain value is expected runs it there, so it's allowed only if it may perform nothing: a function over any row `{e}` used at the empty row, or a `Std.Effect.Comp NoOp NoRes a`, gives its `a` ([proposals/let.md](proposals/let.md) §8). Where a computation is expected (a parameter, constructor field, list item or tuple part of type `Std.Effect.Comp …`), a computation is passed as it is and not run: `isDone c` sees `c` itself, and `Effect.runPure (Done 3)` is `3` ([proposals/effect-polymorphism.md](proposals/effect-polymorphism.md), stage 0). Such an argument is a computation in the parameter's row, not the caller's: one that performs an ability the parameter's row lacks is `E-ABILITY`, which says what the parameter takes, even where the caller may perform it (`examples/reject/passed-computation-ability.sw`). The types stay different: a function returning a computation isn't a function returning a value. A row written `{}` is no row: `{} Nat` is `Nat`. A row is written only on a result type, after `->` or a definition's `:` (D1141): a parameter's type that starts with one, `(c: {} Nat)` or `(c: {IO} Nat)`, is `E-PARSE`, which says to leave out an empty row, or to take a function such as `() -> {IO} Nat` (`examples/reject/row-in-parameter-type.sw`). Messages print the empty-row computation type in full, `Comp NoOp NoRes Nat`, so it is not mistaken for `Nat`. A pure function can use a handler inside; what it handles doesn't appear in its type. How this is translated into ordinary data is described in `docs/core.md`, under "Abilities".

`Effects` (`import Std.Effect (Effects)`) is the type of an effect-row parameter, so a data type can be parameterised by effects as it is by types, and the row goes inside the type's functions: `type Handlers (e: Effects): Type = | MkHandlers (onStep: Nat -> {Partial | e} Nat) (onDone: Nat -> {Partial | e} Nat)`, and `def drive: [e: Effects] -> Handlers e -> Nat -> {Partial | e} Nat`, where `{e}` and `{A | e}` stand for that row (`examples/accept/partial.sw`). Rows are abstract indices: a program can declare an `Effects` parameter and pass it on, but cannot build, compare or inspect one ([proposals/effect-polymorphism.md](proposals/effect-polymorphism.md) §7, D1142, D1143).

### `IO`

`IO` is an ability with `print: Text -> {IO} ()`, `readLine: () -> {IO} Option Text` and `readAll: () -> {IO} Text` (also `IO.print`, `IO.readLine`, `IO.readAll`). `IO.simulate lines prog` runs `prog` against scripted input and records what it prints; `IO.simulateWith seed lines prog` does the same with `IO.randomSeed` giving `seed` (0 under `IO.simulate`). `IO.args()` gives the program's arguments, those after `--` in `stitchwort run Main.main -- a b` or after a built executable's name (none under `IO.simulate`).

- `IO.readLine()` gives the next line without its LF (and a CR just before it), `None` once nothing remains.
- `IO.readAll()` gives everything that remains, verbatim, line endings included; `""` once nothing remains. After it, `IO.readLine()` is `None`; after some `IO.readLine`s it gives the rest. Under `IO.simulate` it gives the remaining scripted lines, each followed by LF.
- `Text.lines: Text -> List Text` follows Rust's `str::lines`: split on LF, drop a CR right before an LF, and the last line's ending is optional. `"a\nb"` and `"a\nb\n"` both give `["a", "b"]`; `""` gives `[]`; `"\n"` gives `[""]`; `"a\r\nb"` gives `["a", "b"]`. A CR anywhere else stays, including a final one.
- `IO.readAllLines(): {IO} List Text` is `(readAll()).lines`. It is total.
- Four lower-level operations are what a terminal handler is built on ([proposals/terminal-io.md](proposals/terminal-io.md) §4): `console: () -> {IO} Console` says whether standard input and output are terminals, and the size (`Console` is `{ inputIsTerminal: Bool, outputIsTerminal: Bool, columns: Nat, rows: Nat }`, 0 by 0 when the size isn't known); `keysMode: Bool -> {IO} ()` enters or leaves keys mode (on a terminal: no line editing or echo, Ctrl-C still stops the program; the alternate screen, cursor hidden, no wrapping; put back however the program ends); `readBytes: () -> {IO} Option (List Nat)` gives the bytes of one read, `None` at the end; `write: Text -> {IO} ()` writes the text with no line ending, then flushes. `print`, `readLine` and `readAll` leave keys mode first. Without a terminal (pipes, the playground) `console` says so and keys mode changes nothing. Under `IO.simulate`, `console` says there's no terminal, `keysMode` does nothing, `readBytes` gives the remaining scripted lines as UTF-8 (`Char.utf8`), each followed by LF, in one read, and `write` records its text as a payload (`examples/accept/terminal-ops.sw`).

### `Abort`

`Std.Abort` (`crates/elab/src/std/Abort/Abort.sw`) is an ability for giving up, as `do` over `Option` in Lean or `?` in Roc: code that may give up says `{Abort}`, reads each step's `Option` with `need`, and a handler decides what giving up means.

```
import Std.Abort (need, ensure, abort, toOption)

def turn (t: Text): {Abort} Int :=
  let (c, rest) := need t.uncons     -- a `None` stops the whole computation
  ensure (c == 'L' || c == 'R')
  let n := rest.toInt.orAbort        -- `need`, by dot notation
  if c == 'L' then -n else n

def parse (t: Text): Option Int := toOption (() => turn t)
```

- `Abort.need: Option a -> {Abort} a`, and `Option.orAbort` for dot notation (`o.orAbort`). `Abort.ensure: Bool -> {Abort} ()` gives up on `False`. `Abort.abort(): {Abort} a` gives up wherever a value of any type is expected.
- `Abort.toOption: (() -> {Abort | e} a) -> {e} Option a` and `Abort.orElse: a -> (() -> {Abort | e} a) -> {e} a` are the handlers. Other abilities pass through, so `{IO, Abort}` code works: what was printed before giving up stays printed (`examples/accept/abort.sw`).
- The operation is `Abort.stop: () -> {Abort} Empty`, for handlers of your own. Its result is `Std.Empty`, a `Type` with no values (`Empty.absurd: Empty -> a`), so no handler can resume it. (`Void` is a proposition, and an operation's result must be a type.) `abort()` is `Empty.absurd (stop())`.
- `Abort.toOption (() => need o) = o` and `Abort.orElse d (() => need o) = o.getOrElse d` hold for every `o`, by `rfl` on each case (`Abort.toOptionNeed`, `Abort.orElseNeed`).

#### Proofs about a block that gave `Some`

A proof that knows `h: toOption (block) = Some v` (or `parse t = Some v`, for a `parse` defined as one) reads off what each step gave with one lemma per step, each continuing from the last one's `rest` (`examples/accept/abort-inversion.sw`):

```
def pickOrder (warehouse: Warehouse) (order: Order): Option Pick :=
  toOption (() =>
    let onHand := warehouse.stock.get order.item |> .orAbort
    let label := warehouse.locations.get order.item |> .orAbort
    let bin := warehouse.bins.get label |> .orAbort
    ensure (order.quantity <= onHand)
    { item = order.item, bin, quantity = order.quantity, left = onHand - order.quantity })

theorem pickStock (warehouse: Warehouse) (order: Order) (pick: Pick) (h: pickOrder warehouse order = Some pick):
    warehouse.stock.get order.item = Some (pick.quantity + pick.left) :=
  Abort.needEqSome h (onHand foundStock rest =>
    Abort.needEqSome rest (label foundLabel rest =>
      Abort.needEqSome rest (bin foundBin rest =>
        Abort.ensureEqSome rest (enough picked =>
          rewrite foundStock, <- Option.someInjective picked in
            rewrite (omega: order.quantity + (onHand - order.quantity) = onHand) in rfl))))
```

- `Abort.needEqSome h use`: the block starts with `need x` (or `x.orAbort`). `use` gets the value `u`, `x = Some u`, and `toOption` of the rest of the block (with `u` for the step) `= Some v`.
- `Abort.ensureEqSome h use`: the block starts with `ensure ok`. `use` gets `ok = True` and the rest.
- `Abort.thenEqSome h use`: the block starts with any `{Abort}` computation `t`, such as a call to a function of your own. `use` gets its value `u`, `toOption (() => t) = Some u` and the rest.
- Each is stated with `[goal: Prop]`, as `Option.flatMapEqSome` is, and the rest of the block is found from `h`'s type by unification, so nothing about the program is written twice. Pure `let`s between steps have already been substituted. The last step of a block has no rest: `rewrite Abort.toOptionNeed at rest` turns `toOption (() => need x) = Some v` into `x = Some v`, and a block that ends in a value leaves `Some e = Some v`, for `Option.someInjective`.
- The other way, every step succeeding gives the result by computing: with the steps' equations, `rewrite foundStock, foundLabel, foundBin, enough in rfl` proves `pickOrder warehouse order = Some …`.
- [`cases`](#cases) takes a block apart too (`h: parseSmallOption s t = Some v`), when it can close every case by itself; these lemmas name what each step gave, for a proof that goes on from there.
- For `Fail.toResult (block) = Ok v`, the same with `Fail.needEqOk` (`need x msg`, `x.orFail msg`), `Fail.ensureEqOk`, `Fail.orFailEqOk` (`r.orFail`, for a `Result`: `r = Ok u`) and `Fail.thenEqOk`, closing with `Result.okInjective`. `Fail.toOption` is `toResult` with the message dropped (`Fail.toOptionToResult`).

### `Fail` and `Result`

`Std.Fail` (`crates/elab/src/std/Fail/Fail.sw`) is `Abort` with a message: code that may fail says `{Fail}`, and a failure says why ([proposals/errors.md](proposals/errors.md)). `Result a e = Ok (value: a) | Err (error: e)` is in the prelude, next to `Option`, so `Ok` and `Err` need no import, and results compare with `==`.

```
import Std (Fail)
import Std.Fail (fail, need, ensure, toResult)

def turn (t: Text): {Fail} Int :=
  let (c, rest) := need t.uncons "expected a turn, got nothing"
  ensure (c == 'L' || c == 'R') "expected L or R, got '${t}'"
  let n := rest.toIntOrFail          -- "expected a whole number, got '…'"
  if c == 'L' then -n else n

def parse (t: Text): Result Int Text := toResult (() => turn t)
```

- `Fail.fail: Text -> {Fail} a` fails wherever a value of any type is expected. `Fail.need: Option a -> Text -> {Fail} a`, and `Option.orFail` for dot notation (`o.orFail "msg"`). `Fail.ensure: Bool -> Text -> {Fail} ()` fails on `False`. `Result.orFail: Result a Text -> {Fail} a` fails with the error.
- The handlers: `Fail.toResult: (() -> {Fail | e} a) -> {e} Result a Text`, `Fail.toOption` (drops the message), `Fail.orElse: a -> (() -> {Fail | e} a) -> {e} a` and `Fail.recover: (Text -> {e} a) -> (() -> {Fail | e} a) -> {e} a`. Other abilities pass through, so `{IO, Fail}` code works: what was printed before the failure stays printed (`examples/accept/fail.sw`).
- `Fail.context label prog` puts `label: ` in front of a failure's message, and is itself `{Fail | e}`: `context "line 3" (() => turn l)` fails with `line 3: expected L or R, got 'X1'`. The `fail` in its clause goes to the next handler out, as a clause's operations do.
- With `Abort`: `Abort.orFail msg prog` turns giving up into failing with `msg`, and `Fail.toAbort prog` turns failing into giving up (the message is dropped).
- `List.map: List a -> (a -> {e} b) -> {e} List b` takes a function that may perform abilities, such as `Fail`: `t.split ',' |> .map Range.parse` fails at the first piece that isn't a range. With a pure function the row is empty and it is the plain `map`.
- `Text.toNatOrFail` and `Text.toIntOrFail` trim the text, read it, and otherwise fail with `expected a whole number, got 't'`, quoting the text as given. Messages start in lowercase, say what was expected and then what was found, and quote the found text in single quotes, which shows stray spaces.
- On `Result` (`import Std (Result)`, or by dot notation): `map`, `mapError`, `flatMap`, `toOption`, `getOrElse`, `isOk` and `traverse` (each element through a function, stopping at the first `Err`), and `Option.toResult o err`. Lemmas: `Result.okInjective`, `Result.flatMapEqOk` (`r` held some `u`, passed to a continuation that gives the goal). A `Result` crosses to JavaScript as `{ $tag: "Ok"; value } | { $tag: "Err"; error }` (`examples/extract/results.sw`).
- The operation is `Fail.stop: Text -> {Fail} Empty`, for handlers of your own; `fail msg` is `Empty.absurd (stop msg)`.
- **`main` may leave `Fail` unhandled:** `def main(): {IO, Fail} () := …` (or `{Fail} ()`, or `{IO, Fail, Partial} ()`) runs under `stitchwort run`, `run --reference`, `run --js` and in the playground. The runner performs `Fail.stop` itself, as it performs `IO.print`: what was printed before stays, `error: <message>` goes to standard error (the playground shows it below the output), and the exit status is 1. Runtime errors (`E-IO`, `E-RESOURCE`) exit with 2. `E-RESOURCE` for recursion is the runner's depth budget: 2,000,000 pending calls on `stitchwort run`, 16,000,000 (or the most the 64 GiB native stack holds for the program's widest frame) on native code, `Limits::native_frames`. A handler still can't go around partial code, so only `main` can leave a partial computation's `Fail` unhandled (`examples/accept/main-fail.sw`, `main-fail-partial.sw`).
- Proofs, each by `rfl` on each case: `Fail.toResultPure` (`toResult (() => v) = Ok v`), `Fail.toResultFail` (`Err msg`), `Fail.toResultNeed` (`toResult (() => need o msg) = Option.toResult o msg`), `Fail.toResultEnsure`, `Fail.toResultOrFail` (`toResult (() => r.orFail) = r`), `Fail.toOptionNeed` and `Abort.orFailNeed`. About any computation, each by `match reify` ([Proofs about effectful code](#proofs-about-effectful-code)): `Fail.toResultThen t k` (`toResult (() => k (t ())) = Result.flatMap (toResult t) (x => toResult (() => k x))`), `Fail.toOptionThen` (the same with `toOption` and `Option.flatMap`), `Fail.toOptionToResult t` (`toOption t = (toResult t).toOption`), `Abort.toOptionThen`, and `Fail.toResultMap f xs` (`toResult (() => xs.map f) = Result.traverse xs (x => toResult (() => f x))`).

### `Each`

`Std.Each` (`crates/elab/src/std/Each/Each.sw`) runs the rest of a computation once for each element of a list and collects every result, as Scala's `for`/`yield` or Haskell's list monad do ([proposals/each-ability.md](proposals/each-ability.md)).

```
import Std (Each)
import Std.Each (each, require)

def pairs (n: Nat): List (Nat, Nat) := Each.collect (() =>
  let a := each (1 ..= n)
  let b := each (a ..= n)    -- may depend on `a`
  require (a + b == n)                -- drops this choice unless it holds
  (a, b))
```

- `Each.each: List a -> {Each} a` and `Each.require: Bool -> {Each} ()`.
- `Each.collect: (() -> {Each} a) -> List a` gives the results in order, the first choice varying slowest. `Each.collectIn: (() -> {Each | e} a) -> {e} List a` is the same with other abilities passing through; the handler outside decides, so `Abort` outside `Each` gives up on everything, and inside it gives up on one choice.
- The operations are `Each.fork: () -> {Each} Bool` (both answers) and `Each.stop: () -> {Each} Empty` (none); `each` is a loop of `fork`s. An operation can't be polymorphic, so there is no `each` operation of its own.
- Proofs: `Each.collectEach k xs` (`collect (() => k (each xs)) = xs.flatMap (x => collect (() => k x))`, by induction), `Each.collectRequire k ok` (`collect` of `require ok` then `k()` is `if ok then collect k else []`, by `rfl` on each case), `Each.collectPure v` (`[v]`, by `rfl`) and `Each.collectEachSelf xs` (`xs`).

### Proofs about effectful code

A handler applied to a computation whose shape is known computes, so a proof about `Fail.toResult (() => need o msg)` splits on `o` and is `rfl` in each case. A law about *any* computation `t: () -> {Fail} a` needs to split on what `t` does. `match reify t with` does that, with clauses written as a handler's ([proposals/proof-reification.md](proposals/proof-reification.md)):

```
theorem Fail.toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k (t ())) = Result.flatMap (Fail.toResult t) (x => Fail.toResult (() => k x)) :=
  match reify t with
    | return x => rfl          -- `t` finished with `x`
    | Fail.stop msg, _ => rfl  -- `t` failed with `msg`
```

- In each clause, `t ()` in the goal (and in the types of the variables in scope) is replaced by what it did, as a `match` on an expression generalises it ([`match`](#match)), so the handlers in the goal compute. The second name in an operation's clause (`_` here) is the rest of the computation, a function from what the operation returns: `| State.get (), rest =>` has `rest: s -> {State s} a`.
- The thunk is a function `() -> {A, B} t` or written in place, `match reify (() => f x) with`. Its row must list its abilities and be closed: `{Fail}` or `{State Nat, Fail}`, not `{Fail | e}` or `{e}`, and not `Partial` (`E-REIFY`). There must be a `return` clause and one clause for each operation of the row (`E-NONEXHAUSTIVE`); an operation of an ability not in the row is `E-ABILITY`.
- It splits once: the first thing the computation does. Laws about computations that resume (`State`) by induction on everything they do aren't supported yet.
- **Proofs only.** `reify` may be used only in a declaration whose result is erased: a `theorem`, or a `def` whose type ends in `Prop` or a type (`def Finished (t: () -> {State s} a): Prop := match reify t with …`), including the local definitions and `match`es inside it. Anywhere else (a `def` that computes data, a `test`, an `instance`, an `export`) it is `E-PROOF-ONLY`: what it gives depends on how a computation is represented, so it must never run. To act on a failure at run time, use a handler.
- **Programs can't take a computation apart either.** `Effect.Comp`'s constructors (`Done`, `Call`) and the definitions that match on it (`Effect.foldComp`, `Effect.bind`, `Effect.translate`, `Effect.runPure`) may be named only in a declaration whose result is erased (the same test), or in a signature or a type. In a `def` that computes data, a `test` or an expression it is `E-PROOF-ONLY`; the standard library is exempt. A program can still pass a computation as a thunk, run it, and give it to a handler: that is all it can do with one. A hand-written tree is only for proofs, and a predicate about one is a `Prop`:

  ```
  def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Prop
    | Done value => Unit
    | Call () rest
  ```
- `reify` is a keyword only right after `match`; elsewhere it's an ordinary name. `match h: reify t` is refused: the equation would be between computations, whose type has no spelling.
- `examples/accept/reify-fail.sw` has the laws, `Fail.toResultMap` (by induction on the list, with a split on `f x` and then on the rest), and one-step splits of a user's `State` computation.

## `Text` helpers

Characters are Unicode scalar values, as for `Text.length`. The text comes last.

- `Text.take t n`, `Text.drop t n`: the first `n` characters, and the rest (all of `t`, or `""`, if it is shorter).
- `Text.get t i`: the character at index `i`, counting from 0, or `None` past the end.
- `Text.count t p`, `Text.any t p`, `Text.all t p`: how many characters satisfy `p`, whether some do, and whether all do; each is the `List` version on `Text.toList`, and a lemma says so.
- `Text.startsWith t p`, `Text.endsWith t s`, `Text.contains t p`: `Bool`s. The empty text starts, ends and occurs in every text.
- `Text.stripPrefix t p`, `Text.stripSuffix t s`: `Some` of `t` without `p` (or `s`), or `None`.
- `Text.splitOn t sep`: splits at each whole occurrence of `sep`, left to right without overlaps: `"a, b".splitOn ", "` is `["a", "b"]`, `"aaa"` on `"aa"` is `["", "a"]`. There is always at least one piece. An empty `sep` doesn't split: the result is `[t]` (as Lean's `String.splitOn`). `Text.split` splits on one `Char`.
- These take the text being examined first and the pattern second, so `line.stripPrefix "L"`, `line |> Text.stripPrefix "L"` and `Text.stripPrefix line "L"` all say the same: `Some` of `line` without a leading `"L"`. Read `t.startsWith p` as "`t` starts with `p`"; `p.startsWith t` is the other way round and type-checks, since both are `Text`, so mind which one is the subject.

Proved: `Text.stripPrefix (p ++ t) p = Some t`, `Text.startsWith (p ++ t) p = True`, `Text.take t n ++ Text.drop t n = t`.

## `Option` helpers

`Std.Option` (`crates/elab/src/std/Option/Option.sw`) has the helpers that save a nested `match` on an `Option`. All are reached by dot notation or a pipe (`x |> .filter p`), and each is defined by matching on its options, so a proof can `match e:` on them.

- `Option.map x f`, `Option.flatMap x f`, `Option.getOrElse x d`: the value changed, changed to an option, or the default. `Option.fold x none some` is `none` for `None` and `some v` for `Some v`.
- `Option.isSome x`, `Option.isNone x`: `Bool`s. `Option.any x p` is `False` for `None`, `Option.all x p` is `True`, and both are `p v` for `Some v`. `Option.filter x p` keeps `Some v` only when `p v`.
- `x.orElse y` is the first `Some` of the two. `x.merge both y` (same type) and `x.alignWith left right both y` (two types) combine two options: a lone value stays (through `left` or `right` for `alignWith`), two values go through `both`, and neither gives `None`.
- Lemmas: `Option.someInjective`, `Option.orElseEqSome` (`x.orElse y = Some v` means `x = Some v`, or `x = None` and `y = Some v`), `Option.mapEqSome`, `Option.flatMapEqSome` (`x` held some `u`, passed to a continuation that gives the goal) and `Option.filterEqSome` (`x = Some v` and `p v = True`), with `Option.orElseNone`, `Option.orElseSome` and `Option.noneOrElse` for computing.

## Grid helpers

For puzzles over a grid of rows. A row of a known width is a `Vec a width`. The row comes first and the fill or pad value after it, so dot notation reads `row.shiftRight 0`.

- `Vec.shiftRight v fill`: element i moves to i + 1, the last element drops off and `fill` comes in at the front (`[1, 2, 3]` gives `[0, 1, 2]`). `Vec.shiftLeft v fill` is the other way round (`[2, 3, 0]`).
- `Vec.around v pad f`: `f left x right` for each element and its two neighbours, with `pad` past either end. It is `Vec.zipWith3 (v.shiftRight pad) v (v.shiftLeft pad) f` (`Vec.aroundShifts`), in one pass.
- `Vec.tabulate n f`: `[f 0, …, f (n - 1)]`, where `f` takes a `Fin n` (as `Vec.get` does).
- `List.transposeFill rows fill`: pads every row with `fill` to the longest row's length (`List.maxLength rows`), then transposes, so no column loses a cell. `List.transpose` keeps only as many columns as the first row is long.
- These are in `std/Vec/Grid.sw` and `std/List/Grid.sw` (`tabulate` is in `Vec.sw`). A program loads those files only if it uses one of these names.

The lemmas read a result one index at a time with `Vec.getOr v i d` (element i, or `d` past the end; it is `List.getOr v.toList i d`), which is the form a proof about one column rewrites with. `i < n` is the row's width. The left neighbour is written `Vec.getOr (VCons pad row) i pad`: at `Succ c` it computes to `Vec.getOr row c pad`, and at 0 it is `pad`.

- `Vec.getOrShiftRight v i d fill (h: i < n)`: index i of `v.shiftRight fill` is `Vec.getOr (VCons fill v) i d`.
- `Vec.getOrShiftLeft v fill i`: index i of `v.shiftLeft fill` is index `Succ i` of `v`, with `fill` as the default, at every i. `Vec.getOrShiftLeftLt` takes any default and needs `i < n`.
- `Vec.getOrAround v i d pad (h: i < n) f`: index i is `f` of indices i - 1, i and `Succ i`, read with default `pad`.
- `Vec.getTabulate` (`Vec.get (Vec.tabulate n f) i = f i`) and `Vec.getOrTabulate d n f i h` (`= f (Fin.ofNatLt n i h)`).
- `Vec.getOrZipWith` and `Vec.getOrZipWith3`: index i is `f` of index i of each input, when `f` maps the defaults to the default; `Vec.getOrMap` the same for `map` (default `f d`). `Vec.getOrReplicate`: copies of x read with default x are x. `Vec.getOrPast`: past the end, `getOr` gives the default. `Vec.getOrGet`: in range it is `Vec.get`. `Vec.headOrGetOr`: `headOr d v` is index 0.
- `Vec.extGetOr u d v h`: vectors equal at every index are equal. `Vec.sumByGetOr v d f`: `v.sumBy f` is the sum of `f` of index i over `List.range 0 n`.
- `List.transposeFillCell rows fill c r`: row r of column c is `List.getOr row c fill` of row r, with no bounds on r or c (cells past the ends are `fill` on both sides). `List.transposeFillColumns` states the whole result as columns read by index. `List.getOrTransposeFill` gives column c as a list. `List.lengthTransposeFill`, `List.lengthColumnTransposeFill` and `List.lengthLeMaxLength` give the lengths.

## `decreasing`

A definition (or theorem) whose recursion isn't on a piece of an argument
says why it ends: `decreasing e` after the result type, before `:=` or the
arms, where `e` is a `Nat` of the parameters named in the header
(docs/proposals/well-founded-recursion.md, stage 1). Every recursive call
needs a proof that `e` is smaller there: `auto` finds one in scope, or the
call gives it as `[decreasing := proof]`.

```
def digitsOnto (n: Nat) (acc: List Nat): List Nat
    decreasing n
:=
  if big: Nat.leq n 9 = False
  then digitsOnto (n / 10) ([n % 10, ..acc]) [decreasing := Nat.divTenLess n big]
  else [n, ..acc]

-- The guard style: the `if` puts its condition in scope, and `auto` finds it.
def halvings (n: Nat) (count: Nat): Nat
    decreasing n
:=
  let next := n / 2
  if next < n then halvings next (count + 1) else count

-- A theorem recursing on the same measure; `evens.unfold n` is `evens n`'s
-- own equation.
theorem evensShort (n: Nat): List.length (evens n) <= n
    decreasing n
:=
  rewrite evens.unfold n in
  match n with …
```

- `:=` may start a line of its own after `decreasing e`, at the
  declaration's column. On one line: `def f (n: Nat): Nat decreasing n := …`.
- **A plain `if` gives its condition to the recursive calls under it**
  (docs/proposals/decreasing-with-hypothesis.md, stage 1): `c = True` in the
  `then` branch and `¬(c = True)` in the `else` for a `Bool` `c` (`if
  Nat.leq (i + 1) bound then f bound (i + 1) else i`, which `omega` proves
  from it), or the proposition and its negation for one such as `a % b < b`,
  as `if _: …` would. Naming it, `if h: …`, is needed only to use `h` in a
  proof written out. `f.unfold` shows such an `if` as written, a plain `if`
  with no proof, wherever only the calls' proofs used the condition; one
  whose condition something else uses, or that sits inside a function passed
  to another (`xs.map (x => if … then f … else …)`), or in an `if`'s
  condition, shows the `if _:` form, as an `if h:` always does. An `if`
  whose branches don't use its condition is the plain `if` as before
  (`examples/accept/decreasing-plain-if.sw`). If the compiler fails to
  generate this form for a definition, which would be a bug in it, the
  definition still checks, `f.unfold` shows the step `decreasing` made
  (every such `if` in the `if _:` form, every `match` with its equation),
  and `W-DECREASING-UNFOLD` says so.
- **A `match` gives its equation to the recursive calls in its arms**
  (stage 2), named or not: in `match set.popMin with | Some (least, rest)
  => f rest …`, the call's proof has `set.popMin = Some (least, rest)` in
  scope, as `match found: …` would give it, and `match n - k with | Succ j
  => f n (k + 1)` with `decreasing n - k` is proved by `omega` from `n - k
  = Succ j` alone. A fact that only a lemma turns into the decrease needs
  the name, to pass it: `match found: set.popMin with | Some (least, rest)
  => f rest … [decreasing := Set.sizePopMin set least rest found]`; the
  `E-DECREASING` message lists an unnamed one as "(this `match`'s arm)".
  `f.unfold` shows the `match` without its equation, wherever only the
  calls' proofs used it (or a `let` only they used, such as `let fewer :=
  Set.sizePopMin …`), so a proof about `f` matches on the same scrutinee,
  or rewrites it (`rewrite f.unfold x, popped in …`), as on any other: no
  `E-MATCH-MOTIVE`. A plain `if` in such an arm is shown plain too. A
  `match` inside a function passed to another (`xs.map (x => match … with
  …)`) keeps its equation in `f.unfold` if a call's proof used it.
  The unnamed equation is in scope for every proof in the arm, not only
  the decrease proofs: if another proof uses it (`predOf (n - k) omega`),
  `f.unfold` keeps it too, and says so by naming the `match`
  (`examples/accept/decreasing-match-fact.sw`).
- **A pair of measures**, `decreasing (m1, m2)`, is lexicographic (stage
  3d): every recursive call makes `m1` smaller (and `m2` may then be
  anything), or keeps `m1` the same and makes `m2` smaller. A call's proof
  is a `Nat.LexLess (m1 new) (m2 new) (m1 old) (m2 old)`, written
  `Nat.LexLess.First h` (with `h: m1 new < m1 old`) or `Nat.LexLess.Second
  rfl h` (with `h: m2 new < m2 old`, the first the same), or found:
  `[decreasing := omega]` tries the first and then the second from the
  arithmetic facts in scope, and `auto` (no proof given) does the same from
  the hypotheses in scope, so a guard works as for one measure. A recursive
  call may sit in another's arguments, as in Ackermann's function:

  ```
  def ack (m: Nat) (n: Nat): Nat
    decreasing (m, n)
  :=
    match m, n with
      | Zero, n => n + 1
      | Succ k, Zero => ack k 1 [decreasing := omega]
      | Succ k, Succ j => ack k (ack (Succ k) j [decreasing := omega]) [decreasing := omega]

  -- Two counters, guard style: `auto` builds each call's proof from the `if`.
  def minutesLeft (hours: Nat) (minutes: Nat): Nat
    decreasing (hours, minutes)
  :=
    let earlierMinute := minutes - 1
    let earlierHour := hours - 1
    if fewerMinutes: earlierMinute < minutes then 1 + minutesLeft hours earlierMinute
    else if fewerHours: earlierHour < hours then 1 + minutesLeft earlierHour 59
    else 0
  ```

  Both parts are `Nat`s of the header's parameters; a longer tuple isn't
  supported yet. Write a proof with the constructors rather than a lemma
  that takes the numbers as arguments: `stitchwort test` computes a lemma's
  number arguments, and with a nested call one of them is the inner call's
  result, computed again at every level (`examples/accept/decreasing-lex.sw`).
- `f.unfold: (x…) -> f x… = <the body, with f in its recursive calls>` is
  generated for every `def` with `decreasing` (not for a theorem). `f x`
  doesn't unfold by itself on an argument that isn't known; `rewrite
  f.unfold x in` takes one step. On known arguments it computes: tests and
  `rfl` work as for any definition.
- A recursive call may be inside a function passed to another, when that
  one has a **congruence lemma** (stage 3a): `List.sumBy xs (d => if h: d < n
  then weight d else 0)` needs the proof of `d < n` like any recursive
  call (here `h`), and the compiler's own proofs use `List.sumByCong`. The
  lemma is found by name, the function's own name and `Cong`, beside it, and
  must say: given the function's parameters in order, each function
  parameter twice (`f1`, `f2`), and then `(x…) -> f1 x… = f2 x…` for each,
  the two calls are equal. `std` has `List.mapCong`, `List.foldLeftCong`,
  `List.sumByCong`, `List.filterMapCong` and `List.occurrencesCong`; your
  own functions can have them too:

  ```
  theorem List.sumByCong [auto add: Add b] (xs: List a) (f1: a -> b) (f2: a -> b) (ef: (x: a) -> f1 x = f2 x):
      List.sumBy xs f1 = List.sumBy xs f2
  ```

  The function may be in a `let`, take several arguments (`List.foldLeft
  (acc x => …)`), `match` on its argument, and sit inside another such
  function; a `theorem` with `decreasing` may recurse inside any function
  (it needs no lemma).
- When there's no cheap guard to test, `List.attach` (stage 3b) gives the
  function its proof instead: `xs.attach` is the elements of `xs`, each a
  `List.Member a xs`, a record of the element (`value`) and the proof that
  it's in `xs` (`isIn: List.Mem value xs`). A fact about membership turns
  `isIn` into the decrease, written in the call:

  ```
  0 ..< n |> .attach |> .sumBy (({ value = d, isIn }) =>
    if Nat.divides d n then f d [decreasing := And.right ((List.memRange d 0 n).forward isIn)] else 0)
  ```

  `List.Mem x xs` is `List.Any (y => y = x) xs`, so on a written-out list
  it computes to a chain of `Or`s. The facts: `List.memRange` (`a <= x`
  and `x < b` in `List.range a b`, an `↔`; `List.memRangeFrom` is the same
  for `List.rangeFrom c s`), `List.memFilter`, `List.memMap`,
  `List.memMapAny` and `List.memAppend`. Once the call is made the proofs
  can be dropped: `List.attachValues`, `List.sumByAttach` and
  `List.mapAttach` say that mapping or summing over `e.value` is the same
  as over `xs`. At run time `attach` builds the list of records (returning
  `xs` itself is a later optimisation).
- Refused, with `E-DECREASING`: a recursive call `auto` can't prove smaller
  (the message shows the goal and the hypotheses in scope); one inside a
  function passed to a function with no congruence lemma, or one of the
  wrong shape (the message says which and why); one inside a function
  stored in data, passed to a local variable, or returning a function
  (comparing functions would need function extensionality); a measure that
  uses no header parameter, definitions that call each other, a recursive
  call in an `if`'s condition, a measure with more than two parts, and a
  body that returns a function. A measure that isn't a
  `Nat` is `E-TYPE-MISMATCH`. A definition that never calls itself gets
  `W-DECREASING-UNUSED`.
- A recursive call written with a dot (`rest.total`) works when `auto`
  finds the proof; one that gives `[decreasing := …]` is written in prefix
  form.
- `decreasing` is a keyword.

## Opaque definitions

An **opaque** definition is checked like any other (its body against its
type, its termination, its effects) and runs like any other, but while other
declarations are checked it has a type and no body: no comparison, `rfl`,
`match` or `rewrite` looks inside it (docs/proposals/opaque-definitions.md).
A call of it is compared with another call of it by the arguments, as a
function variable's would be. It's opaque *to the checker*, not private: the
body is in the source, and `f.unfold` states it. The checker's kernel
enforces it too, and it's part of the definition's hash.

```
opaque def generateLevel (depth: Nat): {Random} Plan :=
  …

-- A declaration that needs the body says so after its type.
theorem generateLevelDepth (depth: Nat) (seed: Nat):
      (seeded seed (() => generateLevel depth)).level.depth = depth
    unfolding generateLevel
:=
  …

-- Or it rewrites with the generated equation.
theorem doubleTwo: double 2 = 4 := rewrite double.unfold in rfl
```

- **`opaque def`**, with or without parameters, arms, effects or
  `decreasing`; `export opaque def` for an export. `opaque theorem` is
  refused (a theorem already stays folded where it's used), and so is
  `opaque instance` (an instance is used by taking it apart), each
  `E-PARSE`. Top level only: a local definition can't be `opaque`.
- **`unfolding f, g`** after the result type (and after `decreasing e`):
  within this declaration's body, `f` and `g` unfold as usual. Its type is
  still checked with every opaque definition hidden. Unfolding is
  transitive: unfolding `f` also unfolds what `f` unfolds, and, for
  definitions that call each other, `f`'s opaque group-mates. `:=` may start
  a line of its own after it, as after `decreasing`.
  - Allowed on `opaque def` and on `theorem`; a theorem with `unfolding`
    stays folded even under `case` and `J`. On a plain `def` it's
    `E-UNFOLDING-TRANSPARENT` (a definition that always unfolds would carry
    the body to places where it's hidden: make it `opaque`, or rewrite with
    `f.unfold`); on an instance, `E-PARSE`; on a local definition, `E-PARSE`
    (a `match` or local definition in a body with `unfolding` unfolds what
    the body does).
  - Each name must be an opaque definition (`E-NOT-OPAQUE`), not one checked
    together with this one, which has no body yet (`E-UNFOLDING-GROUP`).
  - Not with `decreasing` yet (`E-DECREASING`).
- **`f.unfold`**: every opaque `f` without an `unfolding` clause gets the
  theorem `f.unfold (x…): f x… = f.%body x…`, where `f.%body` is a copy of
  the body that computes when something looks inside it (a comparison, a
  `match`), and is otherwise shown by name, as is `f.unfold` itself. So
  `rewrite f.unfold in rfl` proves `f 2 = 4`; a proof that needs to
  rewrite inside the body, or to compute through it inside arithmetic, says
  `unfolding f`. A definition with `decreasing` keeps the `f.unfold` that
  `decreasing` makes. One with an `unfolding` clause gets none, since its
  equation may not be well-typed with what it unfolds hidden (`opaque def
  start: Code unfolding Code := 0`: `start = 0` compares a `Code` with a
  `Nat`); naming it is `E-NO-UNFOLD-EQUATION`.
- `opaque` and `unfolding` are keywords.

Examples: `examples/accept/opaque-*.sw`, `examples/reject/opaque-*.sw`.

## Generated equations

(SW-1035, SW-1067; docs/proposals/function-equations.md.) Every `def` with
arms gets a theorem for each arm: **`f.eqK`** for arm K, counting from 1 in
the order written (`f.eqK.or1`, `f.eqK.or2`, … for the alternatives of an
arm with or-patterns). Each says what a call of `f` on that arm's patterns is:

```
def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | n => 0
```

gives `kind.eq1: kind 3 = 1`, `kind.eq2: kind 7 = 2` and `kind.eq3 (n: Nat)
(notArm1: n ≠ 3) (notArm2: n ≠ 7): kind n = 0`. An arm that an earlier arm
overlaps takes **a hypothesis for each overlap** (`notArmJ`, or `notListed:
c ∉ [...]` for characters), so the equation is true where the arm is the one
that runs. They are ordinary theorems, proved by the compiler and checked by
the kernel: use them like any lemma, `rewrite kind.eq3 n h1 h2 in …`.

**Branches** (SW-1049). Below each arm, every way through the `if`s and
`match`es in tail position (through `let`s and local definitions, not into
arguments or `&&`/`||`) gets an equation of its own, named by the arm's and
one segment per split: `.ifTrue`/`.ifFalse` for an `if`, and for a `match`
the constructor of the alternative in lower case (`.some`, `.none`, `.cons`,
`.true`) where it is one constructor applied to variables, else `.altN`. A
`:=` body that isn't a `match` on its parameters has no arm equation, only
its branches, under `f.eq`: `gcd.eq.ifTrue`. Each branch takes the
hypothesis it was taken under:

```
def firstBig: List Nat → Option Big
  | [] => None
  | [x, ..rest] =>
    match big: Nat.leq 10 x with
      | True => Some { value = x, isBig = big }
      | False => firstBig rest

def countFresh: List Bool → Nat
  | [] => 0
  | [b, ..rest] => if fresh: b = False then 1 + countFresh rest else countFresh rest
```

gives `firstBig.eq2.true (x) (rest) (big: Nat.leq 10 x = True): firstBig
(Cons x rest) = Some { value = x, isBig = big }`, the step a proof can't
take by `rewrite`, `match` or `cases`, and `countFresh.eq2.ifFalse (b) (rest)
(notFresh: b = True): countFresh (Cons b rest) = countFresh rest`.

- **Hypotheses.** A `Bool` `if c` gives `h1: c = True` / `h1: c = False`
  (`h2`, … for later unnamed ones), as elaborated: `if 4 ≤ x` is a test of
  `Nat.leq 4 x`. `if h: p` gives `h: p` / `notH: ¬p`, except that the
  `else` of `p` = `b = True` (or `False`) is the other equation, `b = False`
  (D2186). A `match` on an expression gives its pattern's variables and `e =
  pattern`, named after the `match`'s equation (`match found: e`) or
  `isSome`, `isNone`, `isAlt2`; a catch-all takes `notAlt1`, … for the
  earlier alternatives it overlaps instead. A `match` on the arm's own
  variables puts its pattern in the left side: `takeFirst.eq2.cons (k) (x)
  (rest): takeFirst (Cons x rest) (Succ k) = Cons x (takeFirst rest k)`.
  So does one below a `match` on an expression, on a variable bound further
  up: in the left side for the definition's own variable (`repair.eq.some.succ
  (bits) (fewer) (b) (isSome: List.head [bits] = Some b): repair (Succ fewer)
  bits = Some (fewer + b)`), in the earlier alternative's pattern for one of
  its variables (`isSome: List.head name = Some 'x'`).
- **An overlapped arm's branches.** An arm after one that overlaps it is
  elaborated once for each case of the earlier arm's patterns; where a
  lifted `match` captures what a case binds, the arm has no equation of its
  own, but its branches do, stated in the arm's variables with the overlap
  hypothesis: `explode.eq3.some (depth) (left) (right) (notArm2: …) (inLeft)
  (isSome: explode (depth + 1) left = Some inLeft): explode depth (Pair left
  right) = Some (…)`.
- **Not generated** for a branch (`E-NO-EQUATION`, with the reason): one
  that computes on the proof of an `if`'s `else`, or of its `then` when the
  condition isn't an equation in a type with `DecEq` or a comparison (two
  proofs of it aren't known to be equal). A branch that only passes the
  proof where nothing computes on it (as `Fin.ofNatLt n i h` does with `h`) is
  fine; a
  `match` on several expressions, an alternative with an or-pattern, and a
  `match` whose helper copies variables whose types mention what it
  matches.
- **Messages.** `E-MATCH-MOTIVE`, `E-REWRITE-MOTIVE` and `E-REFL` on a goal
  stuck on a `match` inside `f` note which of `f`'s equations state its steps.

- **Names are reserved.** `theorem f.eq2` is `E-DUPLICATE`, and a local
  definition can't be called `eq`, `eqK` or `induct` (`E-LOCAL-DEFINITION`).
  Adding or removing an arm renumbers the arms after it; a name that no
  longer exists is `E-UNKNOWN-NAME`, whose note says which equations `f` has.
- **Which ones are useful.** A transparent definition's call with constructors
  in its arguments computes in the goal already, so `rewrite f.eq2 in …` there
  is `E-REWRITE-NOTHING` and `rfl` proves it. The equations that matter are
  those whose left side is **stuck**: an arm with overlap hypotheses (`kind
  n`, `n` a variable), a branch (stuck on its condition), and every equation
  of a `decreasing` or `opaque` definition.
- **Not generated.** An equation isn't made when it can't be stated or
  proved within bounds: a definition that performs abilities at the empty row,
  an arm with `()`, an arm whose right side is a `match` on its own variables
  (its alternatives' are), an overlapped arm whose body lifts a `match`, a
  statement more than ten times its arm's size (or a body over 65,536 nodes
  with its `let`s substituted, even where the branch stated would be
  smaller), an arm that more than 64 number hypotheses guard, or one that
  went over the kernel's step budget.
  Naming one is `E-NO-EQUATION` with the reason.
- **Where they are listed.** `stitchwort doc f` has an **Equations** section
  before the theorems: each statement with the line of its arm (`[stuck]`
  marks the ones whose left side doesn't compute), then the equations that
  weren't generated and why; `--json` has `equations` with `total`, `shown`
  (`name`, `statement`, `line`, `file`, `stuck`), `skipped` (`name`,
  `reason`) and `command`. At most 16 are shown. `search` lists them like any
  theorem, after the written theorems of the same relation and place, with
  `"generated": true` in JSON (and `· generated` in the text). Hover on a
  definition shows the count and the first four of those that were made. A
  program's equations are made with it; std's and the core's on demand, when a
  proof names one or `search` or `doc` lists them.

**Functional induction, `f.induct`** (SW-1057). A recursive definition
(structural or `decreasing`) also gets an induction principle with **one case
for each of its equations** above, named after it (`f.eq2.ifTrue.ifFalse` is
case `eq2IfTrueIfFalse`): the equation's variables and hypotheses, then an
induction hypothesis `ih` (`ih1`, `ih2`, … for several) for each recursive call
in the branch's right side, and the motive at the arm's patterns and **the
branch's right side**. So a case never rewrites with an equation: the motive
is given `f`'s result. The leading parameters that every recursive call passes
on unchanged come first, once, and aren't the motive's:

```
def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs :=
  countAbove.induct k (xs result => result ≤ List.length xs)
    omega                    -- eq1:        motive [] 0
    (x xs h ih => omega)     -- eq2IfTrue:  … → motive (Cons x xs) (Succ (countAbove k xs))
    (x xs h ih => omega)     -- eq2IfFalse: … → motive (Cons x xs) (countAbove k xs)
    xs
```

`countAbove.induct (k: Nat) (motive: List Nat → Nat → Prop) (eq1: motive []
0) (eq2IfTrue: (x: Nat) → (xs: List Nat) → (h1: k ≤ x) → (ih: motive xs
(countAbove k xs)) → motive (Cons x xs) (Succ (countAbove k xs))) (eq2IfFalse:
…): (x: List Nat) → motive x (countAbove k x)`. A proof by it needs no decrease
proofs, even for a `decreasing` definition: the generated one recurses on the
same measure with the definition's own. A statement that doesn't mention `f`
ignores the motive's last argument.

- **An inner call first.** `ack k (ack (Succ k) j)` gives the inner call's
  `ih` and then the outer's. A call under a binder whose arguments don't
  mention it (a thunk of `&&` or `||`) has its `ih` like any other.
- **Not generated** (`E-NO-EQUATION` with the reason, and in `doc`'s list): a
  definition with a case whose equation isn't generated (above), or with an
  overlap hypothesis that a number or character `match` refines; one that
  calls itself with an argument that depends on a binder (a function given to
  `List.map`) or inside a lifted `match` or local definition that isn't in tail
  position; one with a lifted `match` with a number literal above 64, or a
  nested pattern on an indexed type, or a catch-all whose earlier alternative
  differs from it only inside a field of a type parameter's type, at a type
  with variables (`Some None`, then `_`, on `Option (Option a)`); a mutual
  group. A lifted `match`'s
  catch-all alternative gets its case, taking the facts that the earlier
  alternatives didn't match (`compare x k ≠ Less`), as its equation does
  (`examples/accept/function-induct-catchall.sw`); so do number literals (`0`,
  `1`, then `_` with `x % 3 ≠ 0 → x % 3 ≠ 1`), nested patterns on types with
  several constructors (`Next after None` and `Next after (Some value)`), and
  an alternative after one it overlaps (`Some n` after `Some 0`, with `n ≠ 0`)
  (`examples/accept/function-induct-split.sw`). A definition that doesn't call itself has none
  (`E-UNKNOWN-NAME`, with a note). `theorem f.induct` beside `def f` is
  `E-DUPLICATE`.
- **Where.** Made with the equations (a program's eagerly, std's on demand);
  `doc f` lists it first in its Equations section; `search` marks it
  generated.

Examples: `examples/reject/function-equations-*.sw`,
`examples/accept/function-induct.sw`,
`crates/driver/tests/proofs/function_equations.rs`,
`crates/driver/tests/proofs/function_induct.rs`.

**`match induct (f args) with`** (SW-1058) is `f.induct` written as a `match`,
with the motive worked out from the goal. `induct` is a keyword only after
`match`, followed by the call:

```
theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs :=
  match induct (countAbove k xs) with
    | eq1 => omega
    | eq2IfTrue x xs h ih => omega
    | eq2IfFalse x xs h ih => omega
```

- **The call** is `f` applied to its explicit arguments, written out: the
  fixed prefix (`k`) may be any terms; the arguments in the motive's places
  (`xs`) must be distinct variables of the context (`E-MATCH-MOTIVE`
  otherwise, saying to generalise them first). The goal must be a proposition.
- **The motive** is the goal with the call replaced by the motive's result and
  those variables by its other parameters. A variable in scope whose type
  mentions the call or one of those variables (and, in turn, one whose type
  mentions that one), including a hypothesis, is generalised as a `match` on an
  expression does: the motive takes it as a premise, each alternative sees it
  under its own name with its type refined to the case, and each `ih` takes it
  as a premise. `found` in `examples/accept/match-induct.sw` is one: the third
  alternative's `ih` is `firstBig rest = Some y → …`, and its body is `ih
  found`. A hole `?` shows these refined types
  (`examples/goals/match-induct.sw`).
- **An alternative** is `| case b1 b2 … => body`, named after a case of
  `f.induct` (the equation's name, `eq2IfTrue`). The names bind the case's
  variables, then its hypotheses, then its induction hypotheses, in
  `f.induct`'s order and all of them; `_` ignores one. A goal that is an
  implication isn't introduced by the names: the body is a function
  (`| eq1 => none => cases`). Alternatives come in any order.
- **Errors.** `E-INDUCT-CASE`: a name that isn't a case, two alternatives for a
  case, or the wrong number of names (each says the cases or the names
  expected). `E-NONEXHAUSTIVE`: a case without an alternative (the message lists
  the cases). `E-NO-INDUCT`: `f` has no `f.induct`, with the reason it wasn't
  made (the `E-NO-EQUATION` one, or that `f` doesn't call itself).
  `E-MATCH-MOTIVE`: the goal isn't a proposition, an argument isn't a
  variable, or the motive worked out doesn't give the goal back (the goal
  mentions the call where it can't be abstracted, as with a `match` on an
  expression); write `f.induct` out in that case.
- It is exactly `f.induct` applied to the prefix, the motive, the cases (the
  alternatives, each a function of its names and of the generalised
  variables), the variables, and the generalised variables, so the kernel
  checks it as it does the explicit form.

Examples: `examples/accept/match-induct.sw`, `examples/goals/match-induct.sw`,
`examples/reject/match-induct-*.sw`.

## `Partial`

A function that might not finish says `Partial` in its row, and so does
everything that runs it (docs/proposals/partial.md, stage 1). It's written
like an ability, but it has no operations and can't be handled; `Partial`
is reserved.

```
def collatzSteps: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (next n)     -- no termination check

-- run by `stitchwort run`
def main(): {IO, Partial} () := IO.print "${collatzSteps 27}"

-- A helper that's given a recursive function must be polymorphic in the
-- rest of its row (`| e`): the recursive calls are requests that only the
-- recursive definition can answer.
def useP (k: Nat -> {Partial | e} Nat) (n: Nat): {Partial | e} Nat := k n

def loop: Nat -> {Partial} Nat
  | 0 => 0
  | n => useP loop (n - 1)
```

- Calling a partial function in code whose type doesn't say `Partial` is
  `E-PARTIAL`. Mentioning one is fine: `u => collatzSteps 3` is a total
  value, and partial functions can be passed around and stored.
- A total function fits where a partial one is expected; not the other way
  round. A row with abilities and a tail, `{A | e}`, is total, so a handler
  can't run a partial computation (`E-PARTIAL`), though its clauses may.
  A row variable used only bare, `{e}`, may stand for a partial row, so
  `List.map xs f` takes a partial `f` and is then partial itself, and so
  does `List.filter`. A callback whose type has no row must finish.
- Definitions that call each other must be all partial or all total
  (`E-PARTIAL-MIXED`). A partial one is partial once it has the parameters
  its arms or parameters name: `def mk (n: Nat): Nat -> {Partial} Nat :=
  …` is total, returning a partial function.
- Inside its definition, a partial recursive function as a value can't be
  passed to a helper with a fixed row (`E-PARTIAL-CALLBACK`) or returned
  (`E-PARTIAL-ESCAPE`); its type parameters come first and every recursive
  call passes them on unchanged (`E-PARTIAL-NONUNIFORM`).
- Only `stitchwort run` (on either runtime, or with `--js`), an executable from `stitchwort build`, `stitchwort test` and the playground run
  partial code. A test may call partial code, with nothing extra to write: it's a runtime check, and `stitchwort test` runs it as `stitchwort run` runs a partial `main`, with no tick limit, so a test that never finishes is a bug for whoever ran it to stop (D1183);
  the checker never does.

## Expressions

Loosest-binding first:

| Syntax | Meaning |
|---|---|
| `x y => e` | Function |
| `(x y: A) -> B` | Dependent function type |
| `[x y: A] -> B` | Function type with implicit parameters, filled in by the compiler |
| `[auto x: P] -> B` | An implicit proof of `P`, found from hypotheses in scope or a decision procedure (an `instance` returning `Decidable …`; an equation is decided by its type's `DecEq`); or, for an interface `P` (`[auto ord: Ord a]`), an instance ([Interfaces](#interfaces)) |
| `[auto P] -> B` | The same without a name, for an interface (`[auto Pretty a]`): it can't be referred to or passed by name |
| `byDecision` | A proof of a closed proposition with a decision procedure, by running it: an `[auto h: P]` argument under a name (`theorem t: Enter ∈ keys := byDecision`; `import Std (byDecision)`; [`byDecision`](#bydecision)) |
| `if c then a else b` | On a `Bool`, or on a proposition with a decision procedure, as `if _: c then a else b` (Lean's way): `if x < y`, `if n <= hi`, `if d != 0` work on `Nat` and `Int`. It is the same term whether or not a branch uses the proof, `Decidable.elim` on the decision, which computes to a case on the decision's test (`Nat.leq x y` for `x <= y`), as the `Bool` `if` on that test does: a `match` on the test, or on the decision, refines it, and its branch equations (`f.eq.ifTrue`) have the `Bool` hypotheses `t = True` and `t = False` on the decision's test `t` when the branches don't use the proof. `c` is tried as a `Bool` first, exactly as before, so a `Bool` condition (`if xs == ys`) means what it always has; only if that fails is `c` tried as a proposition, with everything the first try did undone. A proposition nothing decides is `E-AUTO-NONE` at the condition (`E-INSTANCE-NONE` for an equation in a type without `DecEq`, as `if f = g` on functions); a condition that's neither is the `Bool` error. So do `&&`, `\|\|` and `not` on comparisons: `if x < y && y < z`, `if not (x < y)`. A condition that performs operations must be a `Bool` |
| `if h: P then a else b` | Decides `P` (at runtime if need be). `h: P` in `a`, `h: ¬P` in `b`. The branches may be proofs, in a theorem: `if h: m < n then Inl h else Inr omega` (SW-1015) |
| `A -> B` | Function type |
| `A -> {E, F \| e} B` | Function type whose calls may perform abilities `E` and `F`, plus whatever `e` stands for |
| `handle e with \| return x => … \| op x, k => …` | Runs `e`, handling one ability |
| `match e with \| p => a \| q => b` | Takes apart `e` by patterns; `match h: e with` also names an equation ([`match`](#match)) |
| `()` | The unit value, and its type |
| `(A, B)`, `(a, b)`, `(p, q)` | Tuples: `Pair A B`, `MkPair a b` and the pattern `MkPair p q`, by identity (a user's own `Pair` doesn't change it). Three or more nest to the right: `(a, b, c)` is `(a, (b, c))`. Where a type is expected (a function's domain, a definition of type `Type`) it's the type; otherwise it's the type if its first component's type is a universe. `(e)` is grouping, there is no one-element tuple, and an annotation inside needs brackets: `(a, (b: T))` or `((a, b): T)`. Components are in `Type` (not `Prop`), as `Pair`'s are |
| `x \|> f a b` | Pipe forward: `f x a b`, the value becoming the first argument. Tighter than comparisons, `&&` and `\|\|`, looser than `++` and arithmetic; left-associative. See [Pipe forward](#pipe-forward-) |
| `a \|\| b` | Or. On `Bool`s it's `if a then True else b`: `b` is evaluated, and its operations performed, only if `a` is `False`. Where a proposition is expected (a type, or `if h: …`) it's `Or a b` (constructors `Inl`, `Inr`), decided by `Decidable.or`. Looser than `&&`; groups to the right. See below |
| `a && b` | And. On `Bool`s it's `if a then b else False`: `b` is evaluated only if `a` is `True`. Where a proposition is expected it's `And a b` (constructor `Both`), decided by `Decidable.and`. Looser than `=`, `==` and `<`; groups to the right. See below |
| `a = b`, `a != b` | Equality and inequality (propositions). Not associative |
| `a == b` | Whether `a = b`, as a `Bool`, from the type's `DecEq` instance ([Interfaces](#interfaces)), as `if h:` and `!=` do. The library has instances for `Nat`, `Int`, `Bool`, `Char`, `Text`, `Ordering`, and for lists, tuples, `Option` and `Vec` of types with one (`[(1, "a")] == [(1, "a")]`). A declared data type or record gets one derived when it's declared, if its fields can all be compared: data with `DecEq`, the type itself, the type inside `List`, `Option` and pairs (a nested type, `Packets (items: List Packet)`, also `List (List T)` and `Option (T, Nat)`), or proofs of equations in types with `DecEq` (`type Dir = | L | R`, recursive types, `Tree Nat` for `type Tree (a: Type): Type = …`, value parameters). A module's own `instance T.instDecEq: DecEq T` replaces the derived one. `List (Nat -> Nat)` is `E-INSTANCE-NONE`, naming the element type that has none; so is a type with a function field, another proof field or a type field, or defined together with others (mutual), or nested in another container (`Vec T n`, a type of the program), with a note saying why (naming the container) |
| `a < b`, `a <= b` | Comparisons on `Nat` and `Int` (propositions, decided by computation), and through `Ord` on every other type with one. Not associative, but `<` and `<=` chain together: see [Chained comparisons](#chained-comparisons) |
| `a > b`, `a >= b` | `b < a` and `b <= a`: the same terms, so goals, messages and the printer show `<` and `<=`. No interface, no laws of their own. Same level as `<`; `>` and `>=` chain together, see [Chained comparisons](#chained-comparisons). Since `a > b` is `b < a`, `b` is the left operand and is evaluated first (the language is pure, so only the order of effects in an operand could show it). Usable wherever `<` is: `if x > 0`, conditions, tests, theorem statements (`theorem t (h: b < a): a > b := h`) and `calc` chains. `>>` isn't an operator |
| `a ..< b`, `a ..= b` | A range of `Nat`s: `List.range a b`, the numbers from `a` up to, not including, `b`; and `List.range a (b + 1)`, through `b`. A list, so every list function works on it. Binds more loosely than `++`, tighter than the comparisons and `\|>`; not associative. See [Ranges](#ranges) |
| `a ++ b` | Joins two texts (`Text.append`) or two lists (`List.append`). Binds more loosely than `+`, and groups to the right |
| `a + b`, `a - b` | Addition, and subtraction (stopping at zero on `Nat`). Left-associative |
| `a * b`, `a / b`, `a % b` | Bind tighter than `+`. `/` and `%` are total, as in Lean: `a / 0 = 0` and `a % 0 = a`, on `Nat` and every `Int` division. Lemmas that need `b ≠ 0` (`Nat.modLt`) ask for it |
| `-e` | Prefix minus; it makes its arithmetic `Int` ([Numbers](#numbers)). Binds tighter than `*` `/` `%` and looser than application and dots: `-x.abs` is `-(x.abs)`, `-18 % 100` is `(-18) % 100`. As an argument it needs a space before the `-` and none after it, after an operand: `f -5` is `f (-5)`, `f -x` is `f (-x)`, `f -x.abs` is `f (-(x.abs))`, `f -g x` is `f (-g) x`, and `f -2 * 3` is `(f (-2)) * 3` (a negative argument takes one atom, with its dots and `()` calls, as any argument does). Anything else is as above: `n-1`, `n - 1` and `n- 1` subtract, so `n -1` with `n: Nat` is an error (`E-NOT-A-FUNCTION`, with a note: write `n - 1`). A line break counts as a space, so an indented line `-x` continues the line above as a negative argument, while a block line `-y` at the block's column is a new statement. A `-` glued to a number, with no name, number or closing bracket touching it on the left, is part of the number: `-1.abs` is `(-1).abs`, `f -1.abs` is `f ((-1).abs)`, `-3.sub 5` is `(-3).sub 5`, but `x-1.abs` is `x - (1.abs)`, `- 1.abs` is `-(1.abs)` and `-x.abs` is `-(x.abs)`. For a `Float` that changes a method on a negative literal: `-2.5.floor` is `-3.0` and `-2.5.abs` is `2.5` (before, `-2.0` and `-2.5`). May repeat, and `a - -b` needs the space (`--` starts a comment) (docs/proposals/negative-arguments.md, `examples/accept/negative-arguments.sw`) |
| `(-k)` | In a pattern: a negative `Int` number, in brackets (or as a tuple component, `(-1, 0)`), numerals only. A constructor's argument may be written `Some -1` (a space before the `-`, none after), as `Some (-1)` |
| `f a b` | Application |
| `!a` | `not a`: prefix "not", written as `-` is. Binds tighter than `*` `/` `%`, `<`, `&&` and the rest, and looser than application and dots: `!xs.isEmpty` is `!(xs.isEmpty)`, `!f x` is `!(f x)`, `!a && b` is `(!a) && b`, `!x > y` is `y < (!x)`. May repeat (`!!a`). An argument `!` follows the rule for an argument `-` (a space or a continuation line break before it, none after it, an atom next, and not at the start of a block line): `f !x` is `f (!x)`, `f !x.done` is `f (!(x.done))`, and `f !g x` is `(f (!g)) x`. `x !in xs` is the separate operator `!in`. Like `not`, it's `Bool.not` on a `Bool` and `Not` where a proposition is expected, and `a != b` is unaffected |
| `not a` | `Bool.not a`; where a proposition is expected, `Not a`. Only when `not` is the library's (a local `not` is an ordinary function) and has one argument: `List.map bs not` is `Bool.not` as a function. See below |
| `f (x := e)`, `f [x := e]` | Supplying the explicit or implicit parameter `x` by name. See [Named arguments](#named-arguments) |
| `_` | A hole the compiler fills in |
| `?` | A goal: a part not written yet. The checker says what must go there. See [Goals](#goals-) |
| `x`, `Nat`, `Succ` | Names. Constructors and data types start with an uppercase letter |
| `0`, `42`, `-5` | Numeric literals: a `Nat`, or an `Int` where one is expected (`Nat` by default; also a `Fin n`, `SafeNat` or `SafeInt` where one is expected); `-5` is an `Int` (or a `SafeInt`). See [Numbers](#numbers) |
| `'a'`, `'\n'`, `'\u{1F600}'` | `Char` literals: one Unicode scalar value. Escapes are `\n`, `\t`, `\r`, `\\`, `\"`, `\'`, `\$` and `\u{…}` with 1–6 hex digits; `\u{…}` must name a scalar value, so `'\u{D800}'` is an error. Text literals take the same escapes |
| `"héllo"` | `Text` literal: a sequence of Unicode scalar values (see [text-and-io.md](proposals/text-and-io.md)) |
| `"""` … `"""` | `Text` literal over several lines. See "Text blocks" below |
| `include "inputs/day04.txt"` | The `Text` in a file, read when the program is checked. See [`include`](#include) |
| `Type`, `Type 1`, `Prop` | Universes, `Type n` for `n` up to 65534. `Type 65535`, the largest universe, is the type of `Type 65534`; it parses, but has no type itself, so writing it is `E-UNIVERSE`, and a larger level is `E-PARSE` (docs/core.md, "Universes") |
| `(e: T)` | Type annotation |
| `[a, b, c]` | `List` literal. In an expression, `[x := e]` supplies an implicit argument and every other `[…]` is a list |
| `{ name = e, age }`, `{ p \| age = e }` | Record literal (with an expected type) and update ([Records](#records)). After a `:` or an arrow, `{` followed (after its `}`) by a type starts an ability row instead |
| `e.name` | A field, or dot notation: `T.name e …` for `e: T`, with `e` as the first argument. No spaces around the `.`; binds tighter than application; `f().x` is `(f()).x` (`name()` with no space is a call) |
| `.name`, `.drop 1` | Method section: `x => x.name`, `x => x.drop 1` (`Text.drop x 1`). A space before the `.` (or a bracket or line start). At the start of an expression it takes the rest: `(.id == id)` is `x => x.id == id`. See [Method sections](#method-sections) |
| `(== 'S')`, `(k +)`, `(&&)` | Operator section: `x => x == 'S'`, `x => k + x`; a bare operator is `a b => a && b`. Not `-`: `(- 1)` is the number. See [Operator sections](#operator-sections) |
| `rfl` | Proof of `a = a` |
| `J (y p => P) base proof` | Transport along an equality |

**Interpolation.** Inside a text literal, `${e}` inserts `e` converted by its type's `Show` instance ([Interfaces](#interfaces)): `"Part 1: ${solvePart1 turns}"` is `"Part 1: " ++ Show.toText (solvePart1 turns)`, and `"n = ${2 + 3}"` is `"n = 5"`. Text and characters are inserted as they are (`"${"tea"}"` is `tea`), and quoted inside lists, tuples, records and constructors (`"${["a", "b"]}"` is `["a", "b"]`). The expression may contain braces and nested text literals, as in `"${f "x"}"`. A `$` not followed by `{` is an ordinary character; write `\$` for a literal dollar sign: `"cost: \$5"`.

**Text blocks.** A text literal over several lines is written between `"""` and `"""`, as Java's text blocks, Swift's and Scala's multi-line strings are, for a puzzle's example input in a test:

```
def example: Text := """
  L68
  L30
    R48
  """
-- is "L68\nL30\n  R48\n"
```

- **The text starts on the line after the opening `"""`**, which holds nothing else (spaces aside); `"""x"""` is `E-PARSE`. One rule, as in Java, and a one-line text is `"x"`, so nothing is lost. The newline after the opening `"""` isn't part of the text.
- **The common indentation is removed**: the fewest leading spaces among the lines with something on them and the closing line, when `"""` is alone on it (Java's rule). So the literal can be indented with the code around it, and a closing `"""` indented less than the text keeps the difference: `"""⏎····a⏎··"""` is `"··a\n"`. Lines of only spaces don't count and become empty; spaces at the end of other lines stay. A tab in the indentation is `E-PARSE` (as in code); tabs elsewhere in a line are ordinary characters.
- **The closing `"""` decides the ending.** Alone on its own line, the text ends with a newline after its last line (`Text.lines` ignores it, so `example.lines` is the ten lines above and nothing more). Right after the last character, there is none: `"""⏎  a⏎  b"""` is `"a\nb"`. `"""⏎"""` is `""`.
- **Escapes and `${…}` are as in `"…"`**, read after the indentation is removed: `\n`, `\t`, `\u{…}`, `\$`, `\"`. A `"` or `""` needs no escape; three in a row do (`\"""`; `\"\"\"` also works). A `${…}` stays on one line (`E-PARSE` otherwise), so it can't hold a `"""` text. It ends at the `}` the lexer closes it with, so a `}` in a literal inside it (`${f "}"}`, `${g '}'}`) doesn't end it. A `--` comment inside one runs to the end of the line, so it takes the closing `}` with it; the error names the comment.
- **Line endings are read as `\n`**: a CR before an LF is dropped.
- **It is an ordinary text literal**: the same term as the `"…\n…"` it stands for, with the same hash (`crates/driver/tests/projects/compact_text.rs`), and still compact. Examples: `examples/accept/text-block.sw`.

A partially applied constructor is a function: `Succ` on its own means `n => Succ n`.

### Named arguments

`(x := e)` passes `e` for the explicit parameter named `x`, and `[x := e]` for the implicit or `auto` parameter named `x`: the brackets are the declaration's. They go in any order, mixed with positional arguments, and the call is exactly the positional one, with the same term and hash (`crates/driver/tests/elaboration/named_arguments.rs` names the arguments of every call in `examples/accept` and compares the hashes).

```
def clampTo (low: Nat) (high: Nat) (value: Nat): Nat := …

clampTo (value := 50) (high := 10) (low := 0)      -- clampTo 0 10 50
clampTo 0 (value := 50) (high := 10)               -- the same
place (y := 2) 1                                   -- place 1 2: 1 takes the first free parameter
[1, 50, 200].map (clampTo (low := 5) (high := 100)) -- value => clampTo 5 100 value
pick [label := "a"] [count := 3] 1                 -- implicits in any order
```

- **Filling.** Arguments fill parameters in the order they're written: a named one takes its parameter, a positional one the first explicit parameter still free, and implicits are inserted as for a positional call. A call means the same however it's bracketed: `(place (y := 2)) 1` is `place 1 2`, and in `(place 1) (x := 2)` the `x` is already given. A name given twice, or given after a positional argument has filled it, is `E-DUPLICATE-ARGUMENT`; a name the function doesn't have is `E-UNKNOWN-NAME`, listing its parameters (`(low)`, `[step]`); the wrong bracket is `E-NAMED-BRACKET` ("`count` is an implicit parameter: write `[count := …]`").
- **Leaving parameters out.** Explicit parameters before the last one given that the call leaves out make it a function of them, in their order, with their names: `clampTo (high := 10)` is `low value => clampTo low 10 value`, of type `(low: Nat) -> (value: Nat) -> Nat`, so `(clampTo (high := 10)) (value := 4) (low := 5)` works. Parameters after the last one given stay as in a partial application. A parameter left out is a variable of that function, never inferred from the other arguments: `use (xs := three)` with `use (n: Nat) (xs: Vec Nat n)` must work for every `n`, so it's `E-TYPE-MISMATCH`, with a note to write `(n := 3)`. Where a value is expected, such a call gets a note naming what it's still waiting for.
- **Where the names come from.** The function's declared type: a definition's or constructor's signature, a parameter's or `let`'s annotation (`let g: (start: Nat) -> (stop: Nat) -> Nat := between` renames them), an annotated expression, or a `let` without annotation that keeps its value's type. A partial application keeps the rest of the names. A type synonym, or a result type a definition computes from the parameters (`def scaler (n: Nat): Scaler n`), gives the names of what it computes to once the arguments before it are given: `scaler 2 (plus := 1) (by := 5)` is `(scaler 2) (plus := 1) (by := 5)`. Never unification: in `(if c then f else g) (low := 1)` the names aren't known (`E-UNKNOWN-NAME`, with a note to annotate). A name a function type repeats is `E-AMBIGUOUS` (pass those by position).
- **Everywhere a call is.** Dot notation (`corner.scale (plus := 1) (by := 2)`, the receiver filling the first explicit parameter), method sections (`.shift (dy := 1) (dx := 2)`), pipes (the value on the left fills the first explicit parameter still free: `5 |> clampTo (high := 3) (low := 0)`), constructors (`Circle (id := "a") (radius := 1)`) and proofs (`between (high := h) (low := l) = between l h := rfl`). A data type's parameters, and the forms of quotients, are given by position where the type is written (`List Nat`).
- **A type's parameters on its constructors** (D3514). A constructor takes its data type's parameters as implicit arguments, named as in the type's header, so they're given in square brackets whatever their bracket there: `Nil [a := Nat]`, `Cons [a := Nat] 1 Nil`, `None [a := Text]`, `MkPair [b := Bool] [a := Nat] 1 True` with `type Pair (a: Type) (b: Type)`. They mix with the constructor's fields, named or positional, and its own implicit fields (`VCons [a := Nat] [n := 0] 1 VNil`), and an `auto` parameter is named as one (`[ord := …]`). This says the type where nothing else does (`(Nil [a := Int]).length`); where the expected type says it too, they must agree, or it's `E-TYPE-MISMATCH` between the whole types ("expected `List Nat`, but this has type `List Text`"). The errors are a function's: a name that is neither a field nor a parameter is `E-UNKNOWN-NAME`, listing both ("its parameters are `[a]`, `(head)` and `(tail)`"), a name given twice `E-DUPLICATE-ARGUMENT`, and round brackets `E-NAMED-BRACKET`. By position they're not arguments: `Nil Nat` is `E-NOT-A-FUNCTION`, with a note to write `Nil [a := …]`. An implicit field of the same name as a parameter hides it, as in the declaration, so `[n := …]` still names the field. Patterns don't take them, since the type of what is matched fixes them: `| Cons [a := Nat] x _` is `E-UNKNOWN-NAME`, with a note saying so (`examples/accept/constructor-type-parameters-named.sw`, `examples/reject/constructor-type-parameter-*.sw`).
- **Run order.** In a computation, every argument runs once, where it's written, then the call, as for a positional call (`f (b := say 2) (a := say 1)` prints 2 then 1). A stage of the function (an effectful function returning a function) runs when the parameters before it are given: at the call if they're all given, and otherwise inside the function the call makes, each time it's called (with `staged: (x: Nat) -> {Log} ((y: Nat) -> (z: Nat) -> Nat)`, `staged (z := 3)` is a `(x: Nat) -> {Log} ((y: Nat) -> Nat)` that runs `staged x` when given `x`). An argument whose type needs a parameter that a later computation gives, or that the call leaves out (`use (xs := readVec()) (n := readNat())`), is `E-EFFECT-ORDER`: bind it with `let` first. A positional call gets the same error when an earlier computation's type needs a later one's result (`sized (readVec()) (say 2) rfl`, with `sized [n: Nat] (xs: Vec Nat n) (k: Nat) (same: n = k)`).

- **In the editor.** `stitchwort fmt` keeps `(x := e)` and `[x := e]` as written, with one space around `:=`. The language server offers the parameters not yet given by name when you type `(` or `[` after a function (`clampTo (` offers `low`, `high` and `value`), and hovering a name in `(x := e)` shows the parameter's type. Going to the definition from the name is not supported yet.

Examples: `examples/accept/named-arguments.sw`, `examples/accept/named-arguments-effects.sw`, `examples/reject/named-argument-*.sw`. Design: [named-arguments.md](proposals/named-arguments.md).

### Goals, `?`

`?` stands for a part of a proof or program you haven't written yet. The checker carries on past it and reports, at each `?`, the **goal**: what has to go there, after `⊢`, and the names in scope with their types (a `let`'s with its value too). A `?` can go anywhere an expression can.

```
theorem timesOne (n: Nat): n * 1 = n :=
  match n with
    | Zero => rfl
    | Succ k => ?
```

```
[GOAL] Goal: in `timesOne`
   ╭─[ add.sw:4:17 ]
   │
 4 │     | Succ k => ?
   │                 ┬
   │                 ╰── k: Nat
   │                     ⊢ k * 1 + 1 = Succ k
───╯
1 goal open
```

- **Inside a branch, the goal is the branch's.** Above, `n` is `Succ k`. Goals are shown as written, with the branch's values put in, and when what the goal computes to prints differently, a second line `computes to …` follows (dimmed in the editor and the playground, plain in the terminal; D3522). In a `True` branch, `(if True = True then n else limit) ≤ limit` is followed by `computes to n ≤ limit`; a goal that computes to the same text has one line. The `computes to` line is cut at 240 characters; hypotheses are shown as the checker has them, with no second line. There is no switch between the forms. A sum stuck on an unknown is shown with its number last, as sums are written (`x + 3`, `x + 1`), though `+` computes it to `3 + x` or `Succ x`; a `Succ` written as one, in the source or a pattern, is shown as `Succ k` (the rule: [nat-add-recursion.md](proposals/nat-add-recursion.md) §10, "Printing sums"). A name the branch replaced isn't listed; one that can't be referred to there (shadowed) is shown as `n✝`. Where nothing says what type the `?` has, the goal says "the type here isn't known yet".
- **A declaration with a `?` is unfinished, not wrong.** Each `?` becomes an *assumption* of its goal, and the declaration, and everything that uses it, is checked by the kernel assuming the goal holds (docs/proposals/using-unfinished-proofs.md): so you can state a lemma, leave its proof as `?`, and use it in the main theorem first (Lean's `sorry`), and a mistake in the main theorem is reported now. Nothing that relies on a goal is finished, or trusted, and nothing says it is: `check`, `stitchwort goal` and `audit` each say what relies on which goal (below). A use that has to compute through a `?` (`rfl` on `half 1` while `half`'s `Succ` branch is `?`) *can't be checked until the goal is filled*: it isn't checked at all, rather than being an error, and the tools say so per declaration. These are two different states, and the output keeps them apart: a declaration that *relies on* a goal was checked, assuming the goal holds; one that *waits for* a goal was not checked. A definition with a `?` also has equation lemmas (`half.eq1`, `half.eq2`); they rest on the goal too, so they're unfinished as well. A `?` whose goal can't be stated on its own (it mentions the declaration it's in, or a `match` lifted from it, or what's still unknown) isn't assumed: its declaration, and what uses it, aren't checked at all until it's filled.
- **`check` says what relies on the goals.** After the goals it prints the count, then a line for what relies on them and one for what can't be checked yet, naming each of those and the goal it waits for (D3505):

  ```
  2 goals open, allowed by `check: open-goals: warn`; `stitchwort audit` fails what relies on them
  3 declarations rely on open goals, checked assuming they hold (`stitchwort goal` lists them)
  1 declaration can't be checked until a goal is filled (not checked at all):
    Demo.halfOne  needs `half`'s goal (src/Demo/Demo.sw:11:17)
  ```

  Under the default `fail` the first line is just `2 goals open` and `check` exits 1. A line is left out when it has nothing to say. Counts are of declarations written in source; the lemmas the compiler makes for one are folded into it. The list of what can't be checked shows the first 20.
- **`check` says which declarations have errors** (SW-2943). Before the goal lines it prints the count of declarations with an error and the first three, then those that can't be checked until an error is fixed, each with the declaration with the error it needs and where that is reported:

  ```
  3 errors: in `A.broken`, `A.doubleTwo` and `A.test "own error"`
  4 declarations can't be checked until an error is fixed:
    A.twice              needs `broken` (src/a.sw:5:29)
    B.quadBroken         needs `broken` (src/a.sw:5:29)
  ```

  Each declaration counts once however many diagnostics it has, and a line is left out when it has nothing to say. Any error makes `check`, `test` and `audit` exit 1, under every setting: there is no `errors: warn`, since an open goal is a gap the author declared and an error is not (D-d of docs/proposals/tests-with-errors.md). The list shows the first 20.
- **`check` fails while any goal is open**, after printing them and "N goals open", so a project with holes never passes in CI. `test` runs the tests of what's finished, then fails the same way (unless the project allows open goals, below). `run` runs `main` if `main` is finished; if it relies on a goal it says "`main` relies on an open goal: `half`'s (src/Demo/Demo.sw:11:17), so it isn't run". `build` builds nothing while a goal is open. `eval` and the REPL refuse an expression that uses something unfinished. `axioms` lists the open goals a declaration relies on, beside its axioms: `open goal in `Demo.addComm` (src/Demo/Demo.sw:3:46): ∀ (n m: Nat) => n + m = m + n`. For a declaration that waits for a goal, it names the goal instead.
- **A project may allow open goals** (D3489, D3494, D3500): with `check: open-goals: warn` in its `stitchwort.yaml`, `stitchwort check` reports each open goal as a warning, with the same message and place, says "N goals open, allowed by `check: open-goals: warn`", and exits 0 if nothing else fails. It is for a project that is meant to have unfinished parts, such as a book's exercises. `stitchwort test` follows it too: the tests that don't use an unfinished declaration run as usual; a test whose code reaches one (directly or through what it calls) fails, and says why: `` `half` isn't written yet: its body is `?` (src/Demo/Demo.sw:11:17)``, so the run exits 1 until the function is written (SW-2909, Matt, 11 Nov 2026). A test that only mentions a theorem with an open goal still runs, and its line says what it assumes, the first three names and then `and N more`: ``✓ … ran  (assuming `exercise`)`` (proofs are erased when a test runs). The goals themselves are reported as warnings. The values are `warn` and `fail` (the default, as above); any other is `E-PROJECT-CONFIG`. Only `check` and `test` read it: `audit` still fails each unfinished theorem and everything that uses one, and `run` and `build` treat open goals as they always do. A single file given by path has no project, so it always fails.
- **`stitchwort goal` with no `--at` lists every open goal** of the project and what depends on it (D3505):

  ```
  $ stitchwort goal
  2 goals open

  `Demo.addComm`  src/Demo/Demo.sw:3:46
    ⊢ n + m = m + n
    relied on by: Demo.rearrange

  `Demo.half`  src/Demo/Demo.sw:11:17
    ⊢ Nat
    relied on by: Demo.halfZero
    can't be checked until it is filled: Demo.halfOne
    its equation lemmas (`Demo.half.eq1`, `Demo.half.eq2`) are unfinished too
  ```

  A goal's declaration is named in full, with the place of its `?`. `relied on by` are the declarations checked assuming the goal holds, directly or through what they use; `can't be checked until it is filled` are those that wait for it. Long lists show the first eight. `--json` prints `version` (1), `open`, and `goals`, each with `declaration`, `file`, `line`, `column`, `goal` (what must be shown), `reliedOnBy`, `blocking` and `equationLemmas`, in full. Exit status 0; 1 if the project doesn't check. A goal whose statement couldn't be assumed (see above) is listed with nothing relying on it.

  `stitchwort goal --summary` counts the goals per namespace instead, in the project's order, so a reader working through a book sees their progress chapter by chapter: one line each, `Book.Computing: 6 open` or `Book.Intro: done`, then `11 goals open in 2 of 3 namespaces`. With `--json` it prints `{"namespaces":[{"name":…,"open":N}],"open":N}`. Exit status 0; 1 if the project doesn't check.
- **`?` is never filled in by the compiler**, unlike `_`. Where `_` stands for a proof the compiler can't work out (`E-UNSOLVED`), the error suggests writing `?` there to see what's needed.
- Examples: `examples/goals/` (each one's goals are in `crates/cli/tests/snapshots/examples__goals__*.snap`). The design: [lsp-goal-holes.md](proposals/lsp-goal-holes.md).
- **The editor shows the goal anywhere, not only at a `?`.** The Goals panel ("Stitchwort: Show Goals") follows the cursor through the whole file: in a proof it shows the names in scope and `⊢` the goal of the expression there, in a program `expected T` (with `has type U` below it when the expression's own type differs, or `has type T` alone where nothing was expected). On a step of a proof (a `rewrite` rule, an arm's pattern, a `calc` line, a parameter, a `let`, a branch of `if h:`) it shows the goal before the step and after it, as `goal --at` does (below). It asks the server's `stitchwort/contextAt` once the cursor has rested about 0.3 s, and keeps the previous answer until the next arrives (docs/proposals/goal-at-any-point.md, stage 1). The playground has the same panel under the editor, asking the same two requests after the same pauses; it appears at the first answer, and where the server has nothing the last answer stays, dimmed, with a note (as in VS Code).

### The goal at a point, `stitchwort goal --at`

`stitchwort goal --at FILE:LINE[:COL]` prints the goal and the names in scope at a point of a file, without a `?` there (stages 2 and 3 of [goal-at-any-point.md](proposals/goal-at-any-point.md)): the command-line form of the editor's Goals panel (above), for agents and scripts.

```
$ stitchwort goal --at chain.sw:9
chain.sw:9:3
in `swap`
  a: Nat
  b: Nat
  ⊢ a + b = b + a
```

On a **step** of a proof, the place where its goal changes, it shows the goal before the step and after it, and marks with `+` the names the step brings into scope:

```
$ stitchwort goal --at basics.sw:4:26
basics.sw:4:26
in `multN0M0`, rule 2 of 2 of `rewrite`
  p: Nat
  q: Nat
  before ⊢ q * 0 = 0
  rule   q * 0 = 0
  after  ⊢ 0 = 0

$ stitchwort goal --at basics.sw:14:5
basics.sw:14:5
in `chain`, line 2 of 2 of `calc`, `_ = c`
  a: Nat
  b: Nat
  c: Nat
  h1: a = b
  h2: b = c
  so far a = b
  line   ⊢ b = c
```

- **The point**: line and column count from 1 (the column in characters); without a column, the line's first character that isn't a blank. The answer is for the step the point is on, else the smallest expression checked there, whose `range` the JSON gives. The first line after the point names the declaration, and the step if there is one.
- **Steps**: a rule of a `rewrite` (before, the rule's equation as used, after; for `rewrite … at h`, `h`'s type before and after); an arm's pattern up to its `=>` (the `match`'s goal, the pattern's variables, the arm's goal); `match … with` itself (its goal); a `calc` line up to its proof (`so far`, what the lines before it prove, and `line`, its statement); a lambda's parameter; a `let`'s name; the `then` and `else` of `if h:` (with `h: c` or `h: ¬c`); and a declaration's signature (`the statement`: its body's goal, with the parameters in scope). In a step's proof or body the answer is that expression's, as anywhere else.
- **Goals**: in a proof, `⊢` the goal: what the expression has to prove, also when it fails to (an unknown name, a proof of something else). In program code, `expected T`, and below it `has type U` when the expression's own type differs (`def widen (n: Nat): Int := n` on `n`); where nothing was expected, `has type T` alone. Goals print as `?` goals do: as written, then `computes to …` when that differs. Arithmetic computes as it is checked, so `theorem addZero (n: Nat): n + 0 = n := rfl` shows `⊢ n = n` on `rfl`, the statement as the checker holds it, with no second line. A step's `before`, `after` and `so far` lines each get the second line under them when they differ.
- **Scope**: as for `search --at`: a file on its own is read as `check FILE` sees it, and a file of a project (found from the file's folder up, or `--project DIR`; under its source folders) is read in the project through its check cache. The file is checked again with a probe at the point, so the command takes about as long as `check` of the file; the steps are recorded only for the declaration the point is in, and only on this request, never by `check`.
- **Exit status**: 0 with an answer; 2 with none there (a comment, a blank line, or a declaration whose checking stopped before the point) or for a bad argument (`E-GOAL-AT`: no line, unreadable file, a project that doesn't contain the file); 1 for a file that doesn't parse (its errors are printed).
- **`--json`**: `version` (2), `at` (`file`, `line`, `column`, as given or as the line's first character) and `declaration`, then `context`: `kind` (`proof` or `program`), `target` (the goal as written, or the expected type), `targetComputed` (what it computes to; null when it prints the same), `checked`, `hasType` (the type found, when it isn't `target`; else null), `range` (`line`, `column`, `endLine`, `endColumn` of the expression or step, 1-based, columns in UTF-16 units), `locals` (each `name`, `type` and, for a `let` of data, `value`) and `step`: null, or `form` (`rewriteRule`, `arm`, `match`, `calcLine`, `lambda`, `let`, `if`, `statement`), `description` (as the text heading says it), `range`, `index` and `of` (from 1: rule 2 of 2), `kind`, `before` and `after` (as written) with `beforeComputed` and `afterComputed` (null when the same), `adds` (the names it brings into scope), `rule` and `target` (`h` of `rewrite … at h`). On a step, `target` and `locals` are the goal after it and the names in scope there. With no answer, `context` is `null` (exit 2). An error is `{"version": 1, "error": {"code", "message"}}`.
- **Not yet**: every step of a declaration in one call (`--steps`) and the editor's Next/Previous Step commands; what `cases` split into and which facts `omega` used; goals after an error in the same branch.

### Counterexamples to a theorem

When a theorem's statement checks but its proof doesn't, or its whole proof is `?`, the compiler tries the statement on inputs: every small one first, then random larger ones. If some input makes every hypothesis true and the conclusion false, the statement itself is false, and the error (or the goal) says so in a note, with that input and, for an equation, both sides there:

```
theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a := rfl
```

```
   │ Note 2: this statement is false; a counterexample:
   │           a = 0
   │           b = 1
   │         `a - b + b = a` is false:
   │           left:  1
   │           right: 0
```

- **Only a found counterexample is shown.** Finding none says nothing, and is never a reason to think the statement is true: only a proof is. Nothing about the search can make a declaration check.
- **What's tried**: first every input up to a size, smallest first, so a counterexample found then is a smallest one: `Nat`s and `Int`s by size (0, 1, −1, 2, …), every data type and record of the program and the library by its constructors (`Bool`, `List`, `Option`, pairs, your own types), `Char`s from `'a'`, `'b'`, `'0'`, `' '`, `Text` over those (`""`, `"a"`, …), `Float`s from `0.0`, `1.0`, `-1.0`, `Fin n` and `Vec a n` for a known `n`, and maps and sets made with `Map.fromList` from lists of pairs. Then random inputs, growing to lists of 40 elements and numbers up to 40 (a list's elements share its size, so a long list's elements are small), with numbers at a machine word's edges (2^32, 2^63, 2^64 − 1, 2^64, …), any character (non-ASCII ones too), and `-0.0`, NaN and the infinities. A random counterexample is shrunk: numbers toward 0, list elements removed, each part made smaller, while it's still a counterexample. Up to 2,000 inputs (half small, half random) and about 200 ms. Random inputs are seeded from the statement, so the same statement always gets the same answer. A type parameter, `[a: Type]`, is taken to be `Nat`, and the note says `(with a := Nat)`.
- **Proof fields**: a record like `{ lo: Nat, hi: Nat, ok: lo <= hi }` is made only where its proof field holds, decided by computing it at the fields made (an equation whose sides compute to the same value, or a conjunction of them): no counterexample has `lo > hi`. A proof field that doesn't compute to equations leaves the type out.
- **Hypotheses are filters**: an input that makes one false is skipped, and later hypotheses may use earlier ones' proofs. With the hypothesis `(h: b <= a)` added, `subAdd` is true, and its (still wrong) proof gets no note.
- **What's left out, silently**: statements with a function parameter, a parameter whose type depends on another (`(n: Nat) (i: Fin n)`), a type with indices (other than `Fin` and `Vec` of a known size), a function field, or a proof field that doesn't compute to equations; and a hypothesis or conclusion nothing decides (`if` couldn't decide it either: `=` on a type without `DecEq`, `List.Sorted` written as a proposition, `Exists`).
- **`stitchwort check --only THEOREM`** (repeat the option, or separate names with commas) checks only the named theorems, by full name, in a project (SW-2310). The theorems of the namespaces named on the command line (or, if none is, the namespaces of the names) that none of the named theorems needs, and no definition or test needs, are skipped: not elaborated, not checked, not entered in the check cache (a namespace with any skipped is neither read from nor written to it). What a theorem needs is found from the names written in the declarations, so it errs towards checking more: a theorem is kept if a kept declaration of the same namespace or of one that uses it writes a name with the same last segment. The namespaces those use are checked in full. The last line says `checked N of M theorems of the namespaces named: the other K were NOT checked` (M counts the theorems of the namespaces named; K is 0 when all were needed). A name that is not a theorem of a namespace being checked is `E-UNKNOWN-THEOREM`. It cannot be combined with `--index`, `--counterexamples` or a file. A skipped theorem's name is then unchecked, so a proof that needed it without writing its name fails rather than passing.
- **`stitchwort check --counterexamples`** searches every theorem of the files or namespaces checked, its proof checked or not, with up to 10,000 inputs and 500 ms each (`--counterexample-budget 2s` for more time), prints a line for each theorem found false, `✗ name  counterexample: …`, then a count of the theorems found false, with none found (and how many of those on weak evidence, below), given up on (and how many of those because the hypotheses held in no case, below), inconclusive, and not applicable. It also prints, without `--verbose`, each theorem whose proof checked though no input made its hypotheses true: `! name  gave up: the hypotheses held in 0 of N cases (if they contradict each other, the theorem is vacuous)`, since a theorem with contradictory hypotheses proves nothing (T2 of [agentic-proving.md](research/agentic-proving.md)); not for one that concludes `Void` or a `Not`, which claims exactly that its hypotheses contradict each other. `--verbose` prints a line for every theorem: also `~ name  none in N cases (sizes up to k; evidence, not a proof)`, where k is the size of the largest input the hypotheses held for (SW-903); `~ name  none in N cases (evidence, not a proof), but the hypotheses held only for inputs up to size k of the m made: weak evidence, unless they allow no larger ones` when that is under a quarter of the largest made (`of up to k constructors of the m made` when it is their shape that stayed small: an increasing list held only short, though a list of one large number held); `- name  gave up (hypotheses true in M of N cases)` when they held in under one case in ten but some, `- name  inconclusive (ran out of steps)` and `- name  not applicable: …` (why it's out of scope). A counterexample to a theorem whose proof checked means something is wrong (an axiom it uses, the compiler, or the search), and is printed in full; any counterexample makes the command fail.
- **Trustworthy as a failing `test` is**: the statement runs on the fast runtime, and a counterexample is run again on the reference evaluator before it's shown.
- Examples: `examples/reject/counterexample-*.sw`, `examples/goals/counterexample-*.sw`. The design: [counterexample-search.md](proposals/counterexample-search.md).

### Auditing theorems, `stitchwort audit`

A theorem that checks can still be worth nothing: it may rest on an axiom you didn't mean to allow, use a lemma that is still `?`, or have hypotheses that contradict each other, so that it proves its conclusion only for inputs that don't exist. `theorem vacuous (n: Nat) (h: n + 1 = 0): n = 42 := omega` checks. `stitchwort audit` reports on each of these, and is the check a proof lane runs before it reports and the merge gate runs (SW-912, D2040; stage 1 of T1 in [agentic-proving.md](research/agentic-proving.md)).

```
stitchwort audit                       # every theorem of the project
stitchwort audit Aoc.Year2024.Day06    # a namespace's theorems, and those under it
stitchwort audit Rogue.Proofs.renderCell Rogue.Proofs.clearHead   # theorems by full name
stitchwort audit proofs.sw [NAME...]   # a file's theorems, or the ones named in it
stitchwort audit Std.List              # the standard library's
```

For each theorem:

- **Axioms** (fails): any axiom it depends on, through everything it uses, that isn't allowed, as `stitchwort axioms` finds them. The core has one axiom, `Quot.sound`, and by default it is allowed: it is part of the trusted base, as `propext`, `Quot.sound` and `Classical.choice` are Lean's. A project narrows the list in `stitchwort.yaml`, and `--allowed-axioms LIST` (comma-separated; `''` for none) overrides both:

  ```yaml
  audit:
    allowed-axioms: []
  ```

  A name in either that isn't an axiom is an error.
- **Open goals** (fails, never passes whatever `--allowed-axioms` says: an open goal isn't an axiom): the theorem has a `?`, or relies on one through what it uses (`status: assuming`: the kernel checked it assuming the goal holds), or can't be checked until one is filled (`status: unfinished`). Each is named with the place of its `?`, the first three and then "and N more":

  ```
  ✗ Demo.addComm
      fail: has an open goal (src/Demo/Demo.sw:3:46)
  ✗ Demo.rearrange
      fail: relies on an open goal: `addComm`'s (src/Demo/Demo.sw:3:46); checked assuming it holds
  ✗ Demo.halfOne
      fail: can't be checked until `half`'s goal (src/Demo/Demo.sw:11:17) is filled
  audited 3 theorems: 3 failed, 0 with warnings, 0 passed (2 rely on open goals, 1 not checked)
  ```

- **Errors** (fails; SW-2943). A project with errors is still audited: every theorem gets its verdict, and the run exits 1 whatever they are, with `(K errors in the project)` closing the summary line. A theorem with an error is `status: failed`; one that uses a declaration with an error and so can't be checked until it is fixed is `status: waiting`, with `error` (the `declaration` with the error, and its `file`, `line` and `column`) in the JSON, and `summary.errors` counts the project's. A theorem that doesn't touch an error still passes: the kernel checked it against final declarations only.

  ```
  ✗ A.doubleTwo
      fail: has an error (src/a.sw:9:36)
  ✗ A.twiceOne
      fail: can't be checked until `broken` is fixed (src/a.sw:5:29)
  audited 3 theorems: 2 failed, 0 with warnings, 1 passed (2 errors in the project)
  ```

  A theorem that relies on a declaration with an error, whose statement stands in for it (D3527), isn't waiting: it is `status: assuming`, with that declaration in `openGoals` (`kind: error`): ``relies on `doubleTwo`, which has an error (src/a.sw:9:36); checked assuming its statement``, or ``can't be checked until `broken` (src/a.sw:5:29) is fixed``.

- **Vacuous hypotheses** (warns): the counterexample search (above, but with up to 1,500 inputs and 2 s each as a backstop, `--counterexample-budget`, so that the warnings are the same from run to run unless a statement is slow to run) found no input that made every hypothesis true. If they contradict each other, the theorem is vacuous. This is evidence, not proof: a narrow hypothesis (a list of exactly 50 elements, a monster at exactly the cell given) can hold for none of the inputs made, so read the statement. A theorem that concludes `Void` or a `Not` claims its hypotheses contradict each other, and isn't warned about. Generated declarations (`T.ext`, `f.eq…`) get no vacuity warning: the compiler wrote their hypotheses, so a random miss says nothing about them. `--no-search` skips the search.
- **Counterexample** (fails): the search found one to a theorem that checked, so an axiom it uses, the compiler or the search is wrong.

It prints a line for each theorem with a finding (`✗` fails, `!` warns; `--verbose`: every theorem, with its axioms and the search's verdict), then `audited N theorems: F failed, W with warnings, P passed`, with `(A rely on open goals, E rely on errors, U not checked)` after it when there are any (`rely on errors`: checked assuming the statement of a declaration with an error). The count before the colon is of theorems written in source; when the compiler generated lemmas too, the line names them apart: `audited N theorems and M generated lemmas: …` (singular `lemma` for one). `F`, `W` and `P` count every audited declaration, written and generated. `--json` prints one object instead, for agents: `version` (2), `ok`, `strict`, `allowed_axioms`, `searched`, `summary` (`theorems` and `generated`, the written and generated counts; `failed`, `warned` and `passed` over all; `assuming` and `unfinished`, how many theorems rely on open goals and how many wait for one; `errors`, the declarations with an error in what was loaded), and `theorems`, each with `name`, `generated` (whether the compiler made it), `status` (`checked`, `assuming`, `unfinished`, `waiting` or `failed`), `openGoals` (the `declaration`, `file`, `line`, `column` and `kind` of each gap it relies on or waits for: `goal` for an open goal, `error` for a declaration with an error, whose statement stands in for it), `axioms`, `search` (`verdict`, `line`, `tried`, `held`, `refutes`) and `findings` (`check`: `axioms`, `unfinished`, `failed`, `waiting`, `counterexample` or `vacuous`; `severity`: `fail` or `warn`; `message`). It exits with 1 if any theorem fails, or with `--strict` if any warns, or if the project has any error, or if the targets can't be loaded at all; 2 for a bad `--allowed-axioms`.

Lean's `lake comparator` checks a solution against a challenge: the same statements, axioms from an allowlist, and the kernel's acceptance on replay. `audit` stage 1 does the second, and has the third through `check`; the same-statement check (`--base REV`, `--challenge FILE`) is stage 2, and changes to the program and instances a proof-only change shouldn't touch are stage 3. The vacuity warning has no counterpart in the comparator.

### Lemma search, `stitchwort search`

`stitchwort search` finds the theorems, functions and constructors whose type has a given shape, in the standard library and the project (or a file), so a lemma std already has isn't missed or proved again (SW-915; the design and its measurements: [search.md](proposals/search.md)).

```
stitchwort search 'List.length ((_: List _) ++ _) = _'      # a statement's shape
stitchwort search 'Nat → List _ → List _'                   # a function's type
stitchwort search '[auto eq: DecEq ?a] → (x: ?a) → (x == x) = True'  # `[auto]` and implicit binders work
stitchwort search --rewrite 'List.map (List.map _ _) _'     # lemmas to rewrite this with
stitchwort search '"compare", Ord.compare ?x ?x = _'        # name contains "compare", and a pattern
stitchwort search 'Shape.scale _ _ = _' --project ../shop   # another project
stitchwort search 'List.length (twice _) = _' proofs.sw     # with a file instead of the project
```

```
$ stitchwort search 'List.length ((_: List _) ++ _) = _'
 1. Std.List.lengthAppend  theorem · instance · conclusion
    [a: Type] → (xs: List a) → (ys: List a) → List.length (List.append xs ys) = List.length xs + List.length ys
    std/List/Lemmas.sw:5  (import Std (List))
 2. Std.List.lengthSnoc  theorem · instance · conclusion
    [a: Type] → (xs: List a) → (x: a) → List.length (List.append xs [x]) = Succ (List.length xs)
    std/List/Lemmas.sw:888  (import Std (List))
 3. Std.List.dropAppendLength  theorem · instance · premise
    [a: Type] → (xs: List a) → (ys: List a) → (k: Nat) → List.length xs = k → List.drop (List.append xs ys) k = ys
    std/List/SortLemmas.sw:226  (import Std (List))
 4. Std.List.takeAppendLength  theorem · instance · premise
    [a: Type] → (xs: List a) → (ys: List a) → (k: Nat) → List.length xs = k → List.take (List.append xs ys) k = xs
    std/List/SortLemmas.sw:223  (import Std (List))
    `List.takeAppend` and `List.dropAppend` at a count known to be the first list's length.
4 results, filtered pass
```

A result whose declaration has a doc (above) gets one more line, its summary: `stitchwort search '"filterMap"' --definitions` ends

```
 2. Std.List.filterMap  definition
    [a: Type] → [e: Effect.Effects] → [div: Effect.Divergence] → [b: Type] → List a → (a → {e} Option b) → {e} List b
    std/List/Toolkit.sw:204  (import Std (List))
    Keeps the `Some` results, in order.
```

The summary is shown, never matched: no query finds a result by the words of its doc. A constructor has none, since its location is its type's. With only `"text"` parts, a result whose name is the text (the last component for `"filterMap"`, the whole name at a dot for `"List.filterMap"`) comes first (D2154); it used to come last, behind the theorems about it. To read what a name does, rather than find it, use [`stitchwort doc`](#what-a-declaration-does-stitchwort-doc).

**Open theorems** (SW-2839). A theorem whose own proof has an open goal `?` is usable (an assumption to what cites it, [Goals](#goals-)), so search lists it, with ` (open goal)` after its name in the text output and `"open": true` in the JSON (absent for the others). It ranks after the finished matches of equal fit (relation, place, specificity, premises and size), so a finished theorem of the same shape comes first and an open one with a closer fit still comes before a looser finished one. A theorem that merely cites an open one isn't an open theorem; it is unfinished too and isn't listed.

**The query** is parts separated by commas (a comma inside brackets or quotes doesn't separate):

- **A pattern** (at most one): an expression or a type, elaborated in the scope below. `_` is any term; `?x` is a named hole, the same term at each `?x`, also under the pattern's own arrows (`(?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤ ?c` finds `Nat.leTrans`); a lowercase name that means nothing in scope is a named hole too, so a goal can be pasted as it is printed. A leading `⊢` (or `|-`) matches conclusions only. A pattern that is only a hole (`_`, `?x`) is refused, and so is one that computes to a hole, which the error says (`List.drop _ 0` is its list argument `_`). An operator whose meaning depends on its operands' type, with nothing in its group saying it (`_ ++ _`: lists or texts; `_ + _`, `_ < _`: `Nat`, which is what it defaults to, or `Int`), is tried each way, and the results merged: the JSON's `query.resolutions` lists the readings searched. A reading what surrounds it rules out doesn't elaborate and isn't searched: in `List.length (_ ++ _) = _`, `++` joins lists.
- **A name on its own** (`List.length`, `Ord`): the type must mention it.
- **`"text"`**: the full name must contain it.

**What is searched**: every theorem, definition and constructor of the library (loaded whole, through the check cache) and of the project found from the folder you're in (or `--project DIR`), or of `FILE` instead of the project. A pattern sees the library's namespaces as `import Std (List, Map, …)` brings them and the project's as `import N (..)` does; with a file, it sees names as the file does. A project or file that doesn't check is reported in one line (how many errors, and the first; `stitchwort check` shows them all), and what checked is searched. Declarations with an open `?` aren't searched. Hidden unless `--all`: generated helpers (a `%` in the name) and the library's `…Example` theorems. `--theorems`, `--definitions` and `--constructors` narrow to those kinds (any of them together); each result says its kind. `--in NAMESPACE` (repeatable) narrows to the declarations in that namespace or one inside it, written in full (`--in Std.List`, `--in Aoc.Year2021.Day16`); one that holds nothing gives a warning. An interface's law (a field whose type is a proposition, `Ord.flip`) is a `theorem`, and so is a generated `T.ext`.

**Conjuncts**: a theorem whose conclusion is a conjunction, written (`A ∧ B`) or a call of a definition whose body is one (`Graph.distancesShortest`'s `Graph.Shortest graph sources (graph.distances (index := index) sources)`), is also searched as each conjunct, nested ones too (to three deep), where its body writes them as a conjunction (a conjunct that is a call of another definition isn't unfolded): the result is the theorem's name with `conjunct` (`left`, `right.left`), shown as `Std.Graph.distancesShortest (its left conjunct)`, with the conjunct's type, to take with `And.left (Graph.distancesShortest …)`. It ranks after declarations that match as well.

**Where a pattern matches**: the pattern is unified, two ways, with each candidate's type, its parameters opened as unknowns, without unfolding definitions first (calls are compared by their arguments, then unfolded if they differ). Each match has a **place**: `whole` (a function-type pattern against the whole type), `reordered` (its parameters matched by the candidate's in any order, the candidate having perhaps more: `Ord.compare ?x ?y = Equal → ?x = ?y` is `Ord.equal`'s after its `x` and `y`), `conclusion`, `premise`, or `subterm` (a call inside with the pattern's head); with `--rewrite` only `left` and `right`, the two sides of a conclusion stated as `=` or as `Iff`, with `equation` `eq` or `iff`. A conditional equation (`m ≤ n → Nat.min m n = m`) is a rewrite result too, its premises left open and counted in `premises`. A target of another type than the pattern's isn't tried. A target that is one of the candidate's variables (`(p: Prop) (h: p): p`) matches anything, and isn't tried; one applied to arguments (`p k`) is tried, and ranks last.

**The relation** says how the two met: `instance` (the candidate instantiates to the pattern: only its variables took structure), `generalisation` (the pattern's named holes took structure from the candidate), `commonInstance` (both did: the weakest). A written `_` may take any structure without lowering the relation; a named hole may not. Results are ranked by relation, then whether a candidate's variable absorbed the whole pattern (a lemma ending in `p x`, a computation type `{row} a`: last), place, how much the candidate's variables took (`absorbed`), how many holes took structure (`instantiated`), `premises`, the type's size, then the name.

**The filter and the relaxed pass**: a candidate is compared only if its type names every definition and data type the pattern names (`"searchTier": "filtered"`). If that finds nothing, every candidate is compared, and the results say `relaxed` with a warning: read them as weaker. For a pattern with premises (a function type), that pass still asks for a definition the pattern names (or, if it names none, a data type), and doesn't list a candidate whose own variable took the whole pattern: such patterns otherwise list `Exists.map` and `Quot.funext`, which fit nearly anything through their higher-order variables (SW-935). A conclusion pattern keeps the whole pass, since the lemma that proves a goal often names nothing the goal does. A pattern that names nothing is searched unfiltered from the start (`unfiltered`).

**Interfaces**: a pattern with an interface method at a known type (`Ord.compare (?x: Nat) ?x = _`) is searched twice, as resolved (`Nat.compareSelf`) and with the instance a hole (the generic `Ord.compareSelf`); a result found both ways is listed once, and `via` says which found it.

Each result prints its name, kind, relation and place; its type; and where it is declared, with the import line that brings it into scope. Ten are shown (`--limit N`). **Exit status**: 0 with results, 1 with none, 2 if the query doesn't parse or elaborate.

**`--json`** prints one object, the contract's version 1 (a field that changes meaning or goes changes the version; new fields don't):

```json
{"version": 1,
 "query": {"text": "List.length (twice _) = _", "elaborated": "List.length (twice ?1) = ?2",
           "names": [], "mentions": [], "holes": [], "rewrite": false,
           "kinds": ["theorem", "definition", "constructor"]},
 "searchTier": "filtered",
 "results": [
   {"name": "Main.twiceLength", "kind": "theorem",
    "type": "(xs: List Nat) → List.length (twice xs) = List.length xs + List.length xs",
    "file": "a.sw", "line": 5, "summary": null, "import": null,
    "relation": "instance", "place": "conclusion",
    "absorbed": 0, "instantiated": 1, "premises": 0, "size": 25}],
 "total": 1,
 "budget": {"candidates": 3609, "compared": 1, "outOfBudget": 0, "truncated": false,
            "exhausted": true, "internalErrors": 0},
 "warnings": []}
```

- `kind`: `theorem`, `definition` or `constructor`. `import`: the line to add, or `null` for the file's own declarations. `conjunct`: only for a conjunct (above).
- `summary`: the first sentence of the declaration's doc (above), or `null`; always present. It was added without a version change, as the contract says.
- `relation`, `place`: as above; absent without a pattern. `equation`: only with `--rewrite`. `via`: only for a pattern searched twice (`resolved`, `generic`).
- `budget`: the declarations searched, the comparisons made, those that ran out of their step budget (200,000 steps each: a match there may have been missed, and a warning says so, naming the declarations: usually std's `Float.Theory` lemmas about `magUnits 9218868437227405311`, whose own statements compute too far to compare with any `Nat` sum), whether `--limit` cut the results, whether every candidate was compared (always, in this stage), and comparisons that failed with an internal error (counted as no match; there should be none).
- An error prints `{"version": 1, "error": {"code": …, "message": …}}` and exits with 2.
- `query.resolutions`: only for a pattern searched in more than one reading (above), each as elaborated, `elaborated` first.

**The query log**: `--log FILE`, or the environment variable `STITCHWORT_SEARCH_LOG=FILE`, appends one line of JSON per search to the file (the folder must exist; a log that can't be written is a warning): `log` (the format's version, 2), `event` (`"search"`), `time` (seconds since 1970), `ms` (how long it took), `query`, `elaborated` (each reading), `options` (with `in`), `scope`, `searchTier`, `total`, `results` (each shown, with `rank`, `name`, `kind`, `relation`, `place`) and `budget`; or `error` (`code`, `message`) for a query refused. New fields and events may be added (the lemma a proof then used); a reader skips what it doesn't know. Nothing personal is written: no folder names (version 1's `cwd` is gone), and a file's path is relative to the folder the command ran in, or its name alone if it is outside it. The log is a local file; nothing is sent anywhere. It is for measuring what agents look for, and tuning the ranking from it (stage 3 of [search.md](proposals/search.md)).

### What closes this `?`, `stitchwort search --at`

`stitchwort search --at FILE:LINE[:COL]` reads the goal at the `?` there (`--at FILE --goal N` for the file's N-th goal, in source order; with neither a line nor `--goal`, the first) and lists what closes it: lemmas applied to it, with the proof to write in place of the `?`, every one checked by the kernel; then those that apply leaving goals; then rewrites (stage 2 of [search.md](proposals/search.md)).

```
$ stitchwort search --at chain.sw:5
goal 1 at chain.sw:5:73
  a: Nat
  b: Nat
  c: Nat
  h1: a ≤ b
  h2: b ≤ c
  ⊢ a ≤ c

omega alone closes it (checked by the kernel)

closes it (checked by the kernel):
 1. Nat.leTrans a b c h1 h2  [withHypotheses]
    Std.Nat.leTrans  std/core/Division.sw:41  (import Std (Nat))
 …
applies, leaving goals:
 1. Nat.leOfEq a c ?
    Std.Nat.leOfEq  std/Nat/Arith.sw:96  (import Std (Nat))
    leaves ⊢ a = c
 …
```

- **The goal** is the one the elaborator had at the `?`, its terms, not its printed text read back (SW-989): so a goal is searched whatever its printed form, with a hypothesis printed before the pattern variable it mentions (after a `match` on a constructor), a `x✝` name, a lifted `f.%match1`, a record as a constructor's argument, or a lambda whose binder the printer named like a variable in scope. A variable a proof can't name (`x✝`, a compiler-made one) is in the context but never written in a proof.
- **How**: the goal's hypotheses become fixed variables (a lemma's own variables take the goal's terms, never the other way: `instance` matches only), and the target is searched as a conclusion over every theorem and constructor of the library and the file (and definitions, for a goal that isn't a proposition), without the filter, since a lemma that fits a goal names fewer things than the goal does. A target that starts with arrows (`(n: Nat) → …`) has its variables introduced: each proof starts `n => …`. For each of the first 50 matches (`--candidates N`), those whose conclusion names more definitions first (`List.count xs p ≤ List.count xs q` before `b = True`, which every `≤` on `Nat` also fits), then in the order `search` ranks them, each premise (an explicit parameter whose type is a proposition) is filled with a hypothesis whose type fits, else left `?`; each `?` left is tried with `rfl`, `omega`, `ring`, `cases` and `byDecision`. An equation is also searched the other way round: a lemma that fits it so is suggested as `Eq.sym (L …)`. An argument nothing solved that only premises mention (`List.distinctFlatMap`'s `key`, `List.memFlatMapIntro`'s `x`) is written `_`, and where that can't be worked out, `?` for you to give, if the lemma's conclusion names a definition inside its relation (`List.Distinct (List.flatMap xs f)`, not `a ≤ c`); such a suggestion leaves goals, and is listed after the others.
- **Checked**: every proof is elaborated at the goal (its hypotheses bound as they are at the `?`) in a session with only the file loaded, as it is once pasted, and, with no `?` left, checked by the kernel. Nothing is listed as closing the goal unless the kernel accepted it.
- **The classes**: `exact` (the lemma applied to the goal's terms), `withHypotheses` (premises filled with hypotheses), `afterObligations` (premises closed by `rfl`, `omega`, `ring`, `cases` or `byDecision`, each listed; also a rewrite after which `rfl`, `omega` or `cases` closes the goal, unless that closer closes it alone), and `applicable` (it applies, leaving goals, each listed; checked by the kernel with those goals as hypotheses when they can be written so, else only elaborated). `tactics` lists the closers that close the goal on their own. A hypothesis that is the goal is a `withHypotheses` suggestion of its own (its `kind` is `hypothesis`). An `applicable` suggestion that leaves the goal itself (`Bool.canonicalTrue … ?`) isn't listed. A lemma whose conclusion names nothing (`Eq.sym`'s `b = a`, `Nat.succInjective`'s `m = n`) fits nearly any goal, so it is listed only if it closes it.
- **Rewrites**: each call in the target against the sides of every equation and `Iff` that names its head: `rewrite L … in ?` (or `rewrite <- …`), with the goal it leaves, checked, and whether `rfl`, `omega` or `cases` then closes it. Each hypothesis that is an equation or an `Iff` is tried too, each way (`rewrite <- h in ?`); its `name` is the hypothesis's. When none of those closers closes what a hypothesis's rewrite leaves, that goal is searched again for a lemma that closes it with nothing left open: `rewrite <- h in List.takeAppend xs ys`, a `withHypotheses` suggestion (at most three a rewrite).
- **The induction hypothesis**: in a declaration that is recursive (equations on `Succ n`, `Cons x rest`), calls of the declaration itself on a structurally smaller argument are tried: a variable of the goal inside a constructor of what a parameter stands for at the goal (`n` of `Succ n`, `rest` of `Cons x rest`), the other arguments as at the goal (premises filled from hypotheses) or solved by matching a side of the declaration's equation against a call of the target (`dyAfter n (step probe)`). Each is checked with the declaration bound at the goal as a hypothesis of its type: alone, as `omega [call]`, and as a rewrite (then `rfl`, `omega` or `cases`). What closes is marked `inductionHypothesis` and says that termination is checked once the proof is pasted: in a project's file it is (each closing suggestion is pasted and the namespace checked again); in a file on its own nothing checks it, so `checked` is `elaborated`. When nothing using it closes the goal, the calls are listed (`inductionHypotheses`), for a closer to use.
- **Scope**: a file on its own is read as `check FILE` sees it. **A file of a project** (the project found from the file's folder up, or `--project DIR`; the file must be under its source folders) is read in the project, from wherever you run it: `stitchwort search --at src/Aoc/Year2021/Day02/Proofs/Proofs.sw:35`. The goal is read in the file's namespace, with that file's imports (`import P (S)`, `import M (x as y)`); the candidates are the library's and the project's declarations, except the declaration being proved and whatever uses it (they aren't finished), and the namespaces that use the file's, which it can't import. The project's namespaces load through its check cache (`.stitchwort/cache`), so on a warm cache a goal of the AoC project takes about 2 s; the first run after a change checks what changed, as `check` would.
- **Names**: the proofs name things as the file can write them: a library or project declaration it doesn't import by its full name (`Shop.Spec.doubleSwap a b`), one it imports by its short name or alias, its own namespace's by their own; `import` says what would let it write a shorter name (none for its own namespace). The tactics too: `Std.byDecision` unless the file has `import Std (byDecision)`.
- **Checked in the file** (a project's file): each closing suggestion shown, and each tactic, is also pasted in place of the `?` (in brackets where the `?` is an argument) and the file's namespace checked again, the rest of the project as it was; one that leaves an error there or doesn't close the goal is dropped, with a warning saying why. Each such check checks the namespace again, seconds for one of heavy proofs, so they have a `--time` of their own: past it, after the first, the rest aren't listed, and a warning says how many. The JSON's `budget.inFile` counts them (`checked`, `rejected`, and `unchecked` if any).
- **`--in NAMESPACE`** limits the candidates as for `search`; the induction hypothesis and the goal's hypotheses are tried regardless.
- **Limits**: 50 candidates, three ways of filling each one's premises, 10 s for the search and checking (`--time 30s`; a check already started finishes); the JSON's `budget` says whether more matched than were tried (`truncated`) and whether the time ran out (`exhausted: false`). `--limit N` (10) of each list are shown.
- **Exit status**: 0 if something closes the goal, 1 if nothing does (what applies and the rewrites are still listed), 2 if there is no goal there, or (rarely, now that the goal's terms are searched) the elaborator kept no such goal and its printed statement doesn't read back (`E-SEARCH-AT`).
- **`--json`**: `version` (1), `goal` (`file`, `line`, `column`, `index`, `hypotheses` with `name` and `type`, `target`, `introduced`), `tactics` (each as the file writes it), `results` (each `class`, `proof`, `name`, `kind`, `type`, `file`, `line`, `import`, `checked`: `kernel` or `elaborated`, `obligations` with `target` and `closer`, `goals` with `target` and `lemma`, `searchRank`, and when they apply `inductionHypothesis: true` and `conjunct`), `rewrites` (each `proof`, `name`, `at`, `direction`: `leftToRight` or `rightToLeft`, `equation`, `goal`, `closes`, `checked`, `inductionHypothesis`), `inductionHypotheses` (when listed, above), `total` (`closing`, `applicable`, `rewrites`), `budget` (`candidates`, `matched`, `tried`, `maxCandidates`, `checks`, `truncated`, `exhausted`, `outOfBudget`, `internalErrors`, and in a project's file `inFile` with `checked` and `rejected`) and `warnings`. With `--log`, each `--at` search appends a line with `event: "at"`.
- **The simplest first** (`--simplest-first`; always in the editor, SW-2966): before any search, the closers are tried one at a time, cheapest first: `rfl`; a hypothesis that is exactly the goal; `byDecision`; `omega`; `ring`; and `cases`, only where a hypothesis is an equation (one that rules the case out, `h: False = True`). Each is elaborated and kernel-checked, within 0.5 s (2 s for all). The first that closes the goal is the whole answer (`"simplest": "rfl"` in the JSON, one entry in `tactics`, or one `withHypotheses` result): the search for lemmas doesn't run, so it comes back in about the time of reading the goal. Only when none closes it does the full search run, as described above, without trying those closers again. The ladder is `LADDER` in `crates/driver/src/search_at.rs`.
- **In the editor**: the language server's code actions at a `?` answer at once and never search: the splits, and "Search for a proof" (when `stitchwort.proofSearch.enabled`). Picking it runs the search (the time limit is `stitchwort.proofSearch.timeLimitMs`) through the command `stitchwort.searchProof` (arguments: `{uri, range}` of the `?`), which answers `{version, range, proofs: [{title, newText}], timeLimitMs}` with the simplest proof alone when one of the ladder below closes the goal, else the top three closing proofs (and a tactic that closes it alone), best first, or null if the text changed meanwhile; with several the editor lets you pick one, and with exactly one it inserts it without asking (D3532, with a "Proved by `rfl`" notice); either way the `?` is replaced only if it is still there. It works in a file on its own or in a project's file; in a project it reads the editor's text of the project's open files, saved or not (D3519).

### `include`

`include "path"` is a `Text` with the contents of a file, read when the program is checked: `(include "../../../../../inputs/2025/day04.txt").lines` is the lines of a puzzle input. The path is a literal in quotes, written like an argument (put it in brackets before a `.`, as above).

- **Relative to the file that has the `include`**, with `/` between names, `..` for the folder above, whatever folder `stitchwort` runs from. It must stay inside the project folder (for a file run on its own, the file's folder); a path above it, or an absolute one, is `E-INCLUDE-OUTSIDE`.
- **The contents are what is hashed, not the path.** The text becomes a literal in the definition, so editing the file reruns exactly the tests that use it, and moving or renaming it, with the same text, changes nothing. Tests in `aoc/src/Aoc/Year2025/DayNN/Tests/Input.sw` use it to check each day's answers on the committed puzzle input.
- **Errors.** `E-INCLUDE-MISSING` names the file tried (from the project folder); `E-INCLUDE-NOT-TEXT` is a file that isn't UTF-8; `E-INCLUDE-OUTSIDE` includes a path that leaves the project folder, by `..` or through a symlink; `E-INCLUDE-UNAVAILABLE` is anywhere there are no files to read: a single file in the playground (its projects read the bundled files).
- The text is one compact literal like any other, so a 20 KB input costs no more to check or hash than a 20 KB string.

### `&&`, `||` and `not`

Each has two readings, chosen by what's expected, the way `if c` chooses:

- **Where a proposition is expected** (a type: a signature, `if h: …`, an `auto` argument) they're the propositions `And a b`, `Or a b` and `Not a`, whatever their operands are: which reading applies is decided by the position, never by the operands' types (D3486). Each operand is a proposition, and a `Bool` operand `b` is read as `b = True` on its own ([A `Bool` as a proposition](#a-bool-as-a-proposition)), so `a ∧ b` on two `Bool`s is `a = True ∧ b = True`. The test fact about the `Bool` `a && b` is written with its `= True`, `(a && b) = True`: the left of `=` isn't a proposition position, so there `&&` is the test. `if h: x < y && y < z` gives `h: x < y ∧ y < z` in the `then` branch and `h: ¬(x < y ∧ y < z)` in the `else` branch. The library's `Decidable.and`, `Decidable.or` and `Decidable.not` decide them from decisions of each side; both sides are decided before these run, so `if h: p && q` decides `q` even when `p` is false. `And.left`, `And.right` and `Or.neither` take them apart. Two more propositions are in the library (`Iff` in the core, `import Std (Exists)`), written with operators of their own ([Logic notation](#logic-notation-in--and-exists)): `p <-> q` is `Iff p q`, a record of `forward: p -> q` and `backward: q -> p` (`h.forward x`; `Iff.refl`, `Iff.symm`, `Iff.trans`), and `exists (x: a) => P` is `Exists a ((x: a) => P)`, which says some `x: a` satisfies `P` (`exists (n: Nat) => n * n = 49`), built as `Witness x proof` and taken apart with `Exists.elim` or a `match` whose result is a proposition. Taking the witness out as data is `E-PROP-ELIM` (`examples/reject/exists-witness-to-data.sw`), as for any proposition with a data field.
- **Otherwise** (a `Bool` expected, as in a `def …: Bool`, a test or `if c`, or nothing known, as in `let`) it's a `Bool`, and **each operand is a condition, as `if` takes one**: a `Bool`, or failing that a proposition with a decision procedure, decided. So `x < y && y < z`, `flag && x < 3` and `not (x < y)` are all `Bool`s, and a `Bool` operand means what it always has. `a && b` is `if a then b else False` and `a \|\| b` is `if a then True else b`: `b` isn't evaluated when `a` decides the answer, and when `b` performs operations, they're performed only if `b` is evaluated. Operations in `a` are performed first. With nothing expected, if the `Bool` reading fails, the proposition reading is tried, with everything the first try did undone; if that fails too, the `Bool` reading's error is reported (`E-AUTO-NONE` at an operand nothing decides, as for `if`).
- **The right side knows the left side**, as in `if a then b else False`: when `a` is a proposition (`n != 0`, `x < y`), `b` is checked knowing that `a` holds in `a && b`, and that it doesn't (`¬a`) in `a || b`, so an `auto` argument in `b` can use it. `i < xs.length && xs.getLt i == x` works (the `getLt` needs a proof of `i < xs.length`), as does `i >= xs.length || xs.getLt i == x`; in a chain `a && b && c`, `c` knows both `a` and `b`. A `Bool` left side (`n == 0`, `xs.isEmpty`) says nothing about `b`, just as `if n == 0` doesn't: write `n != 0` or `n = 0` for the fact. When `b` needs no proof, `a && b` is the plain `if a then b else False` on the decision's `Bool`, so the library's lemmas about `&&` and `||` on `Bool`s apply to it; when it does, it's `if _: a then b else False` (`Decidable.elim`), as that `if` makes it.
- **An `if` on `a && b` knows both sides** (SW-1305): its `then` branch has the proof of `a ∧ b`, and `auto` uses each part of a conjunction in scope, so `if i < xs.length && j < xs.length then xs.getLt i` and `if i < xs.length && 0 < i then xs.getLt i` work, as do a chain `a && b && c` and a guard `| (i, j) if i < xs.length && j < xs.length => xs.getLt i`. A `Bool` operand `c` is `c = True` there (`if wanted && i < xs.length then xs.getLt i`). When neither branch uses the proof, the `if` is the plain `if` on the `Bool` `a && b`, as before, and a proof follows it with one `match e: a && b with` (`examples/accept/match-if-and.sw`); this holds also when a branch calls a recursive function or has an inner `match`, whose helper is lifted after the `if` is written: the `if` is settled on `a && b` once the helpers are lifted and are seen not to take the proof. When a branch does use the proof, a proof matches on the parts instead (`match sum == target with`, then `match 2 <= count with`), and it's `if _: a ∧ b` decided by `Decidable.andThen`, which decides `b` only once `a` holds, as `&&` evaluates it. Where `b` itself used `a`'s fact (`i < xs.length && xs.getLt i == x`), the branch doesn't get the conjunction, whose right side would mention that proof. A conjunction given as a hypothesis (`h: b ≠ 0 ∧ c ≠ 0`) offers its parts to `auto` too.

Precedence, loosest first: `->`, then `<->`, then `\|\|`, then `&&`, then `=` `!=` `==` `<` `<=` `>` `>=` `in` `!in`, then `\|>` (the full table is under [Logic notation](#logic-notation-in--and-exists)). So `a \|\| b && c` is `a \|\| (b && c)`, `x < y && y < z` needs no brackets, and `p && q -> r` is `(p && q) -> r`. `not` is a function, so `not x < y` is `(not x) < y`: write `not (x < y)`; prefix `!` binds the same way, tighter than every binary operator (`!x < y` is `(!x) < y`). The printer shows `And p q`, `Or p q` and `Not p` as `p ∧ q`, `p ∨ q` and `¬p` (D1204). A single `&` is still an error.

A test (`test "…" := e`) takes `e` as a condition too: a `Bool`, or a proposition with a decision procedure, so `test "ordered" := 1 < 2 && 2 < 3` and `test "small" := 3 < 5` work.

**Anywhere a `Bool` is expected**, a proposition with a decision procedure is decided, as Lean's `decide` coercion does: `List.filter xs (n => k * n <= size)`, `List.all xs (x => x < 10)`, `def le (a b: Nat): Bool := a <= b`. The expression is elaborated as usual; only if it turns out to be a proposition (its type is `Prop`) and the expected type is the library's `Bool` is it replaced by the test of its decision, `d.holds`, except that the standard decisions of `<=` and `<` on `Nat` and `Int` are read as the comparison itself: `a <= b` as a `Bool` is `Nat.leq a b` (`Int.leq`, `Int.less`; `a < b` on `Nat` is `Nat.leq (Succ a) b`), so it prints, computes and is generalised as that, and a `Bool` fact about it (`Bool.andLeft`, `match e: a <= b with`) is the `Nat.leq a b = True` you would write by hand. `==` and the other decisions stay the test of theirs, `d.holds` (`d.sound` and `d.complete` relate it to the proposition). A decision's test is its first field, so on `Nat` `a == b` computes to `Nat.equal a b`. A proposition nothing decides is `E-AUTO-NONE` at the expression, saying a `Bool` is expected (`List.filter (g => g = f) gs` on functions). Where a proposition is expected nothing changes, and conditions (`if c`, `&&`, `||`, `not`, `test`) still try the `Bool` reading first and then the proposition, as above.

**A comparison as a side of `=` or `!=`** is a proposition, so `(a < b) = (c < d)` is an equation between propositions. When that fails because the other side is a `Bool` (`(List.foldLeft xs 0 Nat.max < k) = (0 < k && List.all xs (x => x < k))`, whose right side is a `Bool` `&&`), the equation is read again, with everything the first reading did undone, with each comparison side as the `Bool` it decides, as if written `((… < k): Bool)`; if that fails too, the first reading's error is reported (SW-944). A goal printed with such an equation pastes back as the same term. Example: `examples/accept/comparison-beside-bool.sw`.

### A `Bool` as a proposition

A `Bool` expression `b` where a proposition is expected is the proposition `b = True` (D3482, docs/proposals/bool-as-proposition.md §4): the same term as writing `= True` out, so the two spellings hash the same. It applies in a theorem's statement, a binder's type (`(h: isSmall n)`), `∀` and `∃` bodies, a type ascription, `if h: b` and `let h: b := …`, each operand of `∧`, `∨`, `¬`, `→` and `↔` there, and an argument whose type is `Prop` (the body of `n => isSmall n` given for `Nat → Prop`). The coercion is of the whole expression: `(h: if c then a else b)` is `(if c then a else b) = True`, not an `if` between two propositions; only `&&`, `||` and `not` are taken apart first, as the connectives.

It doesn't apply where a type of data is expected (`List b` is `E-TYPE-MISMATCH`), where the expected type isn't known yet, or to a side of `=`: in `p = (a ∧ b)` with `p: Prop`, the `∧` side isn't read as a proposition, and its `Bool`s are `E-NOT-A-TYPE`, whose note says to write `= True` out. That keeps a comparison of `Bool`s from turning into an equation between propositions (`examples/reject/bool-side-of-equation.sw`).

Goals, hovers and errors print `b = True` as `b` (`h: isSmall n`, `h: ¬a`, `h: a ∧ b`), except where that text would read back as another proposition: a test whose top is `&&` or `||` keeps it (`(a && b) = True`), as do `a != b` (which would read back as `a ≠ b`), a side of `=` (`(a = True) = (b = True)`) and the constants (`False = True`). `Bool.not a = True` prints as `a.not`, never `!a`. `b = False` prints as written. The split equations `cases` reports keep `= True` too (`the case a = True, b = False`). `stitchwort doc` shows a header as it is written.

### Readings: `@[reading]` and `.read`

A fact about a test, `e = True` or `e = False` with `e: Bool`, is used as the proposition the test stands for through a **reading** (docs/proposals/bool-as-proposition.md §5, §6): a theorem marked `@[reading]` whose statement is `f x… ↔ P` (for `= True`; a `Bool` there is read as `= True` as usual) or `f x… = False ↔ P`, with the test `f` applied to the theorem's parameters, each exactly once.

```
type Within (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def within (lo x hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem withinReads (lo x hi: Nat): within lo x hi ↔ Within lo x hi := …

theorem high (lo x hi: Nat) (h: within lo x hi): x ≤ hi :=
  match h with
    | { low, high } => high

theorem low (lo x hi: Nat) (h: within lo x hi): lo ≤ x := h.read.low

theorem self (x: Nat): within x x x := { low = Nat.leRefl x, high = Nat.leRefl x }
```

- **Patterns.** A constructor or record pattern on a test fact matches the reading's `P`: `| { low, high }` above, `| Both ha hb` on `(a && b) = True`, `| Inl na` on `(a && b) = False`. Each pattern reads one layer: under it, a name binds the next test fact as it is (`Both _ rest` gives `rest: (b || c) = True`), and a nested pattern reads that in turn. In a `let` pattern too (`let Both ha _ := h`).
- **Building.** Where a test fact is expected, a constructor of a proposition (`Both ha hb`, `Inr hb`) or a record literal builds the reading's `P` and the fact from it.
- **`.read`.** `h.read` is the fact as `P`, and a field of `P` can be taken straight from the fact: `h.left` is `h.read.left`. A fact `e = False` whose test has no reading of its own reads as `¬e`.
- **Which reading.** By the test's head as written: a function's own reading, else the reading of what its definition unfolds to, one definition at a time (up to 8; an `opaque` definition isn't unfolded). Before that, a **decision's test** whose decision doesn't compute, `d.holds` for a `d: Decidable p` that is a variable or a call stuck on one (a hypothesis, or `x == y` on a type known only to have `DecEq`, whose `==` is `(DecEq.decide x y).holds`), reads as `p`, and its `= False` as `¬p`, with no `@[reading]`: the proofs are the decision's own, `d.sound h` and `d.complete q` for `= True`, `Decidable.refute d h` and `Decidable.toBoolOfNot d n` for `= False` (`examples/accept/readings-decisions.sw`). A decision that computes is read by its test: `(List.decMem x xs).holds` is `xs.contains x`, read as `x ∈ xs`. The core gives `&&`, `||` and `not` theirs: `(a && b) = True` is `a ∧ b`, `= False` is `a = False ∨ b = False`; `(a || b) = True` is `a ∨ b`, `= False` is `a = False ∧ b = False`; `not a = True` is `a = False`, `= False` is `a = True`. Std gives `xs.contains x` (`x ∈ xs`; `= True` only), `Nat.equal m n` (what `m == n` is on `Nat`: `m = n`, and `m ≠ n` for `= False`), `Option.isSome o` (`∃ x, o = Some x`; `= False` is `o = None`), `Option.isNone o` (`o = None`; `= False` is `∃ x, o = Some x`), `List.isEmpty xs` (`xs = []`), `Text.isEmpty t` (`t.toList = []`), `Set.isSubset a b` (`∀ k, k ∈ a → k ∈ b`), and `List.noRepeats`, `List.isSortedBy` and the like theirs; `Set.isEmpty` and `Map.isEmpty` read as what they unfold to. `xs.any p` reads as `∃ x, x ∈ xs ∧ p x` (`= False`: `∀ x, x ∈ xs → p x = False`) and `xs.all p` as `∀ x, x ∈ xs → p x` (`= False`: `∃ x, x ∈ xs ∧ p x = False`), and `Array`'s, `NonEmptyList`'s and `Text`'s `any` and `all` read as what they unfold to (`examples/accept/readings-any-all.sw`). Where nothing reads, `E-NO-READING` says what the test is and, for a pattern, what it reads as instead. Where a test fact is given for what it reads as (`found: xs.contains x` where `x ∈ xs` is wanted), the `E-TYPE-MISMATCH` has a note saying what it reads as and to add `.read` (`examples/reject/reading-needs-read.sw`).
- **Declaring one.** The test is the function applied to the theorem's parameters, each once, except that a function over an effect row `{e}` (`List.any: (xs: List a) → (p: a → {e} Bool) → {e} Bool`) is stated with pure arguments, `(p: a → Bool)`, which fixes its row to the empty one: a test fact's test is a `Bool`, which `{e} Bool` is only at the empty row. Such a reading fits only tests at the empty row; a test whose row may perform (a function with a `Bool` result that never calls its callback) doesn't fit, and `E-NO-READING` says so (`examples/reject/reading-impure-row.sw`). `E-READING-SHAPE` if the statement isn't an `↔` of that form, or its test passes the function more arguments than the function takes (`def tiny: Nat → Bool := small` takes none, so `tiny n` unfolds to `small n` before anything reads it: declare the reading on `small`, or write `def tiny (n: Nat): Bool := small n`), `E-READING-OVERLAP` for a second reading of the same test and polarity, and `E-READING-PLACE` unless the reading is declared where its test's function is (its namespace in a project, its file in the library), so a reading is in scope whenever its test is. Which declarations see a reading is decided by what depends on what, not by where they're written (D3537): every declaration that mentions a test function with a reading is checked after the reading, wherever it is in the file or namespace, except the reading's own dependencies (a lemma its proof uses), which read the test as what it unfolds to, as the reading's proof does; an error there says the reading isn't available because it depends on that declaration. A reading's own proof can't use it; one whose proof has an error is still filed, as its stand-in, so what reads through it relies on it, as any use of a theorem with an error does. The reading found doesn't depend on whether calls are kept folded while checking (`STITCHWORT_GLUE=0`): the test is taken from the fact's type as written. **A decision of what a test reads as** should test with that test, so `if Small n` and `if isSmall n` are one computation, which `rewrite` and `match h:` treat alike: an `instance` of `Decidable P` whose `holds`, through the decisions it is made from, isn't a call of the function a positive reading of `P` is stated for gets the warning `W-DECISION-TEST` (docs/proposals/bool-as-proposition.md §13), at whichever of the two is checked second (`examples/accept/reading-decision-test.sw`). Only the function is compared, not its arguments, which come from the decisions it is made from. Only a reading whose `P` is its head applied to the reading's own parameters, each once (`Small n`, `List.Mem x xs`), is paired: a connective or relation that std decides generically (`lo ≤ x ∧ x ≤ hi`, `n ≤ 10`) isn't, and neither is an instance that takes a decision (`Decidable.and`), whose test is built from the decisions it is given. A generated instance (a proposition record's derived decision) isn't warned about either. Both sides look only at what the module can see (its own declarations, the namespaces it depends on, the library files it needs), so the warning doesn't depend on what else a run loaded. Examples: `examples/accept/bool-readings.sw`, `examples/reject/reading-*.sw`, `examples/projects/accept/readings-across-namespaces`.

### Chained comparisons

`a <= b < c` is `a <= b && b < c`, as in mathematics (SW-1339, D2385-D2391). `<` and `<=` chain together, as do `>` and `>=`, for any number of links: `0 <= i < n`, `hi >= x > lo`, `a < b <= c < d`. Each link is the comparison it would be alone (`>` and `>=` are flipped as a single one is, the links keeping the order written), joined as `&&` joins them, grouping to the right. A chain is one operand of a longer `&&`: `lo <= x <= hi && p` is `(lo <= x && x <= hi) && p`, so `h.left` is the whole range and `h.left.left` its lower bound. It sits where a comparison does, so arithmetic and `|>` in an operand bind tighter, and it works wherever `&&` does: as a `Bool`, in an `if` or a guard (whose branch knows `lo ≤ x ∧ x ≤ hi`, so `auto` and `omega` use each part), after `if h:`, in a theorem statement or a hypothesis, and in a `test` (a failure shows the link that was false).

**The middle is computed once.** A middle operand that is a name or a literal is written twice, so the chain is the very term of the conjunction written out, with the same hash. Any other middle (`1 <= digits.length <= 3`, `0 < Parse.nat() <= 9`) is bound once, as `let x := middle; lo <= x && x <= hi` with a hidden name, and the operands run in the order written: if the first operand is also not a name or a literal it is bound first, and an operand after a link is only run if the links before it hold (`a < f x < g y < b` runs `g y` only if `a < f x`). Where a proposition is wanted (a statement, a hypothesis, the fact an `if` or a guard learns, a guard's equations) the middle is put back in place of the hidden name, so goals read `lo ≤ f x ∧ f x ≤ hi` and never show the binding; the `Bool` that runs, and the decision of an `if` or `if h:` on the chain, keep the binding, so the middle is computed once. (A chain inside a larger proposition of an `if h:`, as in `if h: p && lo <= f x <= hi`, is decided as the written-out conjunction and computes `f x` twice.)

**What doesn't chain** (also when the chain would start with it, `a = b < c`) is `E-COMPARISON-CHAIN`, with a message that says what to write: `<`/`<=` mixed with `>`/`>=` (`a < b > c`, which says nothing about `a` and `c`), `=` and `==` (for now), `!=` (`a != b != c` doesn't mean all three differ) and `in`. Write the comparisons separately, joined with `&&`. `calc` is unchanged: its steps are one relation each, and it has its own chains. A section takes one operator: `(<= 3 <= 4)` is a syntax error, write a lambda.

Examples: `examples/accept/chained-comparisons.sw`, `examples/reject/chained-comparison-*.sw`.

### Ranges

`a ..< b` is the numbers from `a` up to, not including, `b`; `a ..= b` is the numbers from `a` through `b`. Each is a call of `List.range`, so a range is an ordinary `List Nat`: `0 ..< 3` is `[0, 1, 2]`, `1 ..= 3` is `[1, 2, 3]`, `4 ..= 4` is `[4]`, and `5 ..< 2` is `[]` (an end below the start gives nothing). In a proof, `omega` and `auto` read a hypothesis `x ∈ a ..< b` (or `..=`) as `a ≤ x` and `x < b`, and prove such a goal from the two bounds (`List.memRangeBounds`, `List.memRangeOf`; also when the start is a number and the range has computed to `List.rangeFrom`). Where a `Bool` is expected, `x in a ..< b` is `List.inRange x a b`, two comparisons instead of a walk of the list; `List.inRangeIff` and `List.containsRange` relate it to the proposition and to `contains`. `a ..< b` is `List.range a b` and `a ..= b` is `List.range a (b + 1)`, so `a ..= b` and `a ..< b + 1` are the same term (`rfl`). `Nat` only for now: `"a" ..< "z"` is `E-TYPE-MISMATCH` with a note saying so (docs/proposals/ranges.md).

A range binds more loosely than `++` and arithmetic, and tighter than the comparisons, `in` and `|>`, and is not associative:

| Written | Means |
|---|---|
| `a ..< b + 1` | `a ..< (b + 1)` |
| `0 ..< xs.length` | `0 ..< (xs.length)` |
| `0 ..< n \|> .map f` | `(0 ..< n) \|> .map f` |
| `x in 0 ..< n` | `x in (0 ..< n)` |
| `0 ..< 3 == [0, 1, 2]` | `(0 ..< 3) == [0, 1, 2]` |
| `a ..< b ..< c` | `E-PARSE` |

A dot binds tighter than a range, so a method on a range needs brackets, `(0 ..< n).length`; the pipe reads better, `0 ..< n |> .map f`. In a spread a range needs no brackets: `[0, ..2 ..< n]`. Ranges are written with spaces (the formatter puts them in); a bare `a .. b` or `a..b` is `E-PARSE`, whose message names the two forms and, inside brackets (`[2..n]`), says that the spread is `[2, ..n]` and that a range needs no brackets.

`W-RANGE-IN-BRACKETS` is a warning for a list literal whose only item is a range, `[0 ..< n]`: that is a list of one list. Write `0 ..< n`; `[(0 ..< n)]` says the nesting is meant.

Goals, hovers and messages print `List.range a b` as `a ..< b`, and `List.range a (b + 1)` as `a ..= b`; they are the same term, so `0 ..< n + 1` written by hand prints as `0 ..= n`. A goal where the range has been taken apart by computation (a numeral start, `2 ..< n + 3`) shows what it computes to (`List.rangeFrom`), as any call does. The facts proofs use are `List.memRange` (`x ∈ a ..< b ↔ a ≤ x < b`), `List.lengthRange` and `List.rangeAppend`.

Examples: `examples/accept/ranges.sw`, `examples/accept/ranges-omega.sw`, `examples/accept/ranges-pipes.sw`, `examples/accept/range-in-brackets.sw`, `examples/reject/range-*.sw`.

### Logic notation: `in`, `<->` and `exists`

([proposals/logic-notation.md](proposals/logic-notation.md), D1200–D1211, D3458.) Four forms for statements about collections and logic, each with a Unicode spelling:

- **`x in c`** (`x ∈ c`) is membership, a proposition: `List.Mem x xs` for a list, and `c.contains x = True` for a `Set` or for the keys of a `Map`. Where a `Bool` is expected (`if x in seen`, `xs.filter (x => x in allowed)`, a test) it is decided, as any decidable proposition is: by `List.decMem` from the element type's `DecEq` for a list (its test is `xs.contains x`, so `if x in xs` and `if xs.contains x` are the same computation, and `List.memContains` is the reading of `contains`), and as `c.contains x` for a set or map. **`x !in c`** (`x ∉ c`) is its negation (`Not`, or `Bool.not` as a `Bool`). Anything else on the right is `E-TYPE-MISMATCH`. It sits with `=` and `<`, not associative: `x in xs && y in ys` needs no brackets, `x in xs = b` is an error. `!x in xs` is an error saying the `!` would apply to the element: write `x !in xs` or `!(x in xs)`. `in` is a reserved word.
- **`p <-> q`** (`p ↔ q`) is `Iff p q`. Not associative (`p <-> q <-> r` is an error), looser than `&&` and `||`, tighter than `->`: `p && q <-> r` is `(p && q) <-> r`, and `p <-> q -> r` is `(p <-> q) -> r`.
- **`exists (x: T) => P`** (`∃ (x: T) => P`) is `Exists T ((x: T) => P)`; several parameters, `exists (x y: Nat) => …`, nest one `Exists` each. Like a lambda it takes everything to its right, and like one it may start an expression, the right side of `<->`, or the last operand of `&&` or `||`; elsewhere it needs brackets. After a `.`, `exists` is an ordinary name (a field or method called `exists`), not the keyword.
- **`forall (x: T) => P`** (`∀ (x: T) => P`) is the dependent function type `(x: T) -> P`, the same term, so it says "for all" (D3458). The parameters are a lambda's without patterns: `(x y: T)`, implicit `[a: Type]` and `auto` ones, or a bare name whose type is inferred (`∀ n => n + 0 = n`); each group is one function type, as `(x y: T) -> P` is. The body takes everything to its right, so `∀ (n: Nat) => n > 0 -> P n` is `(n: Nat) -> (n > 0 -> P n)`, and the form goes where `exists` may. Lean's and Rocq's `∀ x, P` is `E-PARSE`, naming `=>` (`examples/reject/logic-unicode-forall.sw`); so are a pattern parameter and a default. House style: `∀` for a quantified hypothesis (`(h: ∀ (x: a) => p x)`) or a quantifier that is part of a statement; a theorem's own variables and the premises its proof names go before the colon (`theorem timesOne (n: Nat): n * 1 = n := match n with | Zero => … | Succ k => …`, D3470, D3471), not as a `∀` after it; and a function type that isn't a proposition stays an arrow. `def`s keep their arms. After a `.`, `forall` is an ordinary name.

Precedence, loosest first:

| Level | Operators | Grouping |
|---|---|---|
| 1 | `x => e`, `exists (x: T) => P`, `forall (x: T) => P` | take everything to the right |
| 2 | `->` | right |
| 3 | `<->` | none |
| 4 | `\|\|` | right |
| 5 | `&&` | right |
| 6 | `=` `!=` `==` `<` `<=` `>` `>=` `in` `!in` | none |
| 7 | `\|>` | left |
| 7.5 | `..<` `..=` | none |
| 8 | `++` | right |
| 9 | `+` `-` | left |
| 10 | `*` `/` `%` | left |
| 11 | prefix `!` `-` | |
| 12 | application, `.` | |

**Unicode spellings** (D1200). Each is the same token as its ASCII form; the formatter keeps whichever was written (D1209), and a proof written either way has the same hash:

| ASCII | Unicode | | ASCII | Unicode |
|---|---|---|---|---|
| `in` | `∈` | | `!` | `¬` |
| `!in` | `∉` | | `<=` | `≤` |
| `->` | `→` | | `>=` | `≥` |
| `<->` | `↔` | | `!=` | `≠` |
| `&&` | `∧` | | `exists` | `∃` |
| `\|\|` | `∨` | | `forall` | `∀` |

Other symbols get an error naming the replacement: `⇒` (`=>` for a lambda or match arm, `->` or `→` for implication), `λ` (`x => e`), `⇔` (`<->`), `≡` (`=`), `⊆` `∪` `∩` and the other set operators (not supported: `Set` has functions), `ℕ` (`Nat`), and so on (`crates/syntax/src/lexer.rs`, `UNSUPPORTED`). There is no user-defined notation (D1207).

**Printing** (D1204, D1211, D3458). Goals and messages show a statement's connectives in Unicode (`∧` `∨` `¬` `≠` `≤` `∈` `∉` `↔` `→`, `∃ (x: T) => P`), whichever spelling the source used, and a `Bool` computation in ASCII (`(n <= limit) = False`, `a && b`), so the two can be told apart. A function type whose result is a proposition prints as `∀ (x: T) => P`: one `∀` for a run of binders the result uses (and implicit ones), neighbours of the same type grouped, `∀ (a b: Nat) => a + b = b + a`; an unused binder is an implication, so `∀ (n: Nat) => n > 0 → P n`. A result counts as a proposition when its form shows it: an equation, a type declared in `Prop`, or a call of a definition whose type ends in `Prop`. A goal's printer also knows the types of the variables in its context, so a variable whose type ends in `Prop` (`p: Nat → Prop`) applied to arguments counts too: `∀ (n: Nat) => p n` (SW-2592). A message has no such types, so there `(x: a) → p x` stays an arrow; so does `(n: Nat) → Vec n` anywhere. Dot calls and `++` print as the source writes them (SW-1674). Comparison on `Nat`/`Int` under a binder may show unfolded (`Nat.leq k y = True`), as before.

**In a `rewrite`.** `rewrite rule in e` uses the same `in`, so a membership test in the rule needs brackets: `rewrite h (3 in xs) in rfl`. Unbracketed, the first `in` ends the rule and the second makes the body a membership test, which is `E-PARSE`, "a membership test in a `rewrite` needs brackets" (`examples/reject/logic-in-rewrite-rule.sw`).

Examples: `examples/accept/logic-notation.sw`, `examples/goals/logic-notation.sw`, `examples/reject/logic-*.sw`.

### Pipe forward `|>`

`x |> f` is `f x`, and `x |> f a b` is `f x a b`: the value on the left becomes the **first** explicit argument, which is where dot notation puts it too (`x.f a b`). That's why the library puts the main argument first (`List.map xs f`, `List.sum xs`), so a pipeline reads in the order things happen:

```
def total: Nat :=
  people
    |> List.map (p => p.age)
    |> List.sum
```

The house form writes the same pipeline with dot calls and a method section: `people |> .map .age |> .sum`.

**Library convention:** in a function that takes a main value (the collection, optional or text being operated on) plus other arguments, the main value comes **first**, then the other arguments, then any function arguments last (`xs.foldLeft 0 (acc x => acc + x)`, which suits a lambda that spans lines). Dot notation, a pipe, a method section and the prefix call then all agree: `xs.map f`, `xs |> List.map f`, `xs |> .map f` and `List.map xs f` are the same call. A function of two values of its own type is named so that `x.f y` reads as a sentence, with the subject first: `t.startsWith p`, `a.sub b`, `xs.append ys`, `p.isPrefixOf t`. Pipes are not the same as in F#, OCaml, Elm or Haskell, which pipe into the last argument; they follow Gleam and Elixir.

It binds tighter than the comparisons, `in`, `&&`, `||` and `<->`, looser than `++`, arithmetic and application, and groups to the left, as in Elixir and Gleam: `x |> f |> g` is `(x |> f) |> g`, `a + b |> f` is `(a + b) |> f`, `xs |> List.sum = 6` is `(xs |> List.sum) = 6`, `a && xs |> .length == 4` is `a && ((xs |> .length) == 4)`, and `x |> f -> T` is `(x |> f) -> T`. Piping a comparison or a conjunction needs brackets: `(a == b) |> f`.

- **Layout.** A line may start with `|>` to continue the expression, if it's indented at least as far as the line the expression starts on, even at the enclosing block's own column (as `then` and `else` may). `|>` is its own token, so it never clashes with the `|` of arms and alternatives. After a `match`, a `|>` line at or right of the last alternative's `|` continues that alternative's body (the last alternative takes what follows, as with any operator); one further left, but at least at the `match` line's column, pipes the whole `match`.
- **A lambda on the right** takes the rest of the expression: `x |> y => f y |> g` is `x |> y => (f y |> g)`, which means the same as `(x |> y => f y) |> g`.
- **The left side is checked first**, and its type is unified with the function's first explicit parameter before the other arguments are checked. So `people |> List.map (p => p.name)` knows `p: Person` when it reaches the lambda (`List.map people (p => p.name)` works the same way, since `people` comes first). A value of the wrong type is `E-TYPE-MISMATCH`, pointing at the function: "`|>` passes the value as the first argument of `List.map`, which takes `List a`; the value before `|>` has type `Text`". A function whose first explicit parameter isn't of the value's type is the same error: there is no search for a later one.
- **The left side runs first** when it performs operations, then the right side's arguments, then the call: `say "left" 1 |> add (say "right" 2)` prints `left`, then `right`.
- **A number literal on the left** is just `f 5`: it takes its type from `f`, as an argument would.

Implicit and `auto` arguments, named arguments and constructors work on the right as in a normal call; the value on the left fills the first explicit parameter they leave free (`5 |> clampTo (high := 3) (low := 0)` is `clampTo 0 3 5`, with `value` the one parameter left).

### Method sections

`.f args` is `x => x.f args`: dot notation with the receiver left out.

```
people.map .name                    -- people.map (p => p.name)
people |> .map .age |> .sum         -- (people.map (p => p.age)).sum
ls.map (.split ',')                 -- ls.map (l => l.split ',')
```

- **Chains and arguments.** `.name.length` is `x => x.name.length`. Arguments after the head section belong to it: `.drop 1` is `x => x.drop 1`. As an argument a section takes none, so bracket it: `List.map people .name`, `people.map (.greet "Hi")`. Like `e.name`, the receiver is the function's first explicit argument (`.split ','` is `t => Text.split t ','`).
- **The space rule.** A section follows a space (or a bracket, or starts the expression): `f p .name` is `f p (.name)`, while `p.name` is still a field access. `p. name` is still an error, and so are `.Name` and `.1`.
- **Pipe.** `xs |> .drop 1` is rewritten by the parser to exactly `xs.drop 1`, with no lambda, so `xs |> .drop 1 |> .sum` is `(xs.drop 1).sum`.
- **Layout.** A section can't start a continuation line as an argument: in `foo xs` followed by an indented `.map f`, the `.map f` would read as another argument of `foo`, so it's a parse error ("a line can't start with a method section"), with a note pointing to `|> .map f` or `(.map f)`. A line starting `|> .map f` is fine.
- **Checking.** A section is a lambda, so it's checked like one: against the function type expected of it (`people.map .name`, `apply .length "abc"` for `apply (f: Text -> Nat)`), after a pipe's left side, or against an annotation (`(.drop 1: List Nat -> List Nat)`). Where what it takes isn't known yet, the section waits for it, whole, and is checked once something says it ([postponement.md](proposals/postponement.md), K3): a later argument (`List.map .position ds`, or a section placed before the list it's applied to), what it's applied to (`let g := .drop 1` then `g xs`; `(.length) "abcd"`, whose result the expected type gives), or anything later in the declaration. It's then the term it is when its argument's type is known from the start, the partial application below included.
- **The partial application.** Where the receiver is the function's only explicit parameter and the section has no arguments, the section is not a lambda but the function `T.f` itself: `.snd` is exactly `Pair.snd` and `.isZero` is `Dial.isZero`, so `xs.any .snd` and `xs.any Pair.snd` are the same term, and a proof that restates a program's expression with the qualified name (`match e: Vec.any Pair.snd next with`) still finds it. A section with arguments stays a lambda: `.sub 3` is `x => Nat.sub x 3`, `.addNat 3` is `x => Mod.addNat x 3`. Implicit arguments are inserted as for the qualified name. A section with chained fields (`.name.length`), or whose arguments don't fit until the receiver's type is fixed, is a lambda too.
- **To the end of the expression (D1192).** A section that *starts* an expression (after `(`, `,`, `:=`, `=>`, `then`, `else`, `|>`) takes the whole expression, operators included: `(.id == id)` is `x => x.id == id`, `(.trim != "")` is `x => x.trim != ""`, `(.fst + 1)` is `x => x.fst + 1`, `(.fst -1)` is `x => x.fst (-1)` (a negative argument, not a subtraction: write `(.fst - 1)` for that), `(.items |> List.sum)` is `x => x.items |> List.sum`. Every binary operator counts (`+ * ++ == != < <= > >= && || in !in <->`). After a pipe, a section takes the operators tighter than `|>` (`xs |> .show ++ "!"` is `xs.show ++ "!"`), and a comparison after it compares the result: `xs |> .sum == 6` is `xs.sum == 6`. It's exactly the written-out lambda, the same term. As an argument a section still takes nothing: `f .a == b` is `(f .a) == b`. The section's argument is used once, at the start; a second section in the same expression is a separate function (`(.isZero || .isEven)` is `x => x.isZero || (.isEven)`, a type error whose note says to write the lambda). Operands run each time the function is called, as in a lambda.
- **`_.name`.** `_` is a hole, not a parameter, so `.count _.isZero` is `E-CANNOT-INFER` with the ordinary "can't tell what the value is" message and no special help (D1194). There is no placeholder for a function's argument, `_`, `it` or `$0` (D1196).
- **Unknown receiver.** A section whose argument's type nothing ever says (`let g := .drop 1` with `g` never applied) is `E-CANNOT-INFER` at the end of its declaration ("can't tell what `.drop` is applied to"), with a note suggesting a pipe, passing it where a function type is known, or an annotation.
- **No such function.** The ordinary dot-notation error: `xs |> .dorp 1` is `E-UNKNOWN-FIELD`, "`List` has no field or function `dorp`", with a "did you mean `drop`?" note. A name other languages use for something std spells differently gets the std name instead, by a table in `crates/elab/src/scope.rs` (`List.size` suggests `List.length`, `Char.isLower` suggests `Char.isAsciiLowercase`); the same for `T.name` with no function in `T` (`E-UNKNOWN-NAME`). Only names that exist are suggested.
- **Effects.** It follows lambda rules: `IO.readAllLines() |> .map (.split ',') |> .length` works in a `{IO}` function.

Examples: `examples/accept/method-sections.sw`, `examples/accept/section-unknown-receiver.sw`, `examples/reject/section-never-applied.sw`, `examples/reject/section-no-such-function.sw`, `examples/reject/section-on-next-line.sw`, `examples/accept/method-section-partial.sw`, `examples/reject/section-underscore.sw`. Design: [method-sections.md](proposals/method-sections.md), [anonymous-lambdas.md](proposals/anonymous-lambdas.md); examples for the end-of-expression form: `examples/accept/lambda-sections.sw`, `examples/reject/section-twice.sw`.

### Operator sections

An operator in brackets with one operand left out is a function of that operand (D1193), and an operator alone is a function of two (D1195). Haskell's sections, with `-` excluded.

```
xs.findIndex (== 'S')        -- x => x == 'S'
xs.filter (> 3)              -- x => x > 3
xs.map (10 +)                -- x => 10 + x
xs.map (++ "!")              -- x => x ++ "!"
xs.foldLeft 0 (+)            -- a b => a + b
rows.foldLeft True (&&)      -- a b => a && b
cs.filter (in vowels)        -- c => c in vowels
```

- **Which operators.** `+ * / % ++ = != == < <= > >= && || in !in <->` and their Unicode spellings (`∈`, `∉`, `↔`, `∧`, `∨`, `≤`, `≥`, `≠`). `|>`, `->` and `=>` are not operators in this sense: `(|> f)` would just be `f`.
- **`-` is not a section.** `(- 1)` and `(-1)` are the number; for the function write `(.sub 1)` or `(x => x - 1)`. `(k -)` is a parse error too. The bare `(-)` is subtraction, `a b => a - b`.
- **One operand, binding tighter.** The operand of `(op e)` or `(e op)` must bind tighter than the operator (`||` takes a whole `&&` chain), so `(+ 1 + 2)` and `(a + b *)` are errors with a note to add brackets: `(+ (1 + 2))`, `((a + b) *)`.
- **A lambda.** A section is exactly the lambda, the same term; `a > b` is `b < a`, so `(> 3)` is `x => 3 < x`. The type of the argument comes from where the section is used, as for a lambda, so `let f := (+ 1)` needs an annotation. A bare operator is a two-parameter lambda: `foldLeft 0 (+)` works where `(a b => a + b)` does.
- **A comparison gives a `Bool` where nothing says otherwise (SW-930).** `a < b` is a proposition, decided into a `Bool` where a `Bool` is expected. A section that compares with `<`, `<=`, `>` or `>=` (`(<)`, `(> 3)`, and a method section such as `(.fst <= 2)`) whose result type nothing has fixed yet, as when it's passed to a generic `zipWith` or `map`, is the `Bool` comparison: `depths.zipWith (depths.drop 1) (<) |> .count (deeper => deeper)` counts the increases. Where a proposition is expected (`List.All (< 5) xs`) it is the proposition. Only here does a section differ from its written lambda, `(a b => a < b)`, which stays a proposition (examples/accept/section-comparison-bool.sw).
- **Not a placeholder.** The missing operand is always at the edge. For a missing value in the middle write the lambda (D1196).

Examples: `examples/accept/lambda-sections.sw`, `examples/reject/section-minus-is-negation.sw`, `examples/reject/section-operator-chain.sw`, `examples/reject/section-operand-too-loose.sw`. Design: [anonymous-lambdas.md](proposals/anonymous-lambdas.md).

### `match`

`match` takes apart one or more values in an expression, with the same patterns as arms:

```
def describe (xs: List Nat): Text :=
  match xs with
    | []         => "empty"
    | [x]        => "one"
    | _          => "many"

def zipLen (xs: List Nat) (ys: List Nat): Nat := 1 + match xs, ys with
  | [_, ..a], [_, ..b] => zipLen a b
  | _, _ => 0
```

The alternatives start with `|`, lined up one under another and further right than the line the `match` starts on. A `match` may also be written on one line: `match n with | Zero => 0 | Succ k => k`. Several scrutinees are separated by commas, and each alternative has one pattern for each. Branches may be several lines, as in a `handle`. Alternatives are tried from top to bottom, and together they must cover every case (`E-NONEXHAUSTIVE`). A `match` that doesn't say what happens for some constructors is told every one it leaves out; see "Missing cases" below.

Patterns are those of arms: variables, `_`, numbers, constructors, tuples, record patterns and `()`. As in arms, an alternative with a `()` pattern and no `=> body` is absurd (`| Rock, ()`: see [Declarations](#declarations)), and `()` with a body is the unit pattern (on another type, the `E-TYPE-MISMATCH` says to leave out the `=>`: `examples/reject/absurd-arm-with-body.sw`). Absurd alternatives sit on lines of their own: on one line, `| Paper, () | Scissors, ()` reads `() | Scissors` as an or-pattern. A `match` can also be used in a signature (`def Pick (b: Bool): Type := match b with | True => Nat | False => Text`), and may be nested in a branch.

There are two translations. If the `match` is the whole right-hand side of a definition, and every scrutinee is an unnamed parameter that its patterns haven't already taken apart, the `match` becomes part of the definition's case tree, as if you had written more arms. Any other `match` becomes a generated definition, named after the definition it is in (shown as `owner.%match1`, though error messages say "this `match`"), which takes the values it needs from the surrounding code and is called where the `match` was. A scrutinee that is a variable is refined in the branches, and so is everything whose type mentions it. A scrutinee that is any other expression is generalised: wherever it appears in the expected type, it's replaced by the pattern of the branch.

`match h: e with` gives each branch an equation `h` about the original expression, such as `h: length xs = Zero` in the `Zero` branch. The expression is also generalised in the expected type, even when `e` is a variable. A `match` with a name is always generated as a definition. In a definition with `decreasing`, a recursive call in an arm gets the equation without the name, and `f.unfold` leaves it out ([`decreasing`](#decreasing), stage 2).

What a generalised `match` (an expression scrutinee, or any named one) replaces:

- **The goal, as written first.** Every occurrence of the scrutinee in the expected type is replaced by the pattern of the branch. The expected type and the hypotheses are first searched as written (the form goals are printed in, calls kept as calls): a subterm with the scrutinee's head is an occurrence if it is equal to it up to computation, without solving any unknown, so `xs.map (f a)` is found where the goal has `xs.map (y => f a y)` (AoC 2020 day 19). Then the branches' goals keep the calls: after `match e: flag` on `(if flag then double a else 0) = …`, the `True` branch is `double a = …`, not `a + a = …`. That result is used only if it replaces every occurrence the search below would, and differs from it only in occurrences written differently; otherwise the `match` replaces exactly what it did before (`examples/accept/match-as-written.sw`, [goal-as-written.md](proposals/goal-as-written.md) stage 2). If the search below can't run because the goal or a hypothesis is too large once its calls are computed (`solved: (start.settle plan 1000 |> …) = Some answer`, AoC 2020 day 11), which would fail with `E-RESOURCE`, the result as written is used without those checks, with the warning `W-MATCH-UNCONFIRMED`: a copy inside a call is then left unrefined, and an arm that needs it fails with its own error (`examples/accept/as-written-unconfirmed.sw`, stage 4).
- **Otherwise, the goal as it computes.** The expected type is searched in its computed form, every call as what it computes to. An occurrence is found by shape: the same term, ignoring source positions and binder names. No definition is unfolded to look for it and no metavariable is solved, so `Ord.compare y x` is not an occurrence of `Ord.compare x y`. (`a <= b` as a `Bool` is `Nat.leq a b`, so it is an occurrence of it; `a == b` on `Nat` is the test of `Nat.decEq a b`, which computes to `Nat.equal a b`, so it is an occurrence of that too.) This is how a `match` reaches a copy of the scrutinee inside a definition the goal mentions: with `isBig n` both shown and inside `label n`, both are replaced, and the branches' goals hold no calls. A closed scrutinee that computes to a constructor (`isBig 20`) has no occurrence in the computed goal, so the `match` replaces nothing, even where the goal as written shows `pick (isBig 20)`. Once the branch's pattern is put in, the goal computes further.
- **Hypotheses.** Variables in scope whose types mention the scrutinee (`h: Nat.leq a b = False -> …`), and the variables whose types mention those, are copied: in each branch they have the replaced type. Variables whose types don't mention it are left alone. A `let`-bound variable is copied like a parameter, as an opaque hypothesis: in the branches it has the replaced type, but its value is forgotten (it's no longer definitionally the value it was bound to; the value is passed in from outside, so nothing is lost for the code after the `match`). So after `let small := halfSmall n`, `match e: half n with …` lets a branch match on `small` at its refined type (`examples/accept/match-let-hypothesis.sw`).
- **The equation.** `match h: e with` adds `h: e = pattern`, about the original expression. It is the one thing in scope that still mentions `e`, so a refined hypothesis is used as it is (`rewrite h at found` finds nothing: `E-REWRITE-NOTHING` says the `match` replaced `e`). Examples: `examples/accept/match-refines-hypotheses.sw`, `examples/reject/rewrite-refined-by-match.sw`.
- **Terms written in the branch, rewritten along the equation.** A term written in the branch isn't refined: a lemma `widthOf slot` still says `slot.field` where the branch's goal has `None`, and so does `h` itself where a refined lemma's premise wants `None = None`. Where a proof's type differs from what's expected only in having `e` where the other has the pattern, either way round, it is rewritten along `h`, as `rewrite h at t in t` would (SW-1538). The proof's type is searched for `e` as the goal is, as written first: a subterm with `e`'s head is an occurrence if it equals `e` up to computation, so a lemma stated with `xs.map (y => f a y)` fits a `match found: xs.map (f a)`, and the motive keeps the type's calls; that result is used only if it replaces every occurrence the search over the computed type would, else that search's is (`examples/accept/match-equation-as-written.sw`, [goal-as-written.md](proposals/goal-as-written.md) stage 3). So in a named `match`, the obvious helper lemma fits, and `h` and `rfl` both prove a refined premise `pattern = pattern`. This needs the name: without one there is no equation, and `E-TYPE-MISMATCH` says to name it, or to bind the lemma with `let` before the `match`, which refines it like a hypothesis. `rfl` still proves only what computes: a premise that mentions `e` (written in the branch, or brought in by a `rewrite`) needs `h`, and `E-REFL` says so. Proofs only; data isn't transported. Examples: `examples/accept/match-equation-transports-proofs.sw`, `examples/accept/match-refined-lemma.sw`, `examples/reject/match-lemma-unnamed-equation.sw`, `examples/reject/match-equation-not-rfl.sw`.
- **`auto` arguments.** A scrutinee that is an application with an `auto` argument is searched as elaborated: `match e: Ord.compare x y with` replaces `Ord.compare x y` in the goal and in `h: Ord.compare x y = Less` without `[ord := ord]` (SW-188; an application's dictionary is found as soon as its arguments fix its type, before the goal is searched).
- **Not found.** If the expression is in neither the goal nor a hypothesis as they compute, the `match` refines nothing; when an arm then fails, `W-MATCH-NOT-FOUND` says so and shows the goal. Write the expression as the goal shows it, `rewrite` first, or bind it with a `let`.

Nothing else changes. The definitions and lemmas you call keep their statements, so a lemma stated about the folded form (`accessible grid s r c`) fails with a type mismatch against a branch's goal that is a step further along. This was the main surprise in the day 4 proofs ([aoc-2025.md](aoc-2025.md), pain point 1), and it is predictable once known. To avoid it, give the lemma the matched value as an argument (`sweepRowCases` on the marks, `ifFloorRoll` on the condition), or state it about the computed form.

The same goes for an occurrence a lemma brings in. The `match` replaces the scrutinee everywhere in the goal it is given, inside lambdas too: with `step: ok x` the `True` branch of `anyR (ys => all2 ok (Cons x ys)) rest` is `anyR (ys => all2 ok ys) rest`, as `all2` computes to `ok x && …` and that to what follows. But a `rewrite` with a lemma inside the branch puts the lemma's statement into the goal, and an `ok x` in it is still there: neither `rfl` nor `cases` rewrites with `step`, so a goal that would hold with `True` in place of `ok x` fails. `rewrite step` replaces it, inside a lambda too, as `ok x` doesn't mention the lambda's parameter, so no congruence lemma is needed; `E-REFL` and `E-CASES` say so when such an occurrence is inside a function (SW-882, `examples/reject/match-scrutinee-from-lemma-under-lambda.sw`).

This is how a proof splits on an `if`: matching on the condition replaces it in the goal, and `h` is the evidence for the branch. No motive is written by hand (`Bool.inspect` asks for one).

```
theorem pickGe: (w: Nat) -> (xs: List Nat) -> (c: Nat) -> (after: List Nat) -> c <= Pair.fst (Bank.best.pick w xs c after)
  | Succ w, [x, ..more], c, after =>
    match e: Nat.leq (Succ c) x with
      | True  => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more)
      | False => pickGe w more c after
```

The condition may be written `a <= b` or `Nat.leq a b`: they are the same `Bool` (`match h: a <= b with` was `E-MATCH-MOTIVE` before SW-206, since a proposition is not a `Bool` to match on; it is now read as the `Bool` it decides). On any other type whose decision computes to `Bool.decTrue b`, `match h: c < x with` matches on `b`, the comparison an unfolded `if c < x` holds: on a `Fin`, ordered by `Ord.byKey Fin.toNat`, that is `Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x)`, so the branches see the `if` decided and `omega` reads `h` (D1073, `examples/accept/match-decided-by-key.sw`). Hypotheses whose types mention the condition (`h: Nat.leq a b = False -> …`) are generalised too, and a branch's goal has already computed one step further, so a branch may need less than the same proof under `Bool.inspect` did. Real proofs: `aoc/src/Aoc/Year2025/Day03/Proofs/Best.sw` (`pickGe`, `pickLen`, `pickSub`, `pickBestStep`) and `aoc/src/Aoc/Year2025/Day02/Proofs/Repeated.sw` (`window`).

A `match` on a *decision* (`match Nat.decLessEq 10 value with | { holds = True, sound = big, complete = _ } => … | { holds = False, … } => …`) replaces the decision, which computes to the record `{ holds = Nat.leq 10 value, … }`, wherever that occurs, and refines an `if` on it too: every `if` on a decided proposition holds its decision, whether its branches use the proof or not (a plain `if` and an `if h:` are the same term, docs/proposals/decidable-record.md §3.1). Use it for the evidence in its `sound` and `complete` fields; to split on the `if` alone, matching on the condition, `match h: 10 <= value with | True => … | False => …`, does the same with less to write (`examples/accept/match-decision-refines-if.sw`, 2021 day 18's `split`, SW-1719, SW-2751).

**Proving things about a definition with an inner `match`.** A `match` inside an arm that isn't the whole right-hand side (an operand of `||`, say) becomes a generated function whose name source can't write, so a lemma can't mention it. A proof doesn't need to:

- *Arms compute.* A call with constructors where the definition splits is already its right-hand side, so `reach (Cons line rest) c (Succ k) d` is an `if` on `charAt line c == '^'` without any lemma, and any equation of that kind is `rfl`.
- *Match on the condition.* `match e: cond with` refines a hypothesis about the call (a parameter, a lambda's variable or a `let`), because the condition is there once the call has unfolded.
- *Leave the inner `match`'s part as `_`.* Arguments you write out inside a branch (`reach (Cons line rest) c (Succ k) d`) are elaborated afresh and aren't refined, only the goal and the variables in scope are. A `_` is solved by unification from the hypothesis, so the generated function is filled in and never written. The type mismatch note for a written-out argument suggests this.
- *Split its scrutinee to make it compute.* The generated function unfolds once its own scrutinee is a constructor, so `match c with | Zero => … | Succ b => …` turns the hidden operand into `False` or `reach rest b k d`.
- *To state something about it, name it.* Writing the same `match` in a lemma makes a second generated function, which is a different definition. Two such functions are compared by their bodies (the same scrutinee, and the same result in every branch), but not when one calls the definition it's written in, as `reach`'s does, so a lemma about a recursive definition's inner `match` still needs it named (SW-386, D1091). Make the `match` a local `def` in the arm and refer to it from outside as `owner.name` ([Local definitions](#local-definitions)).

Example: `examples/accept/match-inner-match-proof.sw`; a real proof is `fallKeeps` in `aoc/src/Aoc/Year2025/Day07/Proofs/Part1.sw`. Design: [proposals/equation-lemmas.md](proposals/equation-lemmas.md).

A scrutinee that performs abilities runs once, in order from left to right, before any branch is chosen. Branches may perform abilities too, if the ability row of the definition allows them.

The first version has limits. Each one is `E-MATCH-MOTIVE`, and the message says how to get round it:

- the same variable is matched twice (`match n, n with …`);
- one scrutinee is part of another (`match n, Succ n with …`);
- the type of one expression scrutinee mentions another expression scrutinee;
- generalising a scrutinee makes the type of something else ill-formed.

The way round all of them is a top-level helper with a written signature.

JavaScript: a `match` that is part of the case tree, with a tail call to its own definition in a branch, becomes a loop like any self tail call. A generated definition doesn't: a `match` that is lifted, in tail position, whose branch calls the owner, is a pair of mutual tail calls, and those aren't loops yet. Deep recursion through it can hit the JS stack limit, which is reported as the boundary's out-of-resources error. A tail `match` on a parameter (the whole right-hand side) isn't affected. Examples: `examples/accept/match.sw`, `examples/extract/match.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 4.

#### Guards: `| p if c => e`

An arm may end its patterns with `if` and a condition: the arm applies only when the patterns match and the condition holds. When it doesn't, the arms below it are tried, as if the arm were not there:

```
def clamp (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

def firstBig (xs: List Nat): List Nat :=
  xs.filterMap (match some | x if x > 2 => x * 10)
```

A guard works in every kind of `match`: `match … with`, a definition's arms, and the clause lambdas `match |`, `match some |` and `matches |` (in `matches`, an arm with a guard and no `=>` is `True`). It covers the whole arm: with several patterns (`| a, b if a < b =>`) it comes once, after the last, and with an or-pattern (`| 'a' | 'e' if strict =>`) it is tested for whichever alternative matched. It stops at the `=>` outside brackets, so `| x if flag => e` is a guard and a result, not a lambda. `if h: P` names the fact in the arm, as in an `if` expression. An arm with `()` and no result can't have a guard (`E-PARSE`), nor can a handler clause, `match induct`, `match reify`, a pattern `let` or a lambda's pattern.

- **What the arm knows.** The arm is the `then` of an `if` on the condition and the arms below it are its `else`, so they know what an `if` would tell them. A decided proposition (`n != 0`, `x < y`) is an anonymous hypothesis in the arm, that `auto` finds (`| (i, xs) if i < xs.length => xs.getLt i` checks the `getLt`), and its negation is known below. A plain `Bool` condition (`here == wanted`) tells nothing. Proofs see an ordinary `if`: `match e: n <= limit with` splits `clamp limit n`.
- **Coverage.** An arm with a guard covers nothing: the checker doesn't reason about conditions, so `| n if n < 5 => … | n if n >= 5 => …` is `E-NONEXHAUSTIVE`, and the error points at the guarded arms and says to add an arm without `if`. A `match some` or `matches` is complete anyway, as its last hidden arm takes what no arm accepts, so `W-MATCH-TOTAL` doesn't fire when a guard makes it useful. `W-REDUNDANT` knows a guarded arm isn't a covering one: an unguarded arm after a guarded one that looks the same is reached.
- **Abilities.** A condition can't perform operations (`E-ABILITY`): it runs inside the case tree, where nothing can be sequenced. A pure call, even of a function whose abilities come from its callback (`xs.all (y => y > 2)`), is fine; for an operation, run it first with `let`.
- **Size.** A guard keeps the arms below it where a plain arm would end the search, so guarded arms that match different columns copy them: a `match` may make 4096 such copies (`E-MATCH-SIZE`): many guarded arms over many plain ones are fine, but each further guarded arm on another column doubles the count. Move some of the arms into a helper.
- **Order.** The splits that arms below a guarded arm need are made before the condition is tested, so a guard may wait for another column to be taken apart. Nothing observable changes, as conditions are pure.
- **Equations.** A guarded arm's generated equation takes its condition as its last hypothesis, `guard` (`h` for `if h: P`): `clamp.eq1: (limit n: Nat) → n ≤ limit → clamp limit n = n`. The condition is said as a proposition where it is a decided one, also when it is written as its `Bool` (`n != 3` gives `n ≠ 3`, `xs == []` gives `xs = []`), as `c = True` for a comparison (`(n <= limit) = True` reads `n ≤ limit`) and another `Bool`, and as `P ∧ Q` for a conjunction of two sides (`a ≠ 0 ∧ b ≠ 0`; a side that is a `Bool` is read as `c = True`). An arm below it takes `notArmJ`, that the condition failed, said in one form for each kind of condition whichever `if` the definition tests it by: `c = False` for a comparison or other `Bool` (`clamp.eq2: (limit n: Nat) → (n <= limit) = False → clamp limit n = limit`), `¬P` for a proposition and for a conjunction (`¬(a ≠ 0 ∧ b ≠ 0)`), except that `¬(n ≠ 3)` is said `n = 3`, or Lean's form with the condition as one more premise where the earlier arm's patterns take only some of its values. A guard adds no name: equations are numbered by arm as before. `f.induct` gives each case the same facts. An equation isn't generated (`E-NO-EQUATION`, with the reason) where the right side computes on a condition's proof that isn't known to be the only one (D2180; an arm that only passes the proof on where nothing computes on it gets its equation, SW-1429), or where the proof needs a split on an indexed family; prove such a case by hand with `f.unfold` or by matching on the condition (docs/proposals/pattern-guards.md §6, `examples/accept/pattern-guard-equations.sw`).

Examples: `examples/accept/pattern-guards.sw`, `pattern-guard-facts.sw`, `pattern-guard-proofs.sw`, `pattern-guard-effects.sw`, `pattern-guard-redundant.sw`; `examples/reject/pattern-guard-*.sw`. Design: [proposals/pattern-guards.md](proposals/pattern-guards.md).

#### Missing cases

When the alternatives of a `match`, or the arms of a definition, leave out some constructors, `E-NONEXHAUSTIVE` lists every case that is missing, as arms to paste, one per line, each ending in `?` so that it checks as an open goal (SW-1027):

```
[E-NONEXHAUSTIVE] Error: missing cases: no arm matches 2 patterns
| Square _ => ?
| Tri _ _ => ?
```

A missing case is the whole row of patterns, one for each scrutinee or argument, separated by commas, so a `match` on `(Option a, Bool)` with two arms can be told `| (None, False) => ?` and `| (Some _, True) => ?`. A field the arm doesn't need is `_`, and implicit fields aren't written. A list is `[]`, `[_, .._]` (`Cons _ _`) and so on, as a list pattern is written, and a pair `(a, b)`. On an indexed family a constructor that can't be there (`VCons` in a `Vec a 0`) isn't listed, as it isn't an error. At most 20 cases are listed, then `and N more`; add those and check again to see the rest. Where what's missing is numbers or characters (`Nat`, `Int`, `Char`, `Fin`), the message says which (`numbers other than 0 and 1`), and the fix is an arm with a variable or `_`. In `check --index`, the diagnostic has a `missing` member with the same cases (docs/proposals/code-navigation.md).

#### Impossible cases

A case can be left out when it can't happen: when, in that case, some variable in scope has a type with no values. That is an equation of two different constructors once the case is known and the types compute (`h: beats Rock theirs` is `False = True` when `theirs` is `Rock` or `Paper`), or a data type with no constructors (`Void`), including a type that computes to one (with `IsSome: Option Nat -> Prop` defined as `Void` at `None`, `h: IsSome o` once `o` is `None`), as well as the indexed families above. Under an arm with a condition, the case left when the condition fails is filled in the same way. The checker fills in the arm `()` would be, the same term, so

```
theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs with
    | Scissors => rfl
```

checks, and so does the same left out of arms (`| Scissors, _ => rfl` alone), in a theorem or a `def` alike (D3534). The variable needn't be a scrutinee: a hypothesis whose type mentions one is refined with it, and an indexed family's hypothesis is tried whatever it mentions (`i: Fin n` once a `Vec a n` is `VNil`, so `def first (v: Vec a n) (i: Fin n): a := match v with | VCons x _ => x` checks). An arm with a body for such a case warns, `W-UNREACHABLE` "this case can't happen" (D3535): `| Rock => Void.exfalso (Bool.falseNotTrue h)` above, with the label "here `h` is `False = True`, which can't hold" (or "is a `Void`, which has no values", or an indexed family's type, "which has no constructor that fits") and the note that the arm can be deleted. The editor shows the arm faded. It warns only when every case the arm covers is ruled out, not on a `()` arm, not on an arm with a condition, and not when the arm binds the impossible value itself (`| p => Void.exfalso (Bool.falseNotTrue p)` on a `p: False = True`, which is how a proof uses it), nor when a later arm would take the case once it's gone (`| Rock => … | _ => rfl`: without the `Rock` arm, `_` would cover `Rock`, where `rfl` fails) unless that arm warns too, nor on the last arm of a `match` whose arms are all ruled out (a `match` needs an arm; or write `()` there), nor on the cases `cases` makes, nor in a `match` refined as written (`W-MATCH-UNCONFIRMED`), where the proof the checker would fill in can be too large to check. On an alternative of an or-pattern (`| Paper | Scissors => …`, `Paper` ruled out), the note says that alternative can be deleted. The promise holds for all the warnings of a `match` at once: the checker compiles the `match` again as it would be without every arm and alternative it warns about, and warns only if each case they covered is then one it fills in (SW-3008). Of `| [], [] => …` and `| [], [y, ..ys] => …`, where either can go but not both (that leaves `[], _`, where a hypothesis matching on both lists doesn't compute), only the second warns, the arms chosen from the last up. A clause of a `match reify` never warns: each is required. An arm whose `match` is checked once for each case of an outer split (`| z, [x, ..rest] => match c: z with …` after a `match z, xs`) warns only if every check of it rules it out, so what is offered is never an arm another case needs. The arm is checked as ever and the term is the same (`examples/accept/unreachable-arm-hypothesis.sw`). A case that can happen is still `E-NONEXHAUSTIVE`, and the error lists only those (`examples/accept/impossible-cases-left-out.sw`, `examples/accept/impossible-case-indexed-hypothesis.sw`, `examples/reject/impossible-cases-one-possible.sw`). The same holds for the numbers a `match` on a `Nat` or a character has no arm for (`| 0 => … | 1 => …` with nothing for the rest): that case is left out as any other when a hypothesis rules it out, one that computes once `n` is known to be neither 0 nor 1 (`h: isSmall n = True` with `isSmall` defined by those numbers and `_ => False`, or `found: command key = Some n` on characters), and otherwise it is `E-NONEXHAUSTIVE`, "no arm matches numbers other than …" (SW-2990). A `match` on an `Int` or a `Fin` names its missing numbers as soon as it finds them, without looking for a hypothesis that rules them out (SW-3012). The checker doesn't search: the equation must be there, in the context, and compute to different constructors; a fact it would have to prove (`n < 0` with `n` unknown, or `h: n < 2` for the numbers other than 0 and 1) needs an arm. The filled-in proof of an equation of two `Bool`s or two `Ordering`s is the library's lemma (`Bool.falseNotTrue h`, `Ordering.lessNotEqual h`), the term the arm would be if written; for any other type it uses a function by cases on that type, a helper declaration of its own (`f.%match1`).

#### Clause lambdas: `match |`, `match some |` and `matches |`

A lambda whose body is a `match` on its parameters can be written as the alternatives alone, with no `match … with` and no parameter names. Three spellings; each is a lambda over an ordinary `match`, so the checker and proofs see nothing new (`docs/proposals/partial-lambdas.md`):

```
operators.any (match
  | Add => last <= target
  | Multiply => last * 2 <= target)          -- x => match x with | Add => … | Multiply => …

lines.filterMap (match some | Corrupted illegal => illegal)
                                             -- x => match x with | Corrupted illegal => Some illegal | _ => None

xs.filter (matches | [_, 'x', .._])          -- x => match x with | [_, 'x', .._] => True | _ => False
```

- **`match | p => e | …`** is total, and checked like any `match` (`E-NONEXHAUSTIVE` for a missing case). Several patterns in an alternative (`| acc, Do => …`) make a lambda of several parameters, and every alternative has as many patterns as the first (`E-PARSE` otherwise).
- **`match some | p => e | …`** keeps what matches. Each result is wrapped in `Some`, and a last alternative `_ => None` is added, so it is an `a → Option b`, for `List.filterMap` (Scala's `collect`), `List.findMap` (`collectFirst`), `Option.flatMap`, `Map.filterMap` and any function of your own. The word `some` is the mark that values can be dropped; a plain `match` never drops a case. Where the type expected is not an `Option`, the error says that `match some` makes one. An alternative whose result is already an `Option` makes an `Option (Option …)`: write a `match` there. If the alternatives you wrote match every value, the added one is never used, and `W-MATCH-TOTAL` says to write `match` (and `map`).
- **`matches | p => c | …`** gives a `Bool`: the result of the alternative that matches, and `False` for the values none matches. An alternative may leave out `=> c`, which then means `True`: `matches | 133 | 160 | 5760`. `W-MATCH-TOTAL` warns when the alternatives cover every value.

`some` is a keyword only between `match` and `|`, and `matches` only in front of a `|` that starts an alternative: `match some with …` still matches on a variable called `some`, and `matches + 1` uses a variable called `matches`. Because the form is an expression, a value can be fed to it with a pipe, `Key.next [27] |> matches | Incomplete` and `scan |> match some | Corrupted c => c`, and as an argument it needs brackets like any lambda.

As a definition's whole body the form is the written arms. `def f: A → Option B := match some | p => e` is `def f: A → Option B | p => Some e | _ => None`, with the same generated equations (`f.eq1`, …) and case tree; `:= matches | p` and `:= match | …` likewise, so a lookup table can drop its `Some`s and its last line:

```
def operationOf: Nat → Option Operation := match some
  | 0 => Sum
  | 1 => Product
  | 7 => EqualTo
```

The rules of `|` are those of `match … with`. On one line a `|` before `=>` continues an or-pattern (`matches | A | B` is true for both), and one after a result starts the next alternative, so alternatives with different results go on their own lines, lined up. An inner `match` on one line takes the alternatives after it: bracket it, or use lines (`examples/reject/clause-lambda-nested-one-line.sw`). Guards (`| p if c => e`) work here as in any `match` (see "Guards" above). Examples: `examples/accept/clause-lambda.sw`, `match-some.sw`, `matches.sw`, `match-some-covers-every-value.sw`; `examples/reject/match-some-not-option.sw`, `matches-not-bool.sw`, `clause-lambda-arity.sw`. The lemma for proofs about `filterMap` is `List.memFilterMap`.

### `calc`

`calc` writes a proof as a chain of steps, one per line. Each step is `_ R e`, where `R` is `=`, `<=`, `<`, `>=` or `>`, followed by `:= proof`:

```
theorem mixed (a: Nat) (b: Nat) (h1: a = b) (h2: b <= 3): a < 5 :=
  calc a
    _ = b := h1
    _ <= 3 := h2
    _ < 5
```

The steps line up, one column further right than the line `calc` is on, and each starts with `_` (so inside a `calc`, a line starting with `_` is the next step, not an argument of the line before). `calc` is a keyword; the relation always goes on a step line, so `calc a = b := p` is a syntax error. `calc` is an expression, usable wherever a proof is.

- **Steps.** `e0` is inferred, and each later expression is checked at its type. Step `i` is the proposition `e(i-1) R e(i)`, and its proof is checked against that. A proof that proves something else is `E-CALC-STEP`, pointing at the proof and saying what the line says.
- **A step with no proof** is closed by `rfl`, checked against the step's proposition: the step holds if that proposition computes to true. For `=` that means the two sides compute to the same value. For `<=` and `<` it is about the order proposition, not the ends: `_ <= n` after `0` needs no proof (`Nat.leq 0 n` computes to `True`), but `calc n` then `_ < n` is rejected even though both ends are `n`. Otherwise it is `E-CALC-STEP` ("this step has no proof, and `rfl` doesn't prove it").
- **Relations.** `=` works at any type. `<=` and `<` are on `Nat` only for now (`E-CALC-RELATION`), and `=`, `<=`, `<` can be mixed freely. `>=` and `>` chain the other way round: a chain whose steps are `=`, `>=` and `>` is read from its last expression back, so `calc a` / `_ > b := p` / `_ >= c := q` is `calc c` / `_ <= b := q` / `_ < a := p` and proves `c < a` (which is what `a > c` means); the proofs are those of the flipped steps (`p: b < a`), and an `=` step's proof is used flipped, with `Eq.sym`. `<`/`<=` and `>`/`>=` can't be mixed in one chain (`E-CALC-RELATION`). Other relations (`!=`, …) aren't chained; `!=` is a syntax error.
- **The conclusion.** The chain proves `e0 R e(n)`, where `R` comes from folding the steps' relations left to right: `=` with `R` is `R`, `<=` with `<=` is `<=`, and any `<` makes it `<`. The steps are joined with the proofs people write by hand: `Eq.trans`, `J` with `Eq.sym` for `=` next to an order, `Nat.leTrans` and `Nat.lessTrans`, and the kernel re-checks the result as usual.
- **With a goal.** Where the type is known, the chain is checked against it by computation: its first and last expressions only have to compute to the goal's sides, and its relation must be the goal's or compute to it — for example, a `<` chain ending at `Succ b` proves `a <= b`, since `a < Succ b` computes to `a <= b`; `<` is not otherwise weakened to `<=` (`Nat.lessLe` does that). Otherwise it is `E-CALC-GOAL`, naming the end that differs. With no goal (`let h := calc …`), the chain has the type `e0 R e(n)`.

| steps so far, next step | result | term |
|---|---|---|
| `=`, `=` | `=` | `Eq.trans p q` |
| `=`, `R` | `R` | `J (w _ => w R c) q (Eq.sym p)` |
| `R`, `=` | `R` | `J (w _ => a R w) p q` |
| `<=`, `<=` | `<=` | `Nat.leTrans a b c p q` |
| `<`, `<=` | `<` | `Nat.leTrans (Succ a) b c p q` |
| `<=`, `<` | `<` | `Nat.leTrans (Succ a) (Succ b) c p q` |
| `<`, `<` | `<` | `Nat.lessTrans a b c p q` |

(`p` proves `a R1 b` and `q` proves `b R2 c`.) Examples: `examples/accept/calc.sw`, `examples/reject/calc-*.sw`. Design: [calc-rewrite.md](proposals/calc-rewrite.md) section 5.

### `rewrite`

`rewrite p in t` proves the goal from `t` by replacing, in the goal, the left side of the equation `p: a = b` by its right side. It spares you the motive: where `Eq.cong (x => (x + n) / d) p` spells out the expression around the change, `rewrite p` looks for `a` in the goal and works the motive out itself.

```
theorem stepZero (highest: Nat) (n: Nat):
    Bool.toNat (0 == 0) + ((Succ highest - 0) % Succ highest + n) / Succ highest
      = ((Succ highest - 1) % Succ highest + Succ n) / Succ highest :=
  rewrite Nat.modSelf (Succ highest), Nat.modSmall highest (Succ highest) (Nat.leRefl highest)
    in Eq.sym (Nat.addDivSelf (Succ highest) n)
```

| form | meaning |
|---|---|
| `rewrite p in t` | `t` proves the goal with `a` replaced by `b` |
| `rewrite p` | the same as `rewrite p in rfl`, against the whole goal |
| `rewrite p, q in t` | `p`, then `q` on what is left, then `t`: `rewrite p in (rewrite q in t)` |
| `rewrite <- p in t` | right to left: `b` is replaced by `a` |
| `rewrite p at h in t` | in `t`, the hypothesis `h` has its type with `a` replaced by `b` |
| `rewrite p at h` | the rewritten `h` itself, as a term |
| `rewrite p, q at h` | `p`, then `q` on what is left, in `h`'s type |
| `rewrite p at f x y` | the term `f x y` with its type rewritten (no `in`: there is no name to rebind) |

`rewrite` and `in` are reserved words (`in` is also membership, `x in xs`). `at` is not: it is only special where a rule can end (outside brackets, inside a rule, and not as a field `r.at`). So a variable called `at` is an ordinary name, a rule may start with one (`rewrite at b h in t`, with `at` a lemma), and a rule that passes it as an argument puts it in parentheses, `rewrite f (at) at h`. The result is a `J` term, which the kernel re-checks; the kernel is unchanged.

- **The goal must be known**, without `at`. `rewrite` is checked against a goal: a definition's body, an argument whose type is fixed, a `calc` step, a `let` with a type. With none (`let h := rewrite p in t`), it is `E-REWRITE-NO-GOAL`; give the type with an ascription, `(rewrite p in t: a = b)`, or rewrite a fact's type instead with `at`. In a `calc` step, `rewrite p` is checked against the step's line, `e(i-1) R e(i)`, and may rewrite either side.
- **`at`: rewriting a hypothesis.** `rewrite p at h` searches the type of `h` instead of the goal, by the same rules (below), and is `h` carried along `p`: a fact about `b` where `h` was about `a`. It never needs a goal, so it works in an untyped `let`, under `Eq.sym`, or where the goal has computed past what you'd rewrite: in `d != 0` from `h: 1 <= d`, the goal after `e: d = 0` is `False = True`, with no `0` left in it, but `e => Bool.falseNotTrue (rewrite e at h)` rewrites `h` to `1 <= 0`, which computes to `False = True`. With `in t`, `h` is rebound for `t` (a `let`, so the old `h` is shadowed; a hypothesis whose type mentions the old `h` isn't changed). `in` needs a local name after `at` (`E-REWRITE-TARGET` otherwise); without `in`, any expression may follow `at`, such as a lemma applied to its arguments. To rewrite the goal too, nest: `rewrite p at h in rewrite p in t`. The errors are the goal's, about "the type of `h`". Examples: `examples/accept/rewrite-at.sw`, `examples/reject/rewrite-at-*.sw`; design: [rewrite-hypothesis.md](proposals/rewrite-hypothesis.md).
- **The rule** is any proof of an equation, with its implicit arguments left open if nothing fixes them (`[n: Nat] -> f n = g n` used as `rewrite h`). Explicit arguments left off its end are unknowns too, as if written `_`: `rewrite Nat.addComm` is `rewrite Nat.addComm _ _`. The equation's *left side* needs a function, constructor or variable at its head; an unknown function (`?g x`) is `E-REWRITE-RULE`, as is a proof that isn't an equation whatever its arguments.
- **Premises.** An argument of the rule that is a proof, left off or written `_` (`Nat.addSubCancel x n` needs `x <= n`), is found when the rule matches: by unification with the rest of the rule, else by a hypothesis in scope of exactly its type, else by `omega`. An `[auto]` argument waits until the match has fixed what it is about (`rewrite Nat.modSmall`). Nothing proves it: `E-REWRITE-PREMISE`, naming the premise and the facts there were; give the proof in that argument's place. Examples: `examples/accept/rewrite-premises.sw`, `examples/reject/rewrite-premise-unproved.sw`.
- **Finding occurrences.** `rewrite` looks in two places. First in the goal as it is printed, with calls such as `isSafe report` kept; if the rule has open arguments, they are solved from the call's arguments (`rewrite isSafeCorrect _` finds `isSafe { levels = xs.reverse }`). It uses that result only if it is the same rewrite it would have made in the second place: no further copy of the left side is left inside a call, the rule's open arguments get the same values, and the rewritten goal checks. The next goal then keeps its calls. Otherwise it looks in the goal as it computes, as it always did, so a rule can still rewrite inside a definition the goal shows as a call. If that finds nothing either, a result from the first place is used even though copies are left. If the second search can't run because it runs out (the goal is too large once its calls are computed, `settle x 1000` unfolding a thousand stuck `if`s, or the comparisons use up the budget, below), so that the `rewrite` would fail with `E-RESOURCE` or `E-REWRITE-BUDGET`, a result from the first place is used without the checks that ran out, and the warning `W-REWRITE-UNCONFIRMED` says so. A copy left inside a call, or an open argument solved differently, then shows as an error in a later step; the proof term is still checked in full, so nothing false is accepted (`examples/accept/as-written-unconfirmed.sw`, `examples/reject/as-written-unconfirmed-*.sw`; [goal-as-written.md](proposals/goal-as-written.md) stage 4). Each search goes in pre-order, outermost first, left to right, and the search never looks inside an occurrence it has chosen. A subterm is an occurrence if it has the same head and number of arguments as `a`, is the same term or has the same type and *computes* to it (in the second search, and the first without the hidden-copy case). Matching the rule's open arguments is one-way: only the rule's own can be solved, and a candidate that fails leaves nothing solved. Every occurrence is replaced, then `t` is checked against the result. If there are none, it is `E-REWRITE-NOTHING`; the message shows the goal (after the rules before this one), what the left side computes to when that differs from how it is written (`Succ n / 1` is looked for as `Succ (Nat.divFuel n n 1)`), and whether the goal already holds by computing, as it does when an earlier rule already replaced what this one would have. If the term after `in` already proves the goal, the message says the goal computed past the rule and suggests dropping the `rewrite`.
- **Inside a function argument.** An occurrence that uses the variable of a function passed as an argument (`x * 1` in `List.map xs (x => x * 1)`) can't be replaced by `J`, which would need function extensionality. Instead `rewrite` uses the **congruence lemma** of the call the function is passed to, the same lemmas a `decreasing` recursive call inside a function uses (below: `List.mapCong`, `List.sumByCong`, …, found by name beside the function): it rewrites the function's body with its variable as a local, and the lemma turns that equation, for every value of the variable, into one between the two calls. A lemma may also give **facts** about the variable, which are hypotheses while the body is rewritten (so they prove a rule's premises): `FCongRange` gives `low: from <= x` and `high: x < until` where the list is `List.range from until` (and `FCongRangeFrom` gives `low: s <= x` and `high: x < s + c` for `List.rangeFrom c s`, which is what a range with a numeral start such as `List.range 1 (n + 1)` evaluates to), `FCongMem` gives `m: List.Mem x xs`. `rewrite` tries `FCongRange`, `FCongRangeFrom`, then `FCongMem`, then `FCong`, using the first whose left side matches the call. Inside a function, a rule whose premise isn't proved there isn't used there; a later rule may do it, and if nothing is rewritten it is `E-REWRITE-PREMISE`. So `rewrite Nat.mulOne _` proves `List.map xs (x => x * 1) = List.map xs (x => x)` by `List.mapCong`. It works through several functions inside each other (`List.map xs (x => List.map ys (y => x + Succ y))`), with `in`, `<-` and `at`, and for a function given as a partial application (`List.sumBy xs (f k)`, with a rule about `f k _`). The result is still an ordinary checked proof term.
  - **`_` for the variable.** The rule is elaborated again for each function, with its unknowns (`_`, implicit arguments) solved there, once per function: write `_` for an argument that is the function's variable, `rewrite Nat.mulSucc k _`. A rule with no unknowns (`Nat.mulSucc k i`, with `i` not in scope) doesn't look inside functions.
  - **Order.** Occurrences inside functions are rewritten first, a step each (outermost call first, its inner functions before its own body), then those that use no such variable, in one step.
  - **No lemma.** If an occurrence is there only inside a function passed to `F` and `F` has no `FCong`, it is `E-REWRITE-CONG`, naming the lemma and showing its statement for `F` (`examples/reject/rewrite-inside-function-no-lemma.sw`). Functions the compiler made (an effect's handler) aren't named; nothing is found there.
  - **Limits.** A variable bound by the goal itself (`f y` in `(y: Nat) -> f y = g y`) still can't be rewritten: introduce it first (`y => rewrite …`). Facts come only from the congruence lemma: one about the variable that a different lemma would give (a `filter`'s condition, say) needs that lemma by hand. The search sees definitions unfolded, so a call such as `List.sumBy xs f` is reached as `List.foldLeft …` and goes through `List.foldLeftCong`. An `[auto]` argument of a lemma used as a rule may need saying, `List.sumByAdd [c := Nat] _ _ _`. Examples: `examples/accept/rewrite-inside-function.sw`; design: [proof-automation.md §6.1](proposals/proof-automation.md).
- **Cost.** All the comparisons of one `rewrite` share a budget of evaluation steps. Running out is `E-REWRITE-BUDGET`, never "no match": it says the comparison was too expensive, not that the occurrence is absent. The message shows the part of the goal and the left side in notes, shortened (`STITCHWORT_FULL_TERMS=1` shows them whole). A part that is the same term as the left side (binder names and source locations aside) matches without computing, so the budget goes on parts that differ. State the step with `calc`, or rewrite with a more specific equation. `STITCHWORT_REWRITE_METRICS=1` prints, per `rewrite`, how many subterms were looked at, how many had the right head, how many comparisons ran and the steps they took.
- **The motive.** After the occurrences are replaced by a variable, the goal must still be a valid proposition (`E-REWRITE-MOTIVE`: the usual cause is an `auto` proof, such as the `i < xs.length` of `xs.getLt i`, that is about the term being replaced; rewrite a larger term that contains it, or use `calc`), and putting the left side back must compute to the original goal. That second check fails only where comparison ignores something it shouldn't have, and is also `E-REWRITE-MOTIVE`.
- **What will surprise you.**
  - `rewrite p` in a `calc` step rewrites the whole step proposition, both sides, not just the expression on the line before. `<-` is therefore needed less often, but it is the only way to replace the right side by the left.
  - Every matching occurrence is replaced. There is no way to pick one; use `calc` to say exactly which form you want.
  - An occurrence can match without being there textually, because a term that computes to the left side matches. And the goal searched is the elaborated goal, which keeps definitions folded only until they can compute: a goal written `Succ m + n` is `Succ (m + n)` by then, and `x % d` has unfolded into `x - x / d * d` (so error messages may show `Nat.leq a b = True` for `a <= b`). A rule's left side is read the same way, so the two still agree.
  - The first match fixes the rule's open arguments. With `f n = g n` and a goal `f 1 + f 2`, only `f 1` is rewritten; `f 2` is a different instance. The search order is what picks the instance, and a chosen occurrence isn't searched inside: in `f (f 1)` with `n := f 1`, the inner `f 1` stays.
  - An occurrence found by being the same term can be of the wrong type: two copies of `x => x`, one for `Bool` and one for `Nat`, are the same term to the search, and a rule about the `Nat` one meets the `Bool` one first (`E-REWRITE-MOTIVE`: the goal with it replaced is ill typed).
  - `E-REWRITE-BUDGET` is about cost, not truth.
  - With proof irrelevance ([proof-irrelevance.md](proposals/proof-irrelevance.md), SW-93), a candidate that equals the left side only by ignoring a proof field can match and then fail the round trip, as `E-REWRITE-MOTIVE`.

Examples: `examples/accept/rewrite.sw`, `examples/reject/rewrite-*.sw`. Design: [calc-rewrite.md](proposals/calc-rewrite.md) section 6; as built, its "As built" note.

#### Patterns in `let` and lambdas

`let` and a lambda's parameters take patterns too:

```
let (q, r) := (n / 7, n % 7)
let MkPair a b := p                -- a constructor's arguments need no brackets
let MkSize { width, .. } := s      -- a constructor's fields by name
let { name, .. } := p
let (a, b): (Nat, Nat) := e       -- the right-hand side is checked against the type
let _ := e
(a, b) => a + b
acc (k, v) => acc + v
{ name, .. } => name
```

`let p := e` followed by the rest of the block means `match e with | p => rest`, and a lambda's pattern parameters are matched against its arguments in the same way. `let x := e` and `let (x) := e` are the ordinary `let`.

A pattern made only of tuples, records, variables and `_` is instead projections, outside a proof: `let (a, b) := e` is `let a := e.fst` and `let b := e.snd`, with `e` computed once (in a hidden `let`, unless it's a variable). So a function using one computes even when `e` is unknown: after `def sw (p: (A, B)): (B, A)` whose body is `let (a, b) := p` then `(b, a)` on the next line, `sw p` is `(p.snd, p.fst)` by `rfl`. Where the expected type is a proposition (a proof), it stays the `match`, which splits `e` into a pair and so refines the goal ([proposals/let.md](proposals/let.md) §7, §A.7).

A thunk `() => e` doesn't match at all: its parameter is a `()`, and the lambda is the plain `_ => e` (with the parameter's type `()`), so the same thunk written twice is the same term, and a law about `() => xs.map f` in a theorem's statement applies to `() => xs.map f` written in its proof (`examples/accept/reify-thunk-in-proof.sw`). Only where the type after it mentions the parameter (`(u: ()) -> P u`) is it matched, so that the goal becomes `P ()`.

The one-alternative `match` must cover every value of the type, or the `let` is `E-LET-REFUTABLE`: coverage is by the type, not the value, so `let Some x = Some 3` is rejected by design. Use `match` to say what happens otherwise. Elimination of proofs still applies (`E-PROP-ELIM`). In a block with abilities, the right-hand side runs once, in order, before the rest.

Limits:

- a record pattern in a lambda needs its type known where the lambda is checked, as `p.name` does;
- a pattern `let` that isn't the whole right-hand side is lifted like a `match`, so it isn't available in `partial` functions, data or ability declarations, or the REPL.

Examples: `examples/accept/let-patterns.sw`. Design: [syntax-conveniences.md](proposals/syntax-conveniences.md) section 5.

### `omega`

`omega` is a proof of a linear arithmetic fact about `Nat`s and `Int`s, found by the compiler from the facts in scope and checked by the kernel:

```
theorem stacked (id: Nat) (lastTo: Nat) (rFrom: Nat) (h1: id <= lastTo) (h2: lastTo + 1 <= rFrom): id < rFrom :=
  omega

theorem topGe: (z: Nat) -> (rs: List Range) -> z <= rs.foldLeft z (m r => Nat.max m r.to)
  | z, []        => Nat.leRefl z
  | z, [r, ..rs] => omega [Nat.leMaxLeft z r.to, topGe (Nat.max z r.to) rs]
```

| form | meaning |
|---|---|
| `omega` | proves the goal from every arithmetic fact in scope |
| `omega [e1, e2]` | the same, with the facts `e1` and `e2` (any proofs, such as a lemma applied to its arguments) added |

`omega` is a keyword and a term, like `rfl`: it can be a definition's body, a `calc` step's proof, an argument whose type is fixed, or `(omega: x * 3 = x + x + x)` given to `rewrite`. Where nothing says what it proves (`let p := omega`) it is `E-OMEGA`. The proof it writes is an application of `Std.Omega.prove` (or `Std.Omega.proveEq` for an equation, `Std.Omega.proveIntEq` on `Int`) to the facts and goal as syntax, a certificate saying how to combine them, `rfl` (the kernel running the library's checker) and the facts' proofs; nothing new is trusted. Design and as built: [omega.md](proposals/omega.md).

- **Goals.** `a <= b`, `a < b` and `a = b` between `Nat`s or between `Int`s, and `Void` (the facts contradict each other). Any other goal (a `Bool` equation, `xs = Nil`, a type of data) is proved when the facts contradict each other, so `Void.exfalso omega` is just `omega`. Around those: `Not p` (proved as `h => …` with `h: p` as a fact), `And p q`, `Nat.LexLess a1 a2 b1 b2` (a lexicographic `decreasing` obligation: `a1 < b1`, else `a1 = b1` and `a2 < b2`), `(p && q) = True`, `(p && q) = False` and `(p || q) = False` (by cases on `p` for the first), `not p = True`/`False`, `Nat.leq a b = False` (from `b < a`), `Int.leq a b = False` and `Int.less a b = False`, and a decided proposition `d.holds = True`/`False`, which is how `a <= b` inside `&&` and `a == b` come out. A disjunction, `Or p q` or `(p || q) = True`, is proved by cases (`Bool.inspect`) on the `Bool` that decides one side (`p = True` itself, or `Nat.equal a b` for `a = b`): where it's `True` that side holds, and where it's `False` the other side is proved with that as a fact; if neither side is decided that way, one side is proved alone, splitting the facts' disjunctions first if it must. A goal is read as it computes, so `x < 0` is `False = True` and `2 < 3` is `True = True`, both fine.
- **Arithmetic.** `+`, numbers, `Succ`, and multiplication by a number on either side: `x * 3` and `3 * x` (which computes to `x + (x + x)`; `k * x` is taken for `k` up to 1000, and a larger `k` is `E-OMEGA` with a note to write `x * k`). Truncated subtraction `a - b`, `Nat.max a b` and `Nat.min a b` (also after `max` and `min` have computed to their `if`) are atoms `omega` knows more about: what always holds (`a - b <= a` and `a <= (a - b) + b`; `a <= Nat.max a b`; `Nat.min a b <= a`, and the same for `b`) and, when it has to, the two cases (`b <= a` and `(a - b) + b = a`, or `a < b` and `a - b = 0`; `max` and `min` are one side or the other). A product of two unknowns `x * y` is an atom, the same atom as `y * x` (by `Nat.mulComm`), but `(x * y) * z` and `x * (y * z)` are different. Anything else of type `Nat` is an **atom**, an unknown `omega` knows only to be at least 0: `List.length xs`, `r.to`, a division by an unknown, a call. `x / k` for a positive number `k` is an atom with the facts `(x / k) * k <= x` and `x <= (x / k) * k + (k - 1)` (SW-997), and `x % k` computes to `x - (x / k) * k`, so `(x / 3) * 3 <= x` and `x % 3 < 3` are `omega`. `x / 0` is an atom with the fact `x / 0 = 0` (`Nat.divFuelZero`), so `x % 0 = x` is `omega` too (SW-1669). A call stuck on an unknown solved since is computed again first, so a field of a record that is written out, `{ row = 1, column = 0 }.row`, is `1` even when the record was only known after the goal was. Two atoms are the same if they're the same term or the compiler can quickly show they compute to the same value; otherwise they're different, which can lose a proof but never makes a wrong one. So `get xs i h1` and `get xs i h2` are different atoms unless they compute to the same thing.
- **Facts** are every hypothesis in scope (parameters, pattern variables, `match e:` and `if h:` equations, `let`s, local theorems) and the listed terms whose type, after computing, is `a <= b`, `a < b`, `a = b` on `Nat` or `Int`, `Int.leq a b = False`, `Int.less a b = False`, `Not (a <= b)`, `Not (a < b)`, `Not (a = b)` (also written `a != b`; `omega` splits it into `a < b` or `b < a` when it has to), `And p q`, `(p && q) = True`, `Nat.leq a b = False`, `Nat.equal a b = True`/`False`, `(p || q) = False`, `not p = True`/`False`, or `d.holds = True`/`False` of one of these (so `a == b` and `a != b` on `Nat` or `Int`; on `Nat`, `a == b` computes to `Nat.equal a b`). A disjunction, `Or p q`, `(p || q) = True` or `(p && q) = False`, is split, as Lean's `omega` does (`splitDisjunction`): if the facts without it don't give the goal, `omega` proves it in each case, with that case's side as a fact (`Or.elim`, `Bool.orElim`), splitting further disjunctions in each case as it needs, at most 8 splits in all (2 for `auto`). The others are ignored. A quantified fact (`(id: Nat) -> covered rs id = True -> id < b`) is used by applying it: `omega [b id h]`. The emitted proof mentions only the facts it uses.
- **`Int`.** As Lean's `omega` does, `Int` and `Nat` arithmetic meet in one problem: an `Int` atom may be negative, and `n.toInt` (which computes to `OfNat n`) is the `Nat` term `n` inside, so its atoms keep their `0 <= x`: `n.toInt - 1 < n.toInt` and, from `n.toInt <= 3`, `n <= 3`. On `Int`: `+`, `-` (`x - y` computes to `x + Int.neg y`), negation, numbers (negative ones too), multiplication by a number on either side (`3 * x`, `x * (-2)`), and `x / k` and `x % k` for a nonzero number `k`, which are atoms with `k * (x / k) + x % k = x`, `0 <= x % k` and `x % k < |k|` (`Int.divAddMod`, `Int.modNonneg`, `Int.modLtAbs`), so `(3 * k) / 3 = k` and `(3 * k) % 3 = 0`. `x / 0` and `x % 0` compute to `0` and `x`. `x * y` and `y * x` are one atom by `Int.mulComm`. `Int.natAbs t` is a `Nat` atom which, when the goal doesn't follow without it, is split on as the disjunction `Int.natAbsDichotomy t`, `(0 <= t ∧ (Int.natAbs t).toInt = t) ∨ (t < 0 ∧ (Int.natAbs t).toInt = 0 - t)`, like a disjunction among the facts (one split each, within the limit of 8), so `(x + y).natAbs <= x.natAbs + y.natAbs` and, from `x.natAbs <= 3`, `x <= 3` are `omega` (SW-1650); a goal with many sizes may need their lemmas listed instead (`omega [Int.natAbsAdd x y]`). `Int.toNat`, `Int.sign` and a division by an unknown are atoms with no facts. Example: `examples/accept/omega-int.sw`.
- **Whole numbers.** `omega` knows the unknowns are whole: from `2 * x <= 3` it gets `x <= 1`, `2 * x = 1` is a contradiction, and when the facts only have fractional solutions it tries a few levels of case splits (`x <= v` or `x >= v + 1`).
- **When it fails** it is `E-OMEGA`, listing the facts and atoms it used and saying which of these it found. None of them is a counterexample to the goal; each says why the search stopped:
  - *an integer model of the arithmetic abstraction*: whole values for the atoms that satisfy every fact and the goal's negation (with atoms like `x * y` or `List.length xs` treated as unknowns, so it may not be a real counterexample);
  - *a rational model of the relaxation*: only fractional values were found, and the case splits didn't rule them out;
  - *unsupported structure*: the goal isn't in the fragment above and the facts don't contradict each other, or (as a note) an atom such as `x * y` is outside it;
  - *budget exhausted*: the search made its limit of rows; nothing is claimed.
- **Not yet**: `if`, and `Int.toNat` or `max`/`min` on `Int` as more than atoms. A goal that is a `Bool` equation between comparisons (`(a <= b) == (c <= d)`) is stage 3.

Examples: `examples/accept/omega-basics.sw`, `examples/accept/omega-stage2.sw`, `examples/accept/omega-int.sw`, `examples/accept/omega-nat-abs.sw`, `examples/accept/omega-division.sw`, `examples/accept/omega-day05.sw`, `examples/reject/omega-*.sw`.

### `ring`

`ring` is a proof of an equation between `Nat`s or `Int`s whose two sides are equal as polynomials: equal once products are multiplied out and like terms collected. The compiler writes the proof and the kernel checks it:

```
theorem square (x: Nat): (x + 1) * (x + 1) = x * x + 2 * x + 1 := ring

theorem pairsStep (n: Nat) (p: Nat) (h: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n := ring [h]

theorem writeTimesMul (k: Nat) (b: Nat): (n: Nat) -> writeTimes k b n = b * multiplier k n
  | Zero   => ring
  | Succ n => rewrite writeTimesMul k b n, multiplierSucc k n in ring
```

| form | meaning |
|---|---|
| `ring` | proves the goal `a = b` |
| `ring [h1, h2]` | the same, using the equations `h1: l1 = r1`, `h2: l2 = r2` (any proofs): it proves `a + r1 + r2 = b + l1 + l2`, or the same with some `l`s and `r`s swapped, and cancels |
| `ring [4 * h1, -h2, c * h3]` | with coefficients: `a - b` must be `4 * (l1 - r1) - (l2 - r2) + c * (l3 - r3)` as polynomials |
| `(ring: a = b)` | states what it proves, for `rewrite` or anywhere the expected type isn't known |

`ring` is a keyword and a term, like `omega`: a definition's body, a `calc` step's proof, an argument whose type is fixed (`Nat.leCongRight x y z ring h`), or `rewrite (ring: i + (p + q) = i + p + q)`. Where nothing says what it proves (`let p := ring`) it is `E-RING`. The proof it writes is `Std.Ring.proveNat env a b rfl` (or `proveInt`, or `proveNatWith`/`proveIntWith` with the hypotheses), where `a` and `b` are the sides as syntax over numbered atoms; `rfl` is the kernel computing both normal forms and finding them the same. `Std.Ring`'s soundness theorems are proved, with no axioms, so nothing new is trusted. Design and as built: [proof-automation.md](proposals/proof-automation.md) §6.2.

- **Arithmetic.** `+`, `*`, numbers and `Succ`; at `Int` also `-`, negation, `x.toInt` (so `(x + y).toInt` is `x.toInt + y.toInt`) and literals like `-3`. `Nat.pow e n` with a number `n` is multiplied out; with an unknown exponent it is an atom, but a call that computes to arithmetic is read as what it computes to, so `Nat.pow 10 (Succ k)` is `Nat.pow 10 k * 10`.
- **Atoms.** Anything else is an unknown: `List.length xs`, `f x`, `multiplier k n`, `x / 2`, `x % 10`, and `a - b` between `Nat`s (truncated subtraction isn't a ring operation; `omega` knows about it). Two atoms are the same if they're the same term or the compiler can quickly show they compute to the same value, as for `omega`.
- **Hypotheses** must be equations of the goal's type. Each entry is a hypothesis with an optional coefficient in front, any `Nat` or `Int` expression of the goal's type (`4 * h`, `x * h`, `(a - b) * h`), and an optional `-` (`-h`, `-4 * h`), which uses it turned round; an entry may also be a sum or difference of these (`3 * h1 - h2`). Coefficients multiply (`2 * (x * h)` is `2 * x` times `h`). With `ring [c * h]`, `h: l = r` is used as `c * l = c * r` (`Std.Ring.scaleNat`, `scaleInt`), so the check is that `a - b` is the combination `Σ cᵢ (lᵢ - rᵢ)`, as in Mathlib's `linear_combination`. An entry with no `-` written is tried both ways round, with up to six such entries; with more, only as written. An entry with a `-` is used as written.
- **When it fails** it is `E-RING`, with both sides' normal forms (highest degree first, in the program's own names) and what the left side has more or less of; with hypotheses, the sides are the ones with the hypotheses added, and a last note shows what is left over: the goal's left minus its right, minus the combination, which has to be 0. A note names each atom that looks like it should have been arithmetic (`a - b`, `x / 2`, a power with an unknown exponent), and when the statement is false for small values the counterexample note shows them.

Examples: `examples/accept/ring-basics.sw`, `examples/accept/ring-coefficients.sw`, `examples/reject/ring-*.sw`.

### `cases`

`cases` is a proof by cases on whatever the goal is stuck on. The compiler finds the value a definition in the goal is waiting for (`a` in `a ∨ b`, `Float.isNaN x` inside `Float.ieeeLe x y`, `s` in `{ s | id = t }.ref`), splits on it as a `match` would, and goes on in each case until every case is closed:

```
theorem orComm (a: Bool) (b: Bool): (a ∨ b) = (b ∨ a) := cases

theorem andLeft (a: Bool) (b: Bool) (h: (a ∧ b) = True): a = True := cases

theorem ieeeLtLe (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True := cases

theorem parseSmallSome (s: Text) (t: Text) (v: Nat) (h: parseSmallOption s t = Some v): v <= 10 := cases
```

| form | meaning |
|---|---|
| `cases` | splits until each case is closed by computation, a contradiction, a hypothesis, `omega`, or deciding it |
| `cases in t` | the same, trying the proof `t` in each case first (before splitting it further) |

`cases` and `cases in t` are a keyword and a term, like `omega`: a definition's body, a `calc` step's proof, or an argument whose type is fixed (`f x cases`; as an argument, `cases in t` is written in brackets, `f x (cases in t)`, since its body runs to the end of the expression). Where nothing says what it proves (`let p := cases`) it is `E-CASES`. `cases` is a reserved word (the word `cases` stays free for `Text.split`). The proof it writes is the `match` you would have written, a case tree of `case` and `J`, and the kernel re-checks it; nothing new is trusted. Design and as built: [simp.md](proposals/simp.md) (stage 1).

- **What it splits on.** The goal is computed as far as it goes, and `cases` looks for what it is stuck on: a variable or call of a type with two or more constructors (`Bool`, `Option`, `Ordering`, a variant type), taking the innermost one, so that `Float.isNaN x` is split rather than the `Nat.equal` it calls. A record is taken apart into its fields only when nothing else is left. It doesn't take apart recursive types (`List`, `Nat`: that's induction, written as recursion), except once where several stuck calls wait for the same value (below), nor propositions or indexed families, nor what `Int`'s own arithmetic (`-`, `+`, `*`, `/`, `%`, `<=`, `<`) is stuck on: `x + y` isn't split into `x`'s `OfNat`/`NegSucc` cases, which is `omega`'s and `ring`'s work (an `Int` variable may still be split as a fallback, below). A hypothesis that says a stuck value is a constructor (`h: f x = True`, `h: parseSmallOption s t = Some v`) is split on too, after the goal; other hypotheses aren't looked at. When two or more stuck calls that `cases` would split (an `Option`, a `Bool`, or such a value they wait for) wait in turn for the same value of a recursive type other than `Nat` (`List.get t 0 = List.head t`, both stuck on `t`), that value is split first, so they compute together: splitting `List.get t 0` and `List.head t` one after the other would make cases that can't happen (one `None`, the other `Some`). This is done once: a value that is itself a field of such a split (`xs` after `t = Cons x xs`) isn't split again, so `cases` never does induction by itself (`examples/accept/cases-shared-list.sw`).
- **Each case** gets the equation of its split, named `%case1`, `%case2`, … in messages, and the goal and every hypothesis that mentions the value are rewritten with the constructor, as a `match h: e with` does. Old copies of the rewritten hypotheses are hidden. A hypothesis `Some a = Some v` is turned into `a = v`, and `True = False` closes the case.
- **Closing a case**, in this order: both sides compute to the same value (`rfl`); a hypothesis equates two different constructors, or two say `e = True` and `e = False` for the same Bool `e` (either way round, with `e` stuck or not; `auto` closes a goal from such a context too); a hypothesis has the goal's type; `t`, for `cases in t`; and, when there is nothing left to split, `omega`. A goal that is itself a comparison (`Nat.leq a b = True`) is given to `omega` before it is split into `True = True` and `False = True`.
- **Implications whose premise holds.** Before looking for something to split, a hypothesis `h: P → Q` whose premise `P` is an equation that holds in the case (its sides compute to the same value, as `b = True → fact` does once `b` is split and the hypothesis rewritten to `True = True → fact`; or a hypothesis says exactly `P`) adds `Q` as a hypothesis (`h rfl`, or `h e`), and the case starts again with it, so `omega` and the closers above see `fact` (SW-948). Only an explicit `P` that `Q` doesn't depend on; nothing is added that is a hypothesis already. So `theorem t (b: Bool) (hb: b = True → n ≤ 3): (b && 4 <= n) = False := cases` needs no `match` on `b` (`examples/accept/cases-guarded-hypotheses.sw`).
- **Deciding it**, after `omega`: a case still open whose goal has a decision procedure, found as for an `[auto h: P]` argument (DESIGN.md §6), has it run; if its test is `True`, the case is closed with the proof `auto` writes, `d.sound rfl`, which the kernel runs again, so nothing new is trusted. This closes `Digit3 = key ∨ …` once `key` is `Digit3`. `False` doesn't fail the case (its hypotheses may still contradict each other); if the case ends open, a note says "the goal's decision procedure says it is false".
- **A goal that is a function type** (`(x: Bool) → P x`, `b = True → Q`) has its leading binders introduced when nothing above proves it whole, so a statement's variables may be bound after the colon as well as before it: `theorem t: (x: Bool) → (y: Bool) → P x y := cases` is the proof `x y => cases`. Every leading binder is introduced, explicit, implicit and `auto`, whatever its type (a function `costs: Costs` is introduced and never split), under its written name; an unnamed one (`A → B`) is shown as `hypothesis 1 (unnamed)`. A `Π` goal a hypothesis, `omega` or `t` proves as it stands keeps that proof. This happens in any case, so a goal that becomes a function type after a split is introduced too.
- **The fallback.** When the goal isn't stuck on anything `cases` splits and nothing closes it (`key ∈ keys` computes to a disjunction of equations, which no definition waits on `key` for), `cases` splits a variable the goal mentions anyway: of those of a type it splits, not yet split in this case, the one whose split makes the fewest cases (a record 1, `Bool` 2, an enumeration its number of constructors), the latest bound on a tie. So `theorem everyKey: (key: NumericKey) → key ∈ numericKeys := cases` splits `key` and decides each case. Fallback splits are marked in the messages: the case's path (`a = True, b = False (fallback)`), a note naming the variables split as a fallback, and in `E-CASES-BUDGET` the values split on (`` `flag` (fallback) ``) and, when a fallback split is what crossed it, "`cases` tried splitting `month : Month` as a fallback; this would exceed the 64-case budget".
- **Budget.** At most 64 cases. Past that it's `E-CASES-BUDGET`, naming the values it split on and the first case still open; prove a fact that decides several cases at once and give it as `cases in t`, or split by hand with `match`. When every value it split is a variable of a finite type, a note points to `Finite.check` ([below](#finite-and-finitecheck)), which checks every value by computing, past any number of cases a truth table could reach. A case whose goal and hypotheses, written out in full, have more than a million parts is too large to split, and gives `E-CASES-BUDGET` at once: a value can share its parts and stay small while its written-out form doubles with each step (`examples/reject/cases-split-too-large.sw`).
- **When it fails** it is `E-CASES` for the first case nothing closed: the case is named by its splits (`a = True, Nat.leq n 2 = False`), the notes show that case's hypotheses and goal, and what the goal was stuck on when it stopped (`xs`, a `List`). With `cases in t`, it's `t`'s own error, with a note naming the case. Further notes count the other cases that failed and the ones that were closed, and how.

`cases` is the truth-table method: its cost is the number of cases, exponential in the number of variables split. Design of the decision closer, binder introduction and the fallback: [decide.md](proposals/decide.md) §6.1. The three ways to prove a statement by computing name what they do: `byDecision` proves a closed decidable proposition by running its decision procedure ([below](#bydecision)); `cases` does finite case analysis, closing each case by computation, a hypothesis, `omega` or deciding it; `omega` is the arithmetic procedure. When a case is left open, the last note of `E-CASES` lists what was tried, deciding it as `byDecision` does among them.

#### `byDecision`

`byDecision` (`import Std (byDecision)`) proves a closed proposition with a decision procedure, by running it: `def byDecision [p: Prop] [auto h: p]: p := h`, so it is an `[auto h: P]` argument under a name, and its proof is the one `auto` writes, `d.sound rfl`, which the kernel runs again (nothing new is trusted). It is Lean's `by decide`:

```
theorem enterIn: Enter ∈ keys := byDecision
theorem small: 2 + 2 < 5 := byDecision
```

A false one is `E-AUTO-FALSE` (`` `Digit0 = Enter ∨ Digit1 = Enter ∨ Void` is false ``); one whose procedure is stuck on a variable is `E-AUTO-STUCK`: split the variable with `cases`, which decides each case the same way, or check every value with `Finite.check` (`examples/accept/by-decision.sw`).

#### `Finite` and `Finite.check`

`Finite a` is an interface ([Interfaces](#interfaces)) with two fields, `all: List a`, every value, and `complete: (x: a) → x ∈ all`, the proof that none is missing; the list may repeat a value. The library has instances for `Bool`, `Ordering`, `Option a` and pairs (of finite types) and `Fin n`. A data type or record declared in a program gets one derived when it is declared, if it isn't recursive and every field's type has one (with `[auto fin: Finite a]` for each type parameter its fields use): enumerations, constructors with finite fields (`Arrow (direction: Direction)`), records of them. `Finite.all` lists the constructors in the order they're declared, each with every value of its fields, the first field varying slowest, which is the order the derived `<` puts them in:

```
type DirectionKey =
  | Arrow (direction: Direction)
  | Activate

theorem keys: Finite.all = [Arrow Up, Arrow Down, Arrow Left, Arrow Right, Activate] := rfl
theorem everyKey (key: DirectionKey): key ∈ (Finite.all: List DirectionKey) := Finite.complete key
```

A recursive type, a type with a field of a type without an instance (`Nat`, a function, a type), a proof field, or a field whose type depends on an earlier one gets none, and the `E-INSTANCE-NONE` where one is wanted says why (`` it's recursive (the field `left` of `Node` holds a `Tree`) ``, `` the field `n` of `Count` has type `Nat`, which has no `Finite` instance ``). A module's own `instance T.instFinite: Finite T` replaces the derived one. Deriving one costs about 0.5 ms for a four-constructor enumeration and 2 ms for eleven (decide.md, "As built (SW-807)").

`Finite.check` (`import Std (Finite)`) checks a `Bool` statement for every value by computing it: `Finite.check (p: a → Bool) (checked: List.all Finite.all p = True) (x: a): p x = True`, where `checked` is usually `rfl`. For several variables, make them one value, a record or a pair of finite types:

```
type Ten = { b0: Bool, b1: Bool, …, b9: Bool }
theorem tenBothWays (t: Ten): sameBothWays t.bits = True := Finite.check (u => sameBothWays u.bits) rfl t
```

It is the way past `cases`' 64 cases: the proof stays one term however many values there are, and the kernel computes `p` for each. 2^10 values take about 0.1 s, 2^16 about 12 s (`examples/accept/finite-check.sw`, `examples/accept/finite-derive.sw`).

Examples: `examples/accept/cases-bool.sw`, `examples/accept/cases-data.sw`, `examples/accept/cases-binders.sw`, `examples/accept/cases-decision.sw`, `examples/accept/cases-fallback.sw`, `examples/reject/cases-*.sw`.

### Numbers

A non-negative numeric literal is a `Nat` or an `Int`, depending on what's expected (`Nat` if nothing says; a `Fin n` too, where one is expected, [below](#fin-literals), and a `SafeNat` or `SafeInt`, checked to be within 2^53 - 1, [Numbers in an `export`](#numbers-in-an-export)); a negative literal such as `-5` is always an `Int`, and `-0` is `0`. A `-` glued to a numeral is part of it, so a method call applies to the negative number: `-5.natAbs` is `(-5).natAbs` ([Expressions](#expressions)). An arithmetic expression or comparison has one number type for all its operands, chosen by the first of these that applies: the expected type; a decimal or exponent literal (`Float`, below); an operand with no literal in it (when there's a prefix minus, only an `Int` or a `Float` one); a prefix minus (which makes it `Int`); any other operand; else `Nat` (D732). So `3 - 5 = -2` is on `Int`, and `x + 1` follows `x`. A literal whose type nothing says yet waits for the rest of the declaration, and is a `Nat` only if nothing says otherwise by its end (D2013, D2084; docs/proposals/postponement.md, stage 4): `let m := 3 - 5` followed by `m + i` with `i: Int` makes `m` an `Int` (`-2`), as in Lean and Haskell (`examples/accept/int-binding-nat.sw`).

There is no implicit conversion between `Nat` and `Int`: use `n.toInt`, `Int.toNat` (negatives become 0) or `Int.toNatChecked`.

`+`, `*`, `<` and `<=` work on any type with the instance they need ([Interfaces](#interfaces); docs/proposals/interfaces.md §5.13): `x + y` is `Add.add x y`, `x * y` is `Mul.mul x y`, and `x < y` and `x <= y` are `Ord`'s `lessThan` and `lessEq`, with the dictionary found as for any `auto` argument, so a dictionary in scope is used (`[auto ord: Ord Nat]` makes `<` on `Nat` its order). On `Nat` and `Int` with no other dictionary in scope that's the library's instances, whose fields are the built-in operations, and the term is the operation itself (`Nat.add x y`), as it always was. `if x < y` decides with the decider in the same dictionary (`Ord.decLessThan`), also through a definition that unfolds to it. The operand type is chosen as above; an expression with `-`, `/`, `%` or a prefix minus is still on `Nat`, `Int` or `Float` only, and so are literals: generic code writes `Add.zero` and `Mul.one` (`E-TYPE-MISMATCH` otherwise, with a note). Missing an instance is `E-INSTANCE-NONE` (`+` on `Bool`, `<` on functions).

A literal argument of a generic function takes its type from the expected result when that is known: with `i: Int`, `chooseFirst 5 i` checked against `Int` works, because the result type is used before the arguments are checked ([syntax-conveniences.md](proposals/syntax-conveniences.md) section 7). The same holds for a constructor of a generic type whose arguments have number literals (`Point 1 "p" 10` of `Mark i n`): the expected type, through an alias too, gives the constructor's parameters before its arguments are checked. Where nothing is expected but a sibling operand has the type (`[Point 1 "p" 10, m]`, `pair (Point 1 "p" 10) m`, `if b then Point 1 "p" 10 else m`, `Point 1 "p" 10 == m`, with `m: Mark Int Nat`), such a constructor is checked after the others, so its literals aren't defaulted to `Nat` first; the terms and the order things run in don't change (`examples/accept/generic-constructor-literals.sw`). Where nothing says what the result is, such as `let v := chooseFirst 5 i`, the `5` waits, and `i` makes it an `Int`. Design: [integers.md](proposals/integers.md); examples: `examples/accept/int-literals.sw`, `examples/accept/int-choose-first.sw`, `examples/accept/expected-types.sw`.

#### `Fin` literals

A numeral checked against `Fin n` (`import Std (Fin)`), where n computes to a number, is the position it names, with its bound checked by computing `k < n` (D1073, [fin-literals.md](proposals/fin-literals.md); `examples/accept/fin-literals.sw`):

```
import Std (Fin, List)

def digits: List (Fin 10) := [2, 7, 5, 7, 3]
def last: Fin (2 * 5) := 9                     -- n need only compute to a number
theorem two: (2: Fin 5) = FSucc (FSucc FZero) := rfl
test "beside a Fin" := digits.all (d => d < 9)
```

The term is `Fin.ofNatLt n k rfl`, which reduces to `FSucc`s around `FZero`. A numeral at or above n (`def x: Fin 5 := 7`: "7 isn't below 5, so it can't be a `Fin 5`") or a negative one is `E-FIN-LITERAL`, and so is one whose n isn't a known number (`Fin n` for a variable n: build it with `Fin.ofNatLt`, giving the proof; `Fin.toNat 3`, where nothing says what n is: annotate, `(3: Fin 10)`). Only an expected `Fin` makes a numeral one: a literal with nothing expected is still a `Nat`, and arithmetic is never on `Fin` (it has no `Add`; use [`Mod n`](#interfaces) for numbers that wrap). In a comparison or `==` beside a `Fin`, the numeral takes that type, as any operand does. Number patterns on a `Fin` are under [Declarations](#declarations).

#### `Float`

`Float` (`import Std (Float)`, `std/Float/Float.sw`) is a 64-bit IEEE 754 double, the JS `number`: a Rust `f64` and a JS `number` at run time, and in the logic the record of its 64 bits, `{ bits: Nat, valid: Float.isValid bits = True }`, with one NaN. Design: [float.md](proposals/float.md) (stages 1a and 1b are built; `sqrt`, `min`/`max` and `Float.ofText` are later).

```
import Std (Float)

def shift (t: Float) (by: Float): Float := t + by    -- IEEE addition, rounded
theorem tenths: 0.1 + 0.2 = 0.30000000000000004 := rfl
test "zeros" := (0.0 == -0.0) = False                  -- `==` is the same double
test "ieee" := Float.ieeeEq 0.0 (-0.0) = True           -- JS's `===`
test "order" := -0.0 < 0.0                             -- `<` is the total order
test "js <" := Float.ieeeLt (-0.0) 0.0 = False          -- JS's `<`
test "round" := Float.round (-2.5) = -2.0               -- JS's `Math.round`
```

- **Literals.** `1.5`, `80281.87`, `1e3`, `1.5e-7`, `2.0E21`: a digit on both sides of `.`, an exponent `e`/`E` with an optional sign. The value is the decimal correctly rounded to the nearest double; `0.10`, `0.1` and `1e-1` are the same double. A literal that would be an infinity (`1e400`) or isn't zero but rounds to zero (`1e-400`) is `E-FLOAT-LITERAL`. A whole literal at `Float` is exact or refused: `9007199254740993` isn't a double (`E-FLOAT-LITERAL`, naming the two nearest), so write one of those or `9007199254740993.0`. A number right after a `.` is never a decimal literal, so `xs.0.1` is `xs` `.` `0` `.` `1` (and an error: there are no numeric projections).
- **The operand type.** A decimal literal makes the expression a `Float`, before a prefix minus would make it an `Int`: `-1 + 0.5` is `-0.5`. A `Float` operand does too: with `t: Float`, `t + -1` and `-t` are `Float`s. A whole literal in a `Float` expression is a `Float`, and `-k` is `Float.neg k`, so `-0` at `Float` is `-0.0`. `Float` doesn't mix with `Nat` or `Int` (`E-TYPE-MISMATCH`).
- **Arithmetic.** `+ - * / %` are the IEEE operations in the order written, so `(a + b) + c` and `a + (b + c)` can differ; they aren't `Add`'s and `Mul`'s (doubles break their laws). `/` and `%` need no proof that the divisor isn't zero: `1.0 / 0.0` is `Float.infinity`, `0.0 / 0.0` is `Float.nan`, and `%` is JS's (the remainder of truncating division, with the dividend's sign: `-5.5 % 2.0` is `-1.5`). The checker computes them on known doubles, so `rfl` proves `0.1 + 0.2 = 0.30000000000000004`, and a goal shows a double as its literal. Goals and messages print `Float.add x y` as `x + y` (and `-`, `*`, `/` likewise); a sum of unknown doubles stays a call, never `Float.Model` bit arithmetic (SW-1763).
- **Rounding.** `Float.floor`, `Float.ceil`, `Float.trunc` and `Float.round` are JS's `Math.*`. `round` is `Math.round` exactly: a half goes towards +infinity (`round (-2.5)` is `-2.0`, `round 2.5` is `3.0`), a zero result keeps the sign (`round (-0.4)` is `-0.0`), and `round 0.49999999999999994` is `0.0`. `Float.abs`, `Float.isNaN` and `Float.isFinite` (neither infinite nor the NaN) are as JS's.
- **Conversions.** `Float.ofInt i` and `Float.ofNat n` are the nearest double, ties to even, or an infinity beyond the largest (JS's `Number(n)` of a `bigint`). `Float.toInt x` is an `Option Int`: `Some` of the integer the double is when it's whole, of any size (`Float.toInt 1e100` is the integer 1e100's bits stand for, not 10^100), else `None` (a fraction, the infinities, the NaN); both zeros are `Some 0`. `Float.toSafeInt` and `Float.toSafeNat` check the safe range too; `SafeInt.toFloat` and `SafeNat.toFloat` are exact. There's no implicit conversion: `t + i` with `i: Int` is `E-TYPE-MISMATCH`, with a note naming `Float.ofInt`.
- **Equality.** `==` and `=` are "the same double", JS's `Object.is`: `0.0` and `-0.0` differ, and `Float.nan == Float.nan`. JS's `===` is `Float.ieeeEq`, where the NaN isn't equal to itself and `0.0` equals `-0.0`; port `a === b` as `Float.ieeeEq a b`.
- **Order.** `<`, `<=`, `List.sort`, `Map Float`, `Set Float` and derived orders use `Ord Float`, IEEE 754's total order: `-infinity < … < -0.0 < 0.0 < … < infinity < Float.nan`, with all of `Ord`'s laws (`Float.compare` is its comparison). JS's `<` and `<=` are `Float.ieeeLt` and `Float.ieeeLe` (`Bool`s, false with a NaN, the zeros equal). Port `a < b` as `Float.ieeeLt a b`, `a > b` as `Float.ieeeLt b a`, `a >= b` as `Float.ieeeLe b a` (not `!(Float.ieeeLt a b)`, which differs on a NaN); when `a` and `b` are calls rather than values, bind them in order first (`let l := left()`, `let r := right()`, then `Float.ieeeLt r l`), as JS evaluates the left operand first. A sort by the total order can put equal JS keys in another order (`-0` before `0`); a port keeps the original comparator with `List.sortBy`, which is stable.
- **Printing.** `${t}` and `Float.toText` are JS's `String(t)`: `0.30000000000000004`, `1e+21`, `1e-7`, `NaN`, `-Infinity`, and `0` for both zeros. Only the runtimes compute it (Node's `String`, and the same digits in the Rust runtime): the checker doesn't, so a `test` that inspects the text of a double, or anything computed from it, doesn't reduce; test printing with `stitchwort run`. `Show Float`'s `toSource` (what lists and records print their elements with) reads back as the same double: `1.5`, `3.0`, `-0.0`, `Float.nan`, `Float.infinity`, `-Float.infinity` (the last four computed by the checker too).

Examples: `examples/accept/float-literals.sw`, `examples/accept/float-operations.sw`, `examples/reject/float-*.sw`, `examples/extract/floats.sw`, `examples/extract/float-times.sw`.
