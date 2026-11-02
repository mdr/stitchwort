# Documentation system research for Stitchwort

Research date: 1 November 2026. Scope: associated documentation for definitions, command-line and editor consumers, checked examples, and a generated API site. Research and design only.

## Recommendation

Give Stitchwort compiler-owned documentation attached to source declarations, authored in Markdown with a small set of semantic extensions. Share the resulting documentation model between search, the LSP, the playground, and a static site generator. Include checked examples in the first useful release.

The strongest combination is conventional comments for authoring, Unison's integration of documentation with code, Lean's semantic references and checked material, and rustdoc's practical treatment of examples and public API presentation. A general-purpose language of executable documentation values would add substantial machinery before Stitchwort needs it.

The important early decisions are attachment, reference resolution, example context, and identity. The choice of comment marker is comparatively easy to change.

## Evidence and method

The comparison uses official language manuals and maintainers' repositories. Searches covered documentation syntax, examples, cross-references, generated documentation, and tooling for Unison, Lean, Idris 2, Agda, Haskell, and Rust. Relevant manual sections and selected implementation paths were inspected; no foreign toolchains were installed or exercised. Behavior described as implemented is supported by manuals or inspected source, rather than a fresh execution test. Sources on `latest`, `main`, and `master` describe the material retrieved on the research date, not a promise about every released version.

Stitchwort findings below were checked in this checkout. Recommendations are design judgments. In particular, the Idris 2 manual and renderer differ in a way that matters to this comparison.

## Comparison

| System | Authoring and association | Examples and semantic content | Most useful lesson |
|---|---|---|---|
| Unison | Documentation expressions of type `Doc`; preceding blocks create a conventional `.doc` definition | Checked inline code, evaluated blocks, definition links, signature/source inclusion, document composition | Documentation can use the compiler's understanding of code |
| Lean | Declaration docstrings; ordinary Markdown or Verso according to configuration | Verso supports elaborated content; separate tools generate API references and larger documents | Preserve semantic structure beyond a string |
| Idris 2 | Preceding `|||` documentation; manual describes named parameter annotations | REPL/editor access and package HTML; current renderer is more limited than the manual suggests | Short summaries and parameter docs suit dependent APIs |
| Agda | Literate source mixed with prose; highlighted source HTML | Selected code blocks participate in checking as source | Checked narrative and source browsing complement an API reference |
| Haskell | Haddock comments on declarations and their parts | Linked identifiers, REPL example markup; separate `doctest` executes examples | Organize around the API readers use, including re-exports |
| Rust | Item and module doc comments rendered as Markdown | Integrated doctests, checked links, explicit example modes | A relatively conventional system can provide strong practical guarantees |

### Unison

Unison's `{{ ... }}` is an expression producing `Doc`, rather than discarded commentary. A block preceding a definition creates its `.doc` companion; UCM's `docs` command follows that convention. Double-backtick snippets are typechecked, triple-backtick code blocks can display evaluated results, and directives embed signatures or source. Documents can include other documents. Definition links identify terms or types, and checked snippets can reflect renaming. These features are described in the [official documentation guide](https://www.unison-lang.org/docs/usage-topics/documentation/).

**Fit for Stitchwort:** adopt checked references, examples, and generated signatures. Those benefits do not require making documentation ordinary runtime values. Unison's representation fits its codebase model; Stitchwort uses text files and already has a compiler/tooling pipeline. Also distinguish a displayed computed result from an assertion about an expected result: both are useful, but only the latter detects an unintended behavior change without review.

### Lean

Lean's `/-- ... -/` docstring is parsed declaration syntax, not whitespace. Misplaced documentation is an error. The `doc.verso` option determines whether its contents are parsed as Verso markup or treated as plain text/Markdown. Nested declaration modifiers cover positions such as constructors and structure projections. This is current documented behavior, rather than a proposal to add structured docstrings. See the [Lean reference on modifiers](https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/).

Two related tools serve different purposes. [`doc-gen4`](https://github.com/leanprover/doc-gen4) generates library API documentation through a Lake build target and supports source links and lookup by declaration name. [Verso](https://verso.lean-lang.org/doc/latest/) is a framework for manuals, tutorials, websites, and other document genres, with extensible markup, cross-reference infrastructure, and elaborated Lean code rendered with hovers, hyperlinks, and proof states. These are complementary concerns, not one interchangeable documentation command.

Lean's [documentation style guide](https://github.com/leanprover/lean4/blob/master/doc/style.md) explicitly distinguishes quick reference in editor hovers from reading in a browser and prioritizes readers learning the language.

**Fit for Stitchwort:** recognize documentation during parsing, retain semantic references, and generate consumer-specific views. Leave proof-state widgets and author-defined markup extensions for later. Stitchwort's existing guide and an API site should share references and example machinery while keeping their different reading structures.

### Idris 2

The [Idris 2 documentation manual](https://idris2.readthedocs.io/en/latest/reference/documenting.html) describes preceding `|||` lines, a first-paragraph overview, `:doc`, module and constructor documentation, and named parameter annotations such as `@ n`. It describes Markdown and shows an `idris example` fence. Named parameters include implicit parameters, which is especially relevant to dependent APIs.

There is an important implementation qualification. In the inspected [`Idris.Doc.String`](https://github.com/idris-lang/Idris2/blob/main/src/Idris/Doc/String.idr), docstrings are stored by name and user text is split into lines for display. In [`Idris.Doc.HTML`](https://github.com/idris-lang/Idris2/blob/main/src/Idris/Doc/HTML.idr), `UserDocString` becomes a `<pre>` block and text is escaped. [`Idris.Package`](https://github.com/idris-lang/Idris2/blob/main/src/Idris/Package.idr) contains the package documentation path. Thus package HTML exists, but this inspected rendering path does not establish the manual's richer Markdown presentation or checked examples. Do not count its example fence as evidence of doctest execution.

**Fit for Stitchwort:** take the compact summary and binder-associated documentation ideas. Specify and test what each renderer and example mode actually guarantees. A plausible-looking code fence should not imply checking that never occurred.

### Agda

Agda's [literate programming support](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) checks code interspersed with prose. Markdown code blocks normally form parts of one source file; an option restricts checking to explicitly tagged Agda blocks. The manual also distinguishes hidden checked code from visible material excluded from checking. These are source-checking rules, not output assertions.

The [HTML backend](https://agda.readthedocs.io/en/latest/tools/generating-html.html) produces highlighted, hyperlinked source and can hand the prose part of literate documents to another renderer. This provides a useful source browser, but it is a different presentation model from a curated page for each API family.

**Fit for Stitchwort:** retain the ability to write checked explanations and navigate to source. Do not equate an HTML rendering of a large library source file with a good API reference. Stitchwort's existing guide already supplies much of the narrative use case; a new literate source format is unnecessary for the initial documentation feature.

### Haskell

[Haddock](https://haskell-haddock.readthedocs.io/latest/markup.html) supports comments before (`-- |`) or after (`-- ^`) declarations, plus documentation for methods, constructors, fields, and function arguments. Identifier markup produces links. Module export lists can control documentation order and grouping, and re-exported entities appear in the public interface. Its `>>>` example markup describes REPL interactions; that rendering is separate from execution.

The maintainer's [`doctest`](https://github.com/sol/doctest) tool checks examples and properties in Haddock comments and supplies example groups and setup mechanisms.

**Fit for Stitchwort:** distinguish where a definition is implemented from where readers discover it. Group APIs by task and show useful names rather than reproducing the implementation file layout. Keep example execution integrated with Stitchwort's own test semantics, so authors do not need to coordinate an unrelated test tool. Prefer one direction of comment attachment initially; Haddock's many placement options introduce avoidable ambiguity.

### Rust

Rust uses `///` for item documentation and `//!` for enclosing module/crate documentation. Its [authoring guide](https://doc.rust-lang.org/rustdoc/how-to-write-documentation.html) recommends a brief explanation followed by detail and a usable example. [Coverage and hiding controls](https://doc.rust-lang.org/rustdoc/write-documentation/what-to-include.html) support progressive documentation of the public surface.

[Rustdoc tests](https://doc.rust-lang.org/rustdoc/write-documentation/documentation-tests.html) execute code blocks; assertions check results. They support hidden setup, compile-only `no_run`, expected compilation failure, and explicit ignored examples. Code that merely runs successfully has a weaker guarantee than an asserted result. Hidden setup improves readability but can obscure what a reader must copy.

[Intra-documentation links](https://doc.rust-lang.org/rustdoc/write-documentation/linking-to-items-by-name.html) resolve names in the definition's scope, support disambiguation, and account for re-exports and added documentation.

**Fit for Stitchwort:** this is the strongest practical starting point. Adapt its conventions to abilities, dependent preconditions, and proofs. Make example modes explicit, keep skipped examples visible to coverage tooling, and ensure links retain their meaning when documentation is displayed from a different namespace.

## Stitchwort foundations

The following are **checked in this checkout**, rather than inferred from the older design document.

| Existing component | Finding | Consequence |
|---|---|---|
| [Lexer](../../crates/syntax/src/lexer.rs) | Ordinary `lex` discards comments; `lex_with_trivia` retains text, spans, and positioning for formatting | Docs need deliberate preservation in the checking pipeline |
| [Declaration AST](../../crates/syntax/src/ast.rs) | Declarations include attributes and spans; a `def` lowers to signature/equation forms | Attach once to the source declaration, before lowering |
| [Navigation symbols](../../crates/elab/src/nav.rs) and [driver index](../../crates/driver/src/nav.rs) | Names, kinds, containers, source ranges, types, and parameter-bearing signatures are represented; no doc field is present | Extend shared metadata rather than extracting comments separately in every consumer |
| [LSP](../../crates/cli/src/lsp.rs) and [live references](../../crates/driver/src/live.rs) | Hover emits a type, kind/name, and omitted defaults; completion support exists | Add docs without discarding useful specialized type/default information |
| [Search](../../crates/driver/src/search.rs) | Results carry names, types, source locations, imports, and matching information; no docs | Supply concise summaries and full lookup, preserving structural search semantics |
| [Guide test harness](../../crates/cli/tests/guide.rs) | Checks example files, quoted snippets, and command output; update mode regenerates quoted material | Reuse the established expectation that documentation code is maintained by checks |
| [Testing guide](../guide/09-testing.md) | `test` conditions are checked and run separately; handlers can make effects testable; test results are content-cached | Reuse this separation and test semantics for documentation examples |
| [Core hashing](../../crates/core/src/hash.rs) and [project caching](../../crates/driver/src/project.rs) | Core identity omits definition names and locations; namespace check-cache inputs include source text and file names | Documentation identity and invalidation need their own treatment |
| [Project namespaces](../projects.md) | Several files can contribute to one namespace; logical names are independent of paths | Namespace documentation must define aggregation and conflict rules |

The standard library already contains useful material to promote selectively. [List.Toolkit](../../crates/elab/src/std/List/Toolkit.sw) describes effect order, short-circuiting, and why some helpers exist. [Text.Text](../../crates/elab/src/std/Text/Text.sw) places concrete padding theorems beside the functions. User-facing explanations belong in API docs; implementation commentary can remain ordinary comments. Do not automatically promote every adjacent comment.

## Proposed authoring model

### Documentation attachment

Use a distinctive preceding comment form, provisionally `--|`, repeated on every documentation line. This fits the existing `--` lexical convention while making continuation and ordinary comments distinguishable. Idris-style `|||` is a credible alternative; a new block-comment syntax is less useful unless wanted independently.

Recognize docs in declaration syntax and preserve their spans. Keep Markdown parsing and semantic enrichment outside the trusted kernel. Prefer these rules:

- A contiguous documentation block attaches to the next declaration or documented member at that syntactic level. A blank separator ends the block's attachment opportunity; a dangling block produces a documentation diagnostic.
- Documentation precedes the declaration's attributes and remains associated across those attributes. Diagnose a second competing block rather than silently selecting one.
- Support definitions, theorems, types and synonyms, constructors, record fields, interfaces and methods, instances, abilities and operations. Nested members attach inside their parent syntax.
- A function's equation arms do not each acquire independent primary docs. A generated projection inherits its source field's documentation; internal generated helpers have no separate public entry.
- Treat namespace overviews explicitly. Permit one primary overview per logical namespace initially; diagnose duplicate primary overviews from different files. Ordinary file comments remain file comments. File-level fragment composition can come later.

Use Markdown paragraphs, lists, headings, emphasis, inline code, and fences. Start with a first-paragraph summary plus optional conventional sections such as Examples, Edge cases, Abilities, Complexity, and Related definitions. These headings organize prose; they do not all need dedicated tags.

Add structured parameter documentation only where it conveys something useful, provisionally `@param name`. Validate names against source binders, including written implicit and `auto` parameters. Do not require boilerplate for every type parameter. Generated binder names should not become an author-facing documentation requirement.

### Semantic references

Provide explicit symbol links, provisionally ``[`List.filterMap`]``. Keep plain backticks as ordinary code formatting. Resolve explicit links after the namespace's declarations are known, using the documentation's original imports and declaration context. This supports references to the documented function itself and to later declarations without making prose order constrain code order.

Persist the resolved target and its original spelling. Render it as an HTML anchor, an editor-compatible link, or a terminal name. Link destinations should describe package/version, logical name, and member kind as needed. Do not manufacture URLs during parsing.

Also support a reference to an existing declaration as an example or theorem to display. This would let `Text.padRight` show its existing example theorems without copying their statements. Displaying a theorem and running an example are distinct actions; the UI should preserve that distinction.

An explicit broken or ambiguous symbol link should be reported at its source span. Plain prose identifiers should not create warnings. Strict documentation builds can make these diagnostics fatal while an editor with incomplete source continues to show the recoverable text.

### Illustrative authoring example

The following is **proposed documentation syntax**, not an implemented feature. The function header and ordinary test expressions follow existing library conventions; the code is not an executed prototype.

````stitchwort
--| Keeps the results for which `f` returns `Some`, preserving input order.
--|
--| Results of `None` are omitted. An empty input produces an empty list.
--| `f` may perform abilities; calls occur in input order, once per element
--| reached. An aborting ability can stop traversal before later elements.
--|
--| ## Examples
--|
--| ```stitchwort test
--| test "keeps successful parses" :=
--|   List.filterMap ["12", "bad", "7"] Text.toNat == [12, 7]
--| test "empty input" :=
--|   List.filterMap ([] : List Text) Text.toNat == ([] : List Nat)
--| ```
--|
--| See [`List.map`] when every element produces a result.
--| @param f Computes an optional result for each element reached.
def List.filterMap: List a → (f: a → {e} Option b) → {e} List b
  ...
````

The example illustrates the desired contract: behavior, omitted results, empty input, ordering, effects, ordinary use, and a related operation. It does not need a mandatory parameter table or a restatement of the type signature. Exact markers and fence grammar should be settled in a later design proposal.

## Checked examples

Make the checking guarantee visible and predictable. The modes below are proposed; their names are illustrative.

| Mode | Guarantee | Appropriate use |
|---|---|---|
| `stitchwort` | Parses and typechecks declarations in the block | Definitions and proof examples |
| `stitchwort test` | Checks the block and runs its `test` declarations successfully | Utility behavior and edge cases |
| `stitchwort eval` | Checks a closed expression and records its evaluated display | Showing a value without hand-maintained output; later extension |
| `stitchwort reject CODE` | Fails with the specified diagnostic code | Invalid uses and unsatisfied preconditions; later extension |
| `text` or another language | Display only | Pseudocode, output, foreign-language examples |

Prefer ordinary test expressions initially. They require less new language than inventing an example assertion notation, exercise existing failure diagnostics, and distinguish a promised result from a newly generated display. A bare evaluation example may update to a changed result without detecting a regression; an assertion does not.

Each block should have isolated names and an explicit context: the documented namespace and that file's imports, with owner binders available for reference checking where appropriate. Runnable tests must still be closed computations. Do not silently invent values for generic parameters or preconditions. Examples attached to a private implementation scope may need explicit public imports for reader-facing validation; the stdlib should favor examples that users can reproduce.

Blocks should not share implicit setup with preceding blocks. Add named, visible setup or references to checked example declarations if needed later. Always map errors back to the original comment, not a synthetic file with confusing line numbers.

Follow Stitchwort's existing distinction between checking and running. The editor, search, and hover must never execute examples. Check example syntax and types during an explicit documentation check initially; ordinary source editing can add incremental diagnostics later. Run assertions through the test path or a dedicated docs-test command included in CI. A site build should consume successful checked results or explicitly invoke that check, rather than silently publish failures.

Abilities make controlled examples practical: use `Fail.toResult`, `IO.simulate`, or a custom handler to obtain a pure result to assert. Do not grant ambient IO to examples. `Partial` and very expensive total computations require execution budgets; totality guarantees termination, not an acceptable time or memory bound. A compile-only example may define an effectful function without running it.

Check examples after their owning namespace is elaborated, in a separate environment that cannot add definitions or instances to ordinary program elaboration. This prevents a documentation example from changing program behavior or creating an elaboration dependency cycle through its owner. Existing theorem references can be displayed directly without re-proving them in a synthetic block.

## Representation and consumers

### Shared documentation data

Use a versioned compiler/tooling model with the owner, source span and original text, summary, structured Markdown, parameter entries, resolved references, and example records. Example records need source, mode, dependencies, and checking status. Status must distinguish unchecked, typechecked, passed, failed, and deliberately skipped; absence of a test run must not look like success.

Store documentation separately from core declarations and runtime data. Associate it with a source/API symbol identity, not solely a core content hash. Stitchwort can give two differently named definitions the same semantic hash; their intended explanations may differ. Conversely, a useful public documentation URL should survive an implementation change.

Separate three dependencies: program semantics, documentation content, and example checking. A prose edit should refresh docs without altering core identity or invalidating unrelated test results. An example's code or semantic dependency change must invalidate its result. A name/import change can invalidate a documentation reference even if semantic hashes stay equal.

This is a desired boundary, not a claim that all existing caches already support it. The current source-text check-cache key means a prose edit can still cause re-elaboration. It is reasonable to retain that conservative behavior initially, provided doc metadata is replayed on cache hits and never becomes stale. Optimizing that key is a separate task.

Keep document references out of the program's semantic dependency graph: a “see also” cycle must not create a recursive program group. Namespace docs and imported dependency docs must remain available even when a consumer has not requested a full source-navigation index.

### Command line and search

Show a summary beside a search result; provide full documentation lookup, provisionally `stitchwort doc NAME`. Expose summary, a documentation target, and optional complete docs through a versioned JSON contract. Distinguish undocumented definitions from a failed lookup.

Initially preserve current name/type/theorem matching and ordering. Documentation text offers an additional useful query channel, but silently mixing prose matches into proof search would change its meaning. Add explicit prose search later, with separate ranking and a clear combination rule. Aliases should lead to the definition's canonical docs while displaying the name the user searched.

### LSP and playground

Hover should show the specialized type already computed at the use site, the documentation summary and relevant detail, and a route to the full reference. Preserve the existing default-argument information. Longer examples and full theorem lists belong behind the full-doc link.

Completion entries can use the same summary and resolve full docs on demand. Parameter docs can later feed signature help, including implicit arguments when relevant. Use the same metadata for the browser playground. Markdown-to-plain-text fallback should retain code and definition names when a client does not support rich formatting.

The live editor needs recoverable documentation even while a declaration or namespace is broken. A previously checked doc may be useful, but the server must track its source revision and avoid presenting a cached successful example result as current after an edit.

### Browsable site

Generate a static reference from checked symbols and docs. Start with namespace pages containing an overview, groups of related definitions, linked signatures, summaries, full entries, examples, and source links. Add an alphabetical index and client-side name/prose search. Namespace pages with stable symbol anchors avoid generating thousands of tiny theorem pages immediately.

Define the intended API surface explicitly. Do not assume Stitchwort's JavaScript `export` marker is a general documentation visibility policy. Use namespace inclusion rules or an API manifest initially, with a way to include less prominent declarations in search and source browsing while hiding generated helpers from the default overview.

Separate ordinary functions, constructors/fields, abilities, interfaces/instances, and theorems in navigation. Readers should be able to find an operation without scrolling through every lemma. Link selected laws from a function's documentation; do not infer that every theorem mentioning a function belongs in its primary entry.

Use logical names for anchors, with escaping and member disambiguation. Version the site and generate a manifest mapping symbol identities to URLs, so links can work across guides, API docs, and dependencies. A source refactor should not change the public URL; a public rename may require a redirect. Escape prose/code and constrain raw HTML and URL schemes in rendering.

Share example/reference processing with the existing guide where useful. Replacing the guide's authoring system is unnecessary for generating a good API reference.

## Standard library documentation policy

Require useful explanations for the intended public surface, with these expectations scaled to the definition:

| Definition family | Information readers need |
|---|---|
| Collections | Order preservation, empty input, duplicates, bounds and truncation, callback order, short-circuit behavior |
| Text | Character/index unit, empty text and separators, trailing separators, whitespace and normalization behavior where relevant |
| Numbers | Rounding and division conventions, zero handling, natural-number subtraction, conversions and loss of information |
| Parsers and conversions | Accepted grammar, whole-input versus prefix consumption, whitespace/sign behavior, failure representation |
| Ability operations | What is performed, when it is performed, handler expectations, abort/resumption behavior |
| Interfaces and instances | Laws expected of instances, defaults, evidence supplied by `auto`, meaningful instance-specific behavior |
| Dependent functions | What indices and evidence mean, which conditions are checked automatically, a concrete valid call |
| Theorems | Informal meaning, hypotheses, orientation/use in rewriting, relation to the corresponding operation |

Do not fill every entry with irrelevant headings. A constructor may need one sentence; a parser deserves several examples. A theorem should explain its use or meaning rather than paraphrase every binder mechanically. Write complexity claims only where they are intended and supported, and qualify backend-dependent behavior.

For utility functions, aim for one ordinary example and an example of the most surprising edge case. For `filterMap`, successful/failed parses are more informative than arithmetic wrapped in `Some`; for a splitter, consecutive and trailing separators often matter more than a second ordinary input. Describe laws and link proofs when available, while distinguishing illustrative tests from universally quantified theorems.

Measure coverage against the chosen API surface. Start with a report and then enforce coverage on selected stdlib namespaces as they are documented. An empty comment or repeated signature should not count as a substantive quality success. Automated checks can enforce presence, valid links, binder names, and example results; editorial review still determines whether behavior and edge cases are explained well.

## Delivery priorities and decisions

| Priority | Scope | Reason |
|---|---|---|
| First useful release | Declaration/member docs, namespace overview, Markdown, summary, explicit symbol links, ordinary checked test examples, shared metadata, CLI lookup/search summaries, hover, a simple static site | Covers authoring and all requested consumers without building a second language |
| Follow-up | Named example/theorem inclusion, evaluation displays, expected-error examples, parameter signature help, coverage enforcement, cross-version/dependency link manifests | Reduces duplication and strengthens navigation and maintenance |
| Defer | User-defined document computation, extensible markup macros, interactive proof-state widgets, a new literate file format, prose embeddings and semantic search | Valuable in some ecosystems, but independent of basic API documentation |

The initial release can be delivered in stages: metadata and terminal/editor views, checked examples, then site rendering and a small set of thoroughly documented stdlib namespaces. All three belong to the target feature; “comments visible on hover” alone would leave the requested system incomplete.

The next design proposal should settle five choices:

1. **Comment and link syntax.** Prefer `--|` and explicit Markdown-style code links; compare with `|||` using real library examples.
2. **Example checking workflow.** Prefer explicit docs checking plus assertions using existing `test` semantics, with no editor execution.
3. **Documentation ownership.** Prefer source/API symbol identity separate from semantic hashes, with one primary namespace overview.
4. **Initial API surface.** Choose which stdlib namespaces and declarations are primary reference material, including treatment of helper definitions and lemmas.
5. **Strictness.** Prefer strict CI for the documented stdlib subset and recoverable diagnostics during editing; add broad missing-doc enforcement progressively.

Before implementation, validate the author experience on a small paper design covering `List.filterMap`, `List.foldRight`, `Text.padRight`, a numeric operation with evidence, a record field, an ability operation, an interface method, and a theorem. These exercise ordering, effects, existing proof examples, dependent arguments, member attachment, and different documentation lengths without requiring a compiler prototype.
