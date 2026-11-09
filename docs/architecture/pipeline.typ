// One-page A4 cheat sheet: how a Stitchwort program goes from source to a
// running artifact. Compile with:
//   nix shell nixpkgs#typst -c typst compile docs/architecture/pipeline.typ
#let commit = sys.inputs.at("commit", default: "")
#let day = sys.inputs.at("date", default: "")

#set page(paper: "a4", margin: (x: 11mm, y: 10mm))
#set text(size: 9pt, font: ("Helvetica", "Arial"))
#set par(leading: 0.4em, spacing: 0.5em)
#show raw: set text(size: 8.2pt, font: ("Menlo", "Courier New"))

#let blue = rgb("#1a5fb4")
#let red = rgb("#b00020")
#let green = rgb("#2a7f3f")
#let orange = rgb("#c05800")
#let purple = rgb("#6b3fa0")
#let grey = luma(110)

#let stage(num, title, crate, colour, body) = block(
  width: 100%, inset: (x: 2.4mm, y: 2mm), radius: 1.5mm,
  stroke: 0.7pt + colour, fill: colour.lighten(92%), breakable: false,
  [
    #grid(columns: (1fr, auto), align: (left, right),
      text(weight: "bold", size: 10.2pt, fill: colour)[#num #title],
      text(size: 7.6pt, fill: grey, raw(crate)))
    #v(-0.6mm)
    #body
  ],
)
#let arrow(label: none) = align(center, block(above: 0.7mm, below: 0.7mm,
  text(size: 8pt, fill: grey)[↓ #if label != none { text(size: 7pt, label) }]))
#let ul(..items) = list(marker: [•], tight: true, spacing: 0.34em, indent: 0mm, body-indent: 1.2mm, ..items)

#grid(columns: (1fr, auto), align: (left + bottom, right + bottom),
  text(size: 18pt, weight: "bold")[Stitchwort: from source to a running program],
  text(size: 6.8pt, fill: grey)[#if commit != "" [commit #commit · ] #day],
)
#v(-1mm)
#line(length: 100%, stroke: 0.5pt + luma(160))
#v(0.5mm)

#grid(columns: (1.05fr, 1fr), column-gutter: 5mm,
[
  // ---------------- Front end and kernel ----------------
  #stage("1", "Source", "*.sw · stitchwort.toml", grey)[
    A file or a project (namespaces, imports). The standard library is `.sw` too, shipped inside `elab` (`src/std/`).
  ]
  #arrow()
  #stage("2", "Parse", "crates/syntax", blue)[
    #ul(
      [Lex and parse into the *surface AST*, with source spans.],
      [Syntax errors and their notes come from here; `stitchwort fmt` works on this tree.],
    )
  ]
  #arrow(label: [surface AST])
  #stage("3", "Elaborate", "crates/elab", blue)[
    Turns what you wrote into fully explicit *core terms*:
    #ul(
      [names and imports resolved; dot calls, operators, sugar expanded;],
      [types inferred and checked; implicit arguments solved by unification (metavariables);],
      [`match` compiled to eliminators; records, ranges, clause lambdas desugared;],
      [abilities: `handle … with` becomes `handlePlus (A.%elim clauses) forward`;],
      [proofs: tactics (`rewrite`, `cases`, `omega`, …), function equations, termination measures.],
    )
    Most error messages and goal printing live here.
  ]
  #arrow(label: [core terms])
  #stage("4", "Kernel check", "crates/core", red)[
    The small *trusted* checker re-checks every definition and data group: types, termination (size-change graphs), positivity, universes. Accepted definitions get a *content hash*; the check cache is keyed by it.
    #ul(
      [`stitchwort check`, `test`, `audit` and the language server stop here.],
      [`core` also has the *reference evaluator*: slow, but the check-time semantics.],
    )
  ]
  #v(1.2mm)
  #block(width: 100%, inset: 2mm, radius: 1.5mm, fill: red.lighten(90%), stroke: (dash: "dashed", paint: red, thickness: 0.7pt))[
    #text(weight: "bold", fill: red)[Trust boundary.] Everything after this point is *untrusted*: a bug can print a wrong answer but can never make a false proof check. Runtimes never depend on `elab`; differential tests compare them with the reference evaluator. Running a program continues at *5* (right), or at *7c* / *7d*.
  ]
  #v(1.2mm)
  #text(weight: "bold", size: 8.6pt, fill: blue)[Shared plumbing]
  #ul(
    [`crates/driver`: the pipeline itself (sessions, caching, tests, error rendering), shared by the CLI and the playground.],
    [`crates/cli`: the `stitchwort` command. `crates/lsp`: the language server (VS Code and the playground editor).],
  )
],
[
  // ---------------- Back ends ----------------
  #align(center, text(size: 8pt, fill: grey)[from 4, checked definitions ↓])
  #v(-0.6mm)
  #stage("5", "Erase and lower", "crates/rt  lower.rs", green)[
    Checked terms become the runtime's *IR*:
    #ul(
      [types, proofs and implicit arguments erased;],
      [lambdas → closures, partial calls → partial applications, case trees → `match`;],
      [std functions swapped for *natives* (Nat arithmetic, Text, arrays), bound by content hash.],
    )
  ]
  #arrow(label: [IR])
  #stage("6", "Optimise the IR", "crates/rt", green)[
    Simplifier (`opt.rs`), specialisation, state-handler fusion, tail recursion modulo cons, hoisting, and *in-place reuse* of cells nothing else holds (`reuse.rs`). Shared by the machine and native code.
  ]
  #arrow()
  #stage("7a", "Bytecode + machine", "rt  code.rs · machine.rs", green)[
    IR compiled to register bytecode, run by the machine on compact values with its own frame stack; effects run by the effect loop (`effect.rs`).
    #ul(
      [`stitchwort run` (the default runtime);],
      [`stitchwort build`: a standalone executable (bytecode + the `standalone` runtime, linked with `cc`);],
      [the *playground*: the whole compiler and this machine compiled to *WebAssembly* (`crates/web`).],
    )
  ]
  #v(1mm)
  #stage("7b", "Native code", "crates/native (Cranelift)", orange)[
    The same bytecode bodies compiled to machine code, linked with the runtime library (`value.rs`, `effect.rs`, `native_abi.rs`, mimalloc).
    #ul(
      [`stitchwort run --native`, `stitchwort build --native` (what the speed comparisons measure);],
      [not in the WebAssembly build.],
    )
  ]
  #v(1mm)
  #stage("7c", "JavaScript", "crates/js", purple)[
    Its own erasure and code generation straight from checked terms (no IR), plus TypeScript declarations and source maps.
    #ul(
      [`stitchwort run --js` (runs with Node), `stitchwort build --js` (an ES module).],
    )
  ]
  #v(1mm)
  #stage("7d", "Reference evaluator", "crates/core", red)[
    `stitchwort run --reference`: evaluates core terms directly. Slow; the yardstick the others are tested against.
  ]
],
)

#v(1.5mm)
#line(length: 100%, stroke: 0.5pt + luma(160))
#v(0.5mm)
#text(weight: "bold", size: 8.6pt, fill: blue)[Which path a command takes]
#v(-0.8mm)
#table(
  columns: (auto, 1fr, auto),
  stroke: none, inset: (x: 1.5mm, y: 0.9mm),
  fill: (_, y) => if calc.odd(y) { luma(245) },
  table.header([*Command*], [*Stages*], [*Runs on*]),
  [`stitchwort check` / `test` / `audit`], [1 → 4 (tests then run on 5 → 7a)], [—],
  [`stitchwort run`], [1 → 4 → 5 → 6 → 7a], [machine],
  [`stitchwort run --native` / `build --native`], [1 → 4 → 5 → 6 → 7b], [native code],
  [`stitchwort build`], [1 → 4 → 5 → 6 → 7a, linked into an executable], [machine, standalone],
  [`stitchwort run --js` / `build --js`], [1 → 4 → 7c], [Node / your JS],
  [`stitchwort run --reference`], [1 → 4 → 7d], [reference evaluator],
  [Playground (browser)], [1 → 4 → 5 → 6 → 7a, all in WebAssembly], [machine in WASM],
)

#v(1.5mm)
#text(weight: "bold", size: 9.6pt, fill: blue)[Words on this page]
#v(-0.6mm)
#grid(columns: (1fr, 1fr), column-gutter: 5mm, row-gutter: 1.1mm,
  [*Surface AST*: the program as written, as a tree with spans.],
  [*Erasure*: dropping what has no run-time meaning (types, proofs, implicit arguments).],
  [*Core term*: the fully explicit form the kernel checks; what hashes and proofs are about.],
  [*IR*: the runtime's erased form: closures, partial applications, matches, natives.],
  [*Content hash*: a definition's identity from its checked term; keys the check cache and binds natives.],
  [*Bytecode*: the IR compiled to register instructions; the machine runs it, native code compiles it.],
  [*Kernel*: the trusted checker in `crates/core`; the only part a proof's validity depends on.],
  [*Effect loop*: the runtime part that routes an ability's operations to their handler.],
  [*Reference evaluator*: evaluates core terms directly; defines what a program means.],
  [*In-place reuse*: overwriting a cell nothing else holds instead of freeing it and allocating.],
)
