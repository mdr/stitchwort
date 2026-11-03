// One-page map of the workspace's crates. Regenerate with build.sh; the
// diagram (crates.svg) comes from dev/crate-graph, which reads the workspace.
#let commit = sys.inputs.at("commit", default: "unknown")
#let day = sys.inputs.at("date", default: "")

#set page(paper: "a4", flipped: true, margin: 10mm)
#set text(size: 7.6pt, font: ("Helvetica", "Arial"))
#set par(leading: 0.38em, spacing: 0.5em)

#let red = rgb("#b00020")
#let blue = rgb("#1a5fb4")
#let orange = rgb("#c05800")
#let green = rgb("#2a7f3f")

#grid(
  columns: (1fr, auto),
  align: (left + bottom, right + bottom),
  text(size: 15pt, weight: "bold")[Stitchwort: the crates],
  text(size: 7pt, fill: luma(110))[workspace at commit #commit #day · generated from `cargo metadata` and the sources],
)
#v(1mm)
#line(length: 100%, stroke: 0.5pt + luma(160))
#v(1.5mm)

#grid(
  columns: (auto, 1fr),
  column-gutter: 4mm,
  image("crates.svg", width: 215mm),
  [
    #text(weight: "bold", size: 8pt)[How to read it]
    #v(-1mm)
    - An arrow `A → B` means A depends on B. Layers run from the interfaces (top) down to the front end. Edges implied by a longer path are left out (`cli → core` is there through `driver`), so the picture shows structure, not every `use`.
    - #text(fill: orange)[Dashed orange]: optional dependency (the CLI's `native` feature).
    - #text(fill: green)[Dotted green]: not a Cargo edge. `stitchwort build` links `standalone`'s static library; `cli` has it only as a dev-dependency, so tests build it.
    - #text(fill: blue)[wasm]: part of the browser playground's build (everything `web` pulls in, through `driver`).
    - #text(fill: red)[Red box]: the trusted kernel.
    - Sizes: `src` is Rust lines in `src/`, `tests` the rest of each crate's Rust (tests, examples, benches), `.sw` Stitchwort lines. The blue bar is `src`, on a square-root scale.
    - Dev-dependencies are not drawn. They mostly point at `driver`, `core` and `rt`, for tests.

    #v(1mm)
    #text(weight: "bold", size: 8pt)[Boundary facts]
    #v(-1mm)
    - `core` is the kernel and more: it also has the pretty-printer, a reference evaluator for differential tests (feature `reference`), erasure, content hashing, resource budgets, and `Term::Meta`, the elaborator's metavariable.
    - `rt` holds most of the backend: erasure, IR, optimiser, bytecode machine, native ABI. `js` and `native` build on it, and `host` and `standalone` run it.
    - The runtimes (`rt`, `js`, `native`, `standalone`) depend on `core` and `syntax`, never on `elab`: they run checked definitions and are untrusted, so they can get an output wrong but not make a false proof check.
    - `elab` is the largest crate by far, and carries the `.sw` standard library (`src/std/`).
    - `driver` is the shared pipeline: `cli` and `web` both sit on it, so neither reimplements checking.
    - `native` (Cranelift) is optional for the CLI and absent from the WebAssembly build; `host` is in it, pulled in by `driver`.
    - `partial-model` is used by nothing in the compiler, only by `driver`'s tests; `bench` measures `driver`.
    - Not Rust and not shown: `board/` (ticket board, JS), `editors/vscode`, the playground page in `web/`, and the `.sw` examples and games.
  ],
)
