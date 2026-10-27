# Stitchwort

A small, total, dependently-typed functional language, for fun and exploring
ideas. See [DESIGN.md](DESIGN.md) for where it's going, and
[docs/core.md](docs/core.md) for what's implemented.

Try it in the browser: the [playground](https://mdr.github.io/stitchwort/), with a
[language guide](https://mdr.github.io/stitchwort/guide/guide.html).

```sh
nix develop                     # or `direnv allow`

cargo run -- check examples/extract/append.sw
cargo run -- eval examples/extract/append.sw "appendNats [1, 2] [3]"
cargo run -- test examples/accept/tests.sw      # run it twice: results are cached
cargo run -- run examples/accept/adder.sw       # run `main` on the fast runtime, reading and printing lines
cargo run -- run --reference examples/accept/adder.sw  # the same on the type checker's own evaluator (slower)
cargo run -- run --js examples/accept/adder.sw  # the same, compiled to JS and run under Node (much faster)
cargo run -- repl examples/extract/append.sw
cargo run -- build --js examples/extract/append.sw -o out/

# a project: a folder with a stitchwort.yaml, its files in namespaces
# (docs/proposals/multi-file.md); run these inside it
cd myproject
stitchwort run Day05.main       # run a function by its full name
stitchwort test                 # every namespace's tests (results cached in .stitchwort/)
stitchwort check Day05          # one namespace, and the ones it uses (prints "checked N namespaces of NAME")
stitchwort axioms Day05.total   # the axioms (today only Quot.sound) a definition depends on
stitchwort axioms file.sw name  # the same for a definition in a single file
stitchwort fmt                  # format the project's sources in place (--check lists what would change)

nix build .#playground          # the browser playground: open result/index.html via a web server
                                #   (it needs result/playground-worker.js and result/pkg/ beside it)
task web:build                  # or build it into web/pkg/ during development
task web:serve                  # build, then serve web/ at http://127.0.0.1:8000:
                                #   index.html (playground), stress.html (deep and large programs
                                #   in WebAssembly; stress.html#run runs them all on load)
task test:browser               # build, then test the playground in headless Chrome (needs Chrome)

task --list                     # the menu: building, tests, snapshots, benchmarks, playground, board, AoC
task test:lane AREA=syntax      # tests in tiers (docs/testing.md): lane < 10 s, merge < 60 s,
task test:merge                 #   daily < 5 minutes (what `nix flake check` runs), full
task test:daily
task bench                      # benchmarks, compared with bench/baseline.toml
```

`stitchwort run` exit codes: 0 means success; 1 means the program didn't check (a compile error, or a file or usage error); 2 means it checked but failed while running (a runtime error, or it ran out of resources).

## Editor support

A local VS Code syntax-colouring extension for `.sw` files is in
[`editors/vscode/`](editors/vscode/README.md).

## Advent of Code

Solutions with proofs are in [`aoc/`](aoc/), one project for every year:
2025 in `Aoc.Year2025` (notes in [docs/aoc-2025.md](docs/aoc-2025.md)),
2024 in `Aoc.Year2024` (notes in [aoc/NOTES-2024.md](aoc/NOTES-2024.md)),
and helpers they share in `Aoc.Common`. Each day is a namespace, such as
`Aoc.Year2025.Day01`, in a folder of the same name. The puzzle inputs are in
`aoc/inputs/YYYY/dayNN.txt`; run a day with
`cd aoc && cargo run --release -- run --js Aoc.Year2025.Day01.main < inputs/2025/day01.txt`.

## Licence

MIT; see [LICENSE](LICENSE).
