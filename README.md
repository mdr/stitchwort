# Stitchwort

A small, total, dependently-typed functional language, for fun and exploring
ideas. See [DESIGN.md](DESIGN.md) for where it's going, and
[docs/core.md](docs/core.md) for what's implemented.

```sh
nix develop                     # or `direnv allow`

cargo run -- check examples/extract/append.sw
cargo run -- eval examples/extract/append.sw "appendNats [1, 2] [3]"
cargo run -- test examples/accept/tests.sw      # run it twice: results are cached
cargo run -- run examples/accept/adder.sw       # run `main`, reading and printing lines
cargo run -- run --js examples/accept/adder.sw  # the same, compiled to JS and run under Node (much faster)
cargo run -- repl examples/extract/append.sw
cargo run -- build --js examples/extract/append.sw -o out/

# a project: a folder with a stitchwort.yaml, its files in namespaces
# (docs/proposals/multi-file.md); run these inside it
cd myproject
stitchwort run Day05.main       # run a function by its full name
stitchwort test                 # every namespace's tests (results cached in .stitchwort/)
stitchwort check Day05          # one namespace, and the ones it uses

nix build .#playground          # the browser playground: open result/index.html via a web server
                                #   (it needs result/playground-worker.js and result/pkg/ beside it)
./web/build.sh                  # or build it into web/pkg/ during development
./web/serve.sh                  # build, then serve web/ at http://127.0.0.1:8000:
                                #   index.html (playground), stress.html (deep and large programs
                                #   in WebAssembly; stress.html#run runs them all on load)
./web/test.sh                   # build, then test the playground in headless Chrome (needs Chrome)

cargo test                      # example programs, snapshots, JS differential tests
nix flake check                 # build, tests, clippy, rustfmt
cargo run --release -p stitchwort-bench   # benchmarks, compared with bench/baseline.toml
```

## Editor support

A local VS Code syntax-colouring extension for `.sw` files is in
[`editors/vscode/`](editors/vscode/README.md).

## Advent of Code 2025

Solutions with proofs are in [`aoc/`](aoc/), with notes in
[docs/aoc-2025.md](docs/aoc-2025.md). Puzzle inputs aren't included; put
yours in `aoc/inputs/dayNN.txt` and run
`cargo run --release -- run --js aoc/day01.sw < aoc/inputs/day01.txt`.

## Licence

MIT; see [LICENSE](LICENSE).
