# Stitchwort

A small, total, dependently-typed functional language, for fun and exploring
ideas. See [DESIGN.md](DESIGN.md) for where it's going, and
[docs/core.md](docs/core.md) for what's implemented.

```sh
nix develop                     # or `direnv allow`

cargo run -- check examples/extract/append.sw
cargo run -- eval examples/extract/append.sw "appendNats [1, 2] [3]"
cargo run -- test examples/accept/tests.sw      # run it twice: results are cached
cargo run -- repl examples/extract/append.sw
cargo run -- build --js examples/extract/append.sw -o out/

nix build .#playground          # the browser playground: open result/index.html via a web server
./web/build.sh                  # or build it into web/pkg/ during development

cargo test                      # example programs, snapshots, JS differential tests
nix flake check                 # build, tests, clippy, rustfmt
```
