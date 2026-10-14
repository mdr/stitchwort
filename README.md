# Stitchwort

A small, total, dependently-typed functional language, for fun and exploring
ideas. See [DESIGN.md](DESIGN.md) for where it's going, and
[docs/core.md](docs/core.md) for what's implemented.

```sh
nix develop                     # or `direnv allow`

cargo run -- check examples/extract/append.sw
cargo run -- eval examples/extract/append.sw "appendNats [1, 2] [3]"
cargo run -- repl examples/extract/append.sw
cargo run -- build --js examples/extract/append.sw -o out/

cargo test                      # example programs, snapshots, JS differential tests
nix flake check                 # build, tests, clippy, rustfmt
```
