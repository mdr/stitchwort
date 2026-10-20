{
  description = "Stitchwort: a small, total, dependently-typed functional language";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane.url = "github:ipetkov/crane";
  };

  outputs =
    {
      nixpkgs,
      rust-overlay,
      crane,
      ...
    }:
    let
      systems = [
        "aarch64-darwin"
        "x86_64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      forAllSystems =
        f:
        nixpkgs.lib.genAttrs systems (
          system:
          f (
            import nixpkgs {
              inherit system;
              overlays = [ rust-overlay.overlays.default ];
            }
          )
        );

      # Rust toolchain (version, components and wasm target pinned in rust-toolchain.toml)
      toolchainFor = pkgs: pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;

      # Builds and checks for the Rust workspace
      buildsFor =
        pkgs:
        let
          inherit (pkgs) lib;
          craneLib = (crane.mkLib pkgs).overrideToolchain toolchainFor;
          src = lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions [
              (craneLib.fileset.commonCargoSources ./.)
              ./examples # example programs are the main test suite
              ./aoc # the lazy-versus-eager library comparison checks it (crates/driver/tests/std_library.rs)
              (lib.fileset.fileFilter (file: file.hasExt "snap") ./crates)
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./crates) # the prelude
              ./web/index.html # the playground's examples are checked
              ./bench # benchmark counts are checked against the baseline
            ];
          };
          # What the playground bundles of the AoC project: its sources and
          # example and puzzle inputs, listed explicitly.
          aocBundle = lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions [
              ./aoc/stitchwort.yaml
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./aoc/src)
              (lib.fileset.fileFilter (file: file.hasExt "txt") ./aoc/examples)
              (lib.fileset.fileFilter (file: file.hasExt "txt") ./aoc/inputs)
            ];
          };
          commonArgs = {
            inherit src;
            pname = "stitchwort";
            version = "0.1.0";
            strictDeps = true;
          };
          cargoArtifacts = craneLib.buildDepsOnly commonArgs;
        in
        {
          stitchwort = craneLib.buildPackage (
            commonArgs
            // {
              inherit cargoArtifacts;
              INSTA_UPDATE = "no"; # fail on snapshot changes instead of writing .snap.new files
              # Differential tests run extracted JS; generated declarations are type-checked.
              nativeCheckInputs = [
                pkgs.nodejs_22
                pkgs.typescript
              ];
              meta.mainProgram = "stitchwort";
            }
          );
          clippy = craneLib.cargoClippy (
            commonArgs
            // {
              inherit cargoArtifacts;
              cargoClippyExtraArgs = "--all-targets -- --deny warnings";
            }
          );
          fmt = craneLib.cargoFmt { inherit src; };

          # The browser playground: the compiler as WebAssembly, plus the page.
          playground = craneLib.buildPackage (
            commonArgs
            // {
              pname = "stitchwort-playground";
              cargoArtifacts = null;
              CARGO_BUILD_TARGET = "wasm32-unknown-unknown";
              cargoExtraArgs = "-p stitchwort-web";
              doCheck = false;
              nativeBuildInputs = [
                pkgs.wasm-bindgen-cli
                pkgs.binaryen
              ];
              installPhaseCommand = ''
                mkdir -p $out/pkg
                wasm-bindgen --target web --no-typescript --out-dir $out/pkg \
                  target/wasm32-unknown-unknown/release/stitchwort_web.wasm
                wasm-opt -Oz --enable-bulk-memory --enable-nontrapping-float-to-int \
                  $out/pkg/stitchwort_web_bg.wasm -o $out/pkg/stitchwort_web_bg.wasm
                cp ${./web/index.html} $out/index.html
                cp ${./web/playground-worker.js} $out/playground-worker.js
                bash ${./web/bundle-projects.sh} ${aocBundle} $out/pkg
              '';
            }
          );
        };
    in
    {
      packages = forAllSystems (pkgs: rec {
        inherit (buildsFor pkgs) stitchwort playground;
        default = stitchwort;
      });

      # `nix flake check`: build + tests, clippy, rustfmt
      checks = forAllSystems (
        pkgs:
        let
          builds = buildsFor pkgs;
        in
        {
          inherit (builds) stitchwort clippy fmt;

          # The kanban board's tests (board/): Node's standard library only.
          board =
            pkgs.runCommand "board-tests"
              {
                nativeBuildInputs = [ pkgs.nodejs_22 ];
                src = pkgs.lib.fileset.toSource {
                  root = ./board;
                  fileset = ./board;
                };
              }
              ''
                cp -r $src board
                cd board
                node --test board.test.js
                touch $out
              '';
        }
      );

      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            (toolchainFor pkgs)
            pkgs.cargo-insta # snapshot tests for example programs
            pkgs.cargo-watch
            pkgs.cargo-llvm-cov # test coverage
            pkgs.cargo-mutants # mutation testing: do the tests notice when code changes?

            # Browser playground: Rust -> WASM
            pkgs.wasm-bindgen-cli
            pkgs.binaryen # wasm-opt

            # Running and type-checking extracted JS/TS
            pkgs.nodejs_22
            pkgs.typescript

            # Nix
            pkgs.nixfmt
          ];
        };
      });

      formatter = forAllSystems (pkgs: pkgs.nixfmt);
    };
}
