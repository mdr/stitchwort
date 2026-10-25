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
              ./clippy.toml # disallows the standard library's hash maps
              ./examples # example programs are the main test suite
              ./aoc # the lazy-versus-eager library comparison checks it (crates/driver/tests/std_library.rs)
              (lib.fileset.fileFilter (file: file.hasExt "snap") ./crates)
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./crates) # the prelude
              ./web/index.html # the playground's examples are checked
              ./web/guide # so are the guide's (crates/web)
              ./docs/guide # the language guide's examples and quoted output are checked (crates/cli/tests/guide.rs)
              ./web/tests/effect-shapes.sw # the effect-shape tests run it (crates/web)
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
              STITCHWORT_SLOW = "1"; # the full gate also runs the slow tier of tests (`dev/t slow`)
              # Run every test binary, so one failure doesn't hide the others.
              cargoTestExtraArgs = "--no-fail-fast";
              # Differential tests run extracted JS; generated declarations are type-checked.
              nativeCheckInputs = [
                pkgs.nodejs_22
                pkgs.typescript
              ];
              meta.mainProgram = "stitchwort";
            }
          );
          # The CLI binary alone, without running the test suite: what `nix run`
          # and `nix build` give by default. The tested build is `stitchwort`
          # (in `checks`, so `nix flake check` still runs every test).
          stitchwort-bin = craneLib.buildPackage (
            commonArgs
            // {
              inherit cargoArtifacts;
              doCheck = false;
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

          # One test binary that loads the prelude, built and run in the debug
          # profile (the other checks are release), so debug-only failures such
          # as arithmetic overflow and `debug_assert!` are caught by the gate.
          debug-builtins = craneLib.cargoTest (
            commonArgs
            // {
              pname = "stitchwort-debug-builtins";
              CARGO_PROFILE = "dev";
              cargoArtifacts = craneLib.buildDepsOnly (
                commonArgs
                // {
                  pname = "stitchwort-debug-builtins";
                  CARGO_PROFILE = "dev";
                }
              );
              doInstallCargoArtifacts = false; # nothing builds on this one
              cargoTestExtraArgs = "-p stitchwort-driver --test builtins";
              INSTA_UPDATE = "no";
            }
          );

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
                cp -r --no-preserve=mode ${./web/guide} $out/guide
                cp ${./web/playground-worker.js} $out/playground-worker.js
                bash ${./web/bundle-projects.sh} ${aocBundle} $out/pkg
                bash ${./web/write-version.sh} $out
              '';
            }
          );
        };
    in
    {
      packages = forAllSystems (pkgs: rec {
        inherit (buildsFor pkgs) stitchwort stitchwort-bin playground;
        default = stitchwort-bin;
      });

      # `nix flake check`: build + tests, clippy, rustfmt
      checks = forAllSystems (
        pkgs:
        let
          builds = buildsFor pkgs;
        in
        {
          inherit (builds) stitchwort clippy fmt debug-builtins;

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
            pkgs.cargo-nextest # `dev/t full`: the whole suite with test binaries run in parallel

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
