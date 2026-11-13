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
      # On Linux, also the musl target, which the runtime library of
      # `stitchwort build` is built for, so executables link statically.
      toolchainFor =
        pkgs:
        let
          toolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
        in
        if pkgs.stdenv.hostPlatform.isLinux then
          toolchain.override {
            targets = [
              "wasm32-unknown-unknown"
              (muslTarget pkgs)
            ];
          }
        else
          toolchain;

      # The Rust target of this system's musl, as `aarch64-unknown-linux-musl`.
      muslTarget = pkgs: "${pkgs.stdenv.hostPlatform.parsed.cpu.name}-unknown-linux-musl";

      # On Linux, cargo builds for musl (docs/proposals/standalone-
      # executables.md, "Static Linux executables"): `stitchwort` and the
      # runtime library it links executables with, with musl's own C
      # compiler for mimalloc and as the linker.
      #
      # The linker is that compiler wrapper told to use mold. GNU ld takes
      # 1.70 s to link the CLI after a one-file change; mold takes 0.27 s,
      # which makes the whole rebuild 2.26 s into 0.83 s (SW-2105, measured
      # on x86_64 NixOS). `-B` points gcc at mold's `ld.mold`, which
      # `-fuse-ld=mold` then selects; the wrapper passes both through. Not
      # wild: it segfaults on this workspace.
      muslEnv =
        pkgs:
        let
          target = muslTarget pkgs;
          variable = builtins.replaceStrings [ "-" ] [ "_" ] target;
          cc = pkgs.pkgsStatic.stdenv.cc;
          moldLinker = pkgs.writeShellScript "musl-cc-mold" ''
            exec ${cc}/bin/${cc.targetPrefix}cc -B${pkgs.mold}/bin -fuse-ld=mold "$@"
          '';
        in
        {
          CARGO_BUILD_TARGET = target;
          "CC_${variable}" = "${cc}/bin/${cc.targetPrefix}cc";
          "AR_${variable}" = "${cc}/bin/${cc.targetPrefix}ar";
          "CARGO_TARGET_${nixpkgs.lib.toUpper variable}_LINKER" = "${moldLinker}";
        };

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
              ./.config/nextest.toml # test threads and test groups
              ./examples # example programs are the main test suite
              ./aoc # the lazy-versus-eager library comparison checks it (crates/driver/tests/library/std_library.rs)
              (lib.fileset.fileFilter (file: file.hasExt "snap") ./crates)
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./crates) # the standard library, read from the source tree by the tests
              ./crates/elab/src/std/core/order.txt # the core's file list
              ./web/index.html # the playground's examples are checked
              ./web/guide # so are the guide's (crates/web)
              ./docs/guide # the language guide's examples and quoted output are checked (crates/cli/tests/tools/guide.rs)
              ./web/tests/effect-shapes.sw # the effect-shape tests run it (crates/web)
              ./bench # benchmark counts are checked against the baseline
              ./games/rogue # a goals test checks its proofs with holes added (crates/cli/tests/tools/project.rs)
            ];
          };
          # What the playground bundles of the AoC project (its sources and
          # example and puzzle inputs), of the roguelike, of the Software
          # Foundations port and of the book (their sources), listed
          # explicitly. book/ is optional: bundle-projects.sh skips it.
          aocBundle = lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions ([
              ./aoc/stitchwort.yaml
              ./games/rogue/stitchwort.yaml
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./games/rogue/src)
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./aoc/src)
              (lib.fileset.fileFilter (file: file.hasExt "txt") ./aoc/examples)
              (lib.fileset.fileFilter (file: file.hasExt "txt") ./aoc/inputs)
              ./sf/stitchwort.yaml
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./sf/src)
            ] ++ lib.optionals (builtins.pathExists ./book/stitchwort.yaml) [
              ./book/stitchwort.yaml
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./book/src)
            ]);
          };
          # The standard library, as files: the installed binary reads it
          # from `../share/stitchwort/std` beside itself, and the playground
          # bundles it (docs/proposals/std-as-data.md).
          stdSource = lib.fileset.toSource {
            root = ./crates/elab/src/std;
            fileset = lib.fileset.unions [
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./crates/elab/src/std)
              ./crates/elab/src/std/core/order.txt
            ];
          };
          # bundle-std.sh takes the repository's root.
          stdBundleRoot = lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions [
              (lib.fileset.fileFilter (file: file.hasExt "sw") ./crates/elab/src/std)
              ./crates/elab/src/std/core/order.txt
            ];
          };
          commonArgs = {
            inherit src;
            pname = "stitchwort";
            version = "0.1.0";
            strictDeps = true;
          }
          // lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux (muslEnv pkgs);
          cargoArtifacts = craneLib.buildDepsOnly commonArgs;
          # `stitchwort build` links executables against the runtime library
          # (crates/standalone), which it looks for in `../lib/stitchwort/`
          # from its own binary (docs/proposals/standalone-executables.md
          # §2.2). Crane installs a static library in `lib/`, if at all.
          installRuntime = ''
            mkdir -p $out/share/stitchwort
            cp -r --no-preserve=mode ${stdSource} $out/share/stitchwort/std
            mkdir -p $out/lib/stitchwort
            if [ -e $out/lib/libstitchwort_standalone.a ]; then
              mv $out/lib/libstitchwort_standalone.a $out/lib/stitchwort/
            else
              cp ''${CARGO_TARGET_DIR:-target}/''${CARGO_BUILD_TARGET:+$CARGO_BUILD_TARGET/}release/libstitchwort_standalone.a $out/lib/stitchwort/
            fi
          '';
          nextestArgs = commonArgs // {
            inherit cargoArtifacts;
            INSTA_UPDATE = "no"; # fail on snapshot changes instead of writing .snap.new files
            doInstallCargoArtifacts = false; # nothing builds on these
            # The broad tier (docs/testing.md, "Tiers"): the `broad` profile
            # of `.config/nextest.toml`, and STITCHWORT_TIER for the corpus
            # sweeps. Every test runs, so one failure doesn't hide the others.
            cargoNextestExtraArgs = "--no-fail-fast --profile broad --features stitchwort-cli/dev";
            STITCHWORT_TIER = "broad";
            # The corpus sweeps go two at a time (`corpus-sweeps` in
            # `.config/nextest.toml`), each on a pool of 5 threads.
            STITCHWORT_TEST_THREADS = "5";
            # Nextest doesn't run doctests, and stitchwort-partial-model has
            # three (src/typed.rs, two of them `compile_fail`), so run those
            # here: about a second.
            postCheck = "cargoWithProfile test --doc --workspace --no-fail-fast";
            # Differential tests run extracted JS; generated declarations are type-checked.
            nativeBuildInputs = [
              pkgs.nodejs_22
              pkgs.typescript
            ];
          };
        in
        rec {
          # The tests, run by cargo-nextest (every test in its own process, test
          # binaries side by side; `.config/nextest.toml`), then the doctests.
          # `stitchwort` is the broad tier (what `nix flake check` runs);
          # `stitchwort-all` is the all tier, built only on request (`task
          # test:all:nix`).
          stitchwort = craneLib.cargoNextest (nextestArgs // { pname = "stitchwort"; });
          stitchwort-all = craneLib.cargoNextest (
            nextestArgs
            // {
              pname = "stitchwort-all";
              cargoNextestExtraArgs = "--no-fail-fast --profile all --features stitchwort-cli/dev";
              STITCHWORT_TIER = "all"; # every corpus sweep over the whole corpus
            }
          );
          # The CLI binary alone, without running the test suite: what `nix run`
          # and `nix build` give by default. The tested build is `stitchwort`
          # (in `checks`, so `nix flake check` still runs every test).
          #
          # It builds `-p` the crates it ships. A root `cargo build` would also
          # build stitchwort-bench, which depends on stitchwort-dev-features,
          # and Cargo would give the shipped binary the dev feature set
          # (`test-bypass` and the rest). `dev/features-check` (the quick tier)
          # fails if these arguments' feature set has any of them.
          stitchwort-bin = craneLib.buildPackage (
            commonArgs
            // {
              inherit cargoArtifacts;
              cargoExtraArgs = "--locked -p stitchwort-cli -p stitchwort-standalone";
              doCheck = false;
              postInstall = installRuntime;
              meta.mainProgram = "stitchwort";
            }
          );
          # The CLI with native code (Cranelift, docs/proposals/native-
          # compilation.md): `nix build .#stitchwort-native-bin`. The
          # default binary leaves it out.
          stitchwort-native-bin = craneLib.buildPackage (
            commonArgs
            // {
              inherit cargoArtifacts;
              pname = "stitchwort-native";
              cargoExtraArgs = "--locked -p stitchwort-cli -p stitchwort-standalone --features stitchwort-cli/native";
              doCheck = false;
              postInstall = installRuntime;
              meta.mainProgram = "stitchwort";
            }
          );
          clippy = craneLib.cargoClippy (
            commonArgs
            // {
              inherit cargoArtifacts;
              # With the CLI's `native` feature, so its code is linted too.
              cargoClippyExtraArgs = "--all-targets --features stitchwort-cli/dev -- --deny warnings";
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

          # The playground's editor: CodeMirror 6 and its language-server
          # client, bundled by nixpkgs' esbuild over the locked npm
          # dependencies (web/editor/package-lock.json). After changing the
          # lockfile, set npmDepsHash to lib.fakeHash and copy the hash from
          # the build's error.
          editor = pkgs.buildNpmPackage {
            pname = "stitchwort-playground-editor";
            version = "0";
            src = lib.fileset.toSource {
              root = ./web/editor;
              fileset = lib.fileset.unions [
                ./web/editor/package.json
                ./web/editor/package-lock.json
                ./web/editor/src
                ./web/editor/build.sh
              ];
            };
            npmDepsHash = "sha256-tw21Ehe84oBhAJ1zV4nQ2FOw/tvWa9aPp06UENn/AmM=";
            dontNpmBuild = true;
            nativeBuildInputs = [ pkgs.esbuild ];
            installPhase = ''
              SKIP_NPM_CI=1 bash build.sh $out
            '';
          };

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
                pkgs.nodejs_22
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
                cp ${./web/lsp-worker.js} $out/lsp-worker.js
                cp ${./web/lsp-search-worker.js} $out/lsp-search-worker.js
                cp ${./web/coi-serviceworker.js} $out/coi-serviceworker.js
                bash ${./web/bundle-std.sh} ${stdBundleRoot} $out/pkg
                node ${./web/bundle-std-cache.mjs} $out/pkg
                bash ${./web/bundle-projects.sh} ${aocBundle} $out/pkg
                cp -r --no-preserve=mode ${editor} $out/dist
                bash ${./web/write-version.sh} $out
              '';
            }
          );
        };
    in
    {
      packages = forAllSystems (pkgs: rec {
        inherit (buildsFor pkgs)
          stitchwort-bin
          stitchwort-native-bin
          stitchwort-all
          playground
          editor
          ;
        default = stitchwort-bin;
      });

      # `nix flake check`: the broad tier (build + tests, clippy, rustfmt)
      checks = forAllSystems (
        pkgs:
        let
          builds = buildsFor pkgs;
        in
        {
          inherit (builds)
            stitchwort
            clippy
            fmt
            debug-builtins
            ;

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

      devShells = forAllSystems (
        pkgs:
        let
          default = pkgs.mkShell {
            packages = [
              (toolchainFor pkgs)
              pkgs.cargo-insta # snapshot tests for example programs
              pkgs.cargo-watch
              pkgs.cargo-llvm-cov # test coverage
              pkgs.cargo-mutants # mutation testing: do the tests notice when code changes?
              pkgs.cargo-nextest # runs the test tiers (.config/nextest.toml)
              pkgs.lld # faster linking of the many test binaries (see env below)
              pkgs.go-task # `task`: the menu of what to run (Taskfile.yml)
              pkgs.python3 # dev/memguard, which every test task runs under
              pkgs.jq # task test:lanes-nonempty reads `cargo nextest list` JSON
              pkgs.kache # compiler cache for lane checkouts only (task worktree:new, D2200)

              # Browser playground: Rust -> WASM
              pkgs.wasm-bindgen-cli
              pkgs.binaryen # wasm-opt

              # Running and type-checking extracted JS/TS
              pkgs.nodejs_22
              pkgs.typescript
              pkgs.esbuild # web/editor/build.sh bundles the playground's editor

              # Nix
              pkgs.nixfmt
            ];
            env = {
              # Local release builds (every test build) recompile incrementally:
              # a one-line `elab` edit rebuilds in about 20 s, not 130 s. Only
              # the devShell sets this; the package and check builds above do not
              # inherit it, so the distributed binary is built from scratch.
              CARGO_PROFILE_RELEASE_INCREMENTAL = "true";
            }
            // pkgs.lib.optionalAttrs pkgs.stdenv.hostPlatform.isDarwin {
              # Link with lld: a rebuild links about 150 test binaries, and lld
              # takes about 15% off its CPU time (SW-1754). A target-specific
              # variable, not RUSTFLAGS, so `.cargo/config.toml`'s wasm32
              # rustflags still apply; the package and check builds don't see it.
              CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS = "-C link-arg=-fuse-ld=lld";
              CARGO_TARGET_X86_64_APPLE_DARWIN_RUSTFLAGS = "-C link-arg=-fuse-ld=lld";
            }
            // pkgs.lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux (muslEnv pkgs);
          };
        in
        {
          inherit default;

          # `nix develop .#compare`: the default shell plus the other languages
          # of `task bench:compare` (bench/compare). Lean is a large closure, so
          # it stays out of the shell every lane enters.
          compare = pkgs.mkShell {
            inputsFrom = [ default ];
            packages = [
              pkgs.lean4
              pkgs.hyperfine
              pkgs.pypy3
            ]
            # `--instructions` counts with `perf stat` on Linux.
            ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [ pkgs.perf ];
          };
        }
      );

      formatter = forAllSystems (pkgs: pkgs.nixfmt);
    };
}
