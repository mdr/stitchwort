# The standard library as data (SW-1136)

Status: implemented in the same lane (D2249, D2256, Matt, 3 Nov 2026).
Architecture review step 2 (`docs/research/architecture-review.md`).

No build embeds the `.sw` standard library. A `.sw` edit compiles no Rust.
Single-file distribution is not a goal. `std_text()` (crates/elab/src/std_dir.rs)
reads the library once per process from files; where it looks is the only
design question.

## Where each host finds std

First match wins:

1. `--std-dir` (`use_std_dir`), then `STITCHWORT_STD_DIR`. Unchanged; an
   explicit choice always overrides.
2. **Installed binary:** `<exe dir>/../share/stitchwort/std`, with the
   executable path canonicalised (a profile symlink points into the store).
   `flake.nix` installs it there (`postInstall`, from the `std` directory of
   the source), beside `lib/stitchwort/` which the runtime library already
   uses the same way.
3. **Dev builds and tests:** the nearest ancestor of the executable that has
   `crates/elab/src/std/core/order.txt` (cargo's `target/release/deps/<test>`
   and `target/release/stitchwort` are inside the checkout; so are nextest's
   binaries in the `nix flake check` sandbox, whose source tree is copied
   and built in place), then the same search from the current directory
   (for a `CARGO_TARGET_DIR` outside the checkout; cargo runs tests in the
   crate's directory). No path is baked in at compile time, so a worktree
   and its kache-restored objects stay interchangeable. Installed beats dev,
   so an installed `stitchwort` run inside a checkout uses its own std.
4. **Nothing found:** a clear error naming the places tried and the two
   overrides, not a fallback to something stale.
5. **Playground (wasm):** no file system. `web/build.sh` (and the flake's
   `playground`) writes `pkg/std.bundle`, the library's files concatenated
   (`path bytes\n` then the bytes, so no escaping); each JS host fetches it
   beside the wasm and passes it to `load_std(bytes)` before the first call.
   Content-hashed in `version.json` like the other compiler files (a std edit
   changes `compiler`). A `.sw` edit needs the bundle step, not cargo.
6. **Language server:** library documents already come from the loaded text
   (`nav::std_source`); where the library was read from a directory, the
   server now answers `Place::Library` with the file's own `file:` URI so
   the editor opens the real file (and edits it), else the `std:` scheme as
   today (wasm, or the file missing).

## Core file order

`std/core/order.txt`: one core file name per line (no extension), in
dependency order; `#` starts a comment. It replaces `CORE_FILES`/`core_files!`.
A new core file is a new line, not a rebuild. The existing test that every
`std/core/*.sw` is listed now checks the manifest. A listed file that is
missing, or a duplicate, is an error.

## A hash of the std a binary was built for: not kept

A binary is no longer built for a std, so a build-time hash would mean
build.rs reading the `.sw` files and recompiling on every edit, which is
what this change removes. What protects core builtins already works on the
text read, not on the build: registration checks each builtin's type, arity
and the shapes of `Nat`, `Bool`, `Decidable` (`E-BUILTIN`, a hard error), and
the content-pinned natives are verified by `pinned_hashes` (a pin that stops
matching is dropped silently at run time, which only that test catches). A
std that differs in a way those miss is outside the guarantees, as
`--std-dir` already is (docs/core.md, SW-898). The installed std comes from
the same source as the binary (one flake package), so a mismatch needs an
explicit override. So: no new mismatch check; `mode()` says which directory a
test run read, and the caches key on a hash of the text (below).

## Fingerprint and cache keys

- The check cache keys on each library file's text as read already (SW-145),
  and the test-result cache and the compile cache use `build_fingerprint()`.
  That function now always mixes in a BLAKE3 of the core and library text; before, it did so only
  for a directory read, because `FINGERPRINT` covered the embedded copy.
  Hashing ~1 MB with BLAKE3 is under a millisecond, once per process.
- `driver/build.rs` stops hashing `.sw` files (`source_files` keeps `.rs`), and
  stops declaring the crates' `src` directories as `rerun-if-changed` (cargo
  scans directories recursively, so a `.sw` under `elab/src/std` would rerun
  the script); it declares each `.rs` file instead. A `.sw` edit then leaves
  `FINGERPRINT` and every crate untouched, and the caches are invalidated
  exactly as far as the text changed: the key moves, which is the point,
  but nothing is compiled. `SOURCE_FINGERPRINT` (is the wasm bundle stale?)
  no longer covers `.sw`; the bundle's std (`pkg/std.bundle`) is hashed into
  `version.json`'s `compiler` field instead.

## Not done

SW-1109 (a std snapshot as a shipped data file) and anything beyond the
playground's single bundle file.
