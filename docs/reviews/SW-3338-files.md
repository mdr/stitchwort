# SW-3338 review: stage F1, the `Files` ability

Opus review of `lane/SW-3338` (`git diff main...lane/SW-3338`, 96 files), 15 Nov 2026.
Read: CLAUDE.md, `docs/proposals/file-io-and-text.md` §2, §3, §6, the ticket's
lane notes, and the whole diff apart from the hash snapshots, which were
checked by script (below).

Ran: `cargo nextest run -p stitchwort-rt --lib -E 'test(host_files)'`
(4 passed). I also probed the lane's release binary
(`target/release/stitchwort`, built 08:37, after `dae604e55`) with small
programs in the scratchpad: edge-case paths on the model and on the host, a
`{IO, Fail, Files, Partial}` main on machine, `--reference` and `--native`,
`Files.simulate` plus `printError` under `--js`, and writes over a FIFO, a
dangling link, a hard link and a read-only file.

**Verdict: merge after fixes.** The design matches the paper and D3595,
D3586 and D3587. The checking invariant holds (§1). The runners agree,
including on the four-ability row. The std laws say what their names claim.
But the host's `write` has three behaviours a user would call data loss or a
security bug (H1, H2, M1), and a test writes into the source tree, where the
lane committed the result (H3).

Must fix before merging: **H1, H2, H3, M1, M4** (all small).
Should fix in this lane, or file as tickets: **M2, M3, M5**.
Low items: tickets or one batch.

---

## High

### H1. `write` overwrites a read-only file
`crates/rt/src/files.rs:97-123`. The temporary file is created in the
folder, given the old file's mode and renamed over the target. A rename
needs write permission on the folder, not on the file, so a `chmod 444` file
is silently replaced. The paper and the docs say that's `NotPermitted`
("the program's user may not read or write it"), and `echo x > ro.txt`
refuses it.

Repro (scratchpad `sw3338rev/ro`): `echo keep > ro.txt; chmod 444 ro.txt`,
then `Files.write ("ro.txt".toPath, "overwritten")` prints `ok`, and the
file now holds `overwritten`, still mode `r--r--r--`.

Fix: when the target exists, check that it's writable before making the
temporary file: open it with `OpenOptions::new().write(true)` (no truncate)
and drop the handle, so ACLs and root are handled as the OS does it. Map the
failure through `failure()`, so it gives `NotPermitted`. Add the case to
`host_files_not_permitted_and_permissions_kept`.

### H2. `write` replaces FIFOs, devices and dangling links with regular files
`files.rs:93-96, 97-102, 123`.
- An existing target that isn't a regular file (`Kind::Other`: FIFO, socket,
  device) gets the rename treatment, so it is replaced by a regular file.
  As root, `Files.write ("/dev/null".toPath, …)` would replace `/dev/null`.
  As a user, writing to a FIFO destroys it, and `/dev/stdout` fails (the
  temporary file can't be made in `/dev`), though writing there is a
  normal thing to ask.
- A dangling symlink: `canonicalize` fails, `unwrap_or(path)` keeps the
  link's own path, and the rename replaces the **link** with a file. The doc
  comment, Files.sw:228 and syntax.md all say links are written through.

Repro (scratchpad `sw3338rev/fifo`): `mkfifo pipe; ln -s nowhere.txt
dangling`. Writing each prints `ok`, and `ls -la` then shows both as regular
files (`-rw-r--r--`).

Fix (small, the orchestrator's call):
- A target that exists and isn't a regular file is written in place, with
  `OpenOptions::write(true).truncate(true)`. Atomic replacement means
  nothing for a device.
- A dangling link resolves to `parent(link).join(read_link(link))`, and the
  write goes there (the temporary file beside it), so the link survives.
- Add both cases to the host tests, under `#[cfg(unix)]`.

### H3. A test writes into `crates/cli/`, and the result is committed
- `crates/cli/out.txt` (contents `written é`) is committed in `64cc7881c`.
- The cause is `crates/cli/tests/running/build.rs:144`: `run_executable`
  starts the built executable with no `current_dir`, so it runs in the
  test's working directory, the crate folder. `a_files_program_runs_as_it_does_under_run`
  therefore has the executable write `crates/cli/out.txt`. The assertion
  reads `dir/out.txt`, which `stitchwort run` wrote, so the test passes
  without checking that the executable writes in its own folder.
- Every run of the test rewrites a tracked file.

Fix: `run_executable` sets `.current_dir(exe.parent())`, the same folder
`stitchwort(dir, …)` uses. Also `git rm crates/cli/out.txt`.

---

## Medium

### M1. The new contents sit in a world-readable temporary file
`files.rs:114-121`. The temporary file is made with the default mode
(`0o666 & umask`, so `0644` with the usual umask). The text is written and
synced, and only then is the old mode copied on. A `0600` file's new
contents (a token, say) are therefore readable by other users for that
window.

Fix:
- Create the temporary file `0o600` (`std::os::unix::fs::OpenOptionsExt::mode`).
- Copy the old mode on (`set_permissions`) before `write_all`, or after the
  write and before the rename; at no point is it wider than the final mode.
- For a new file, keep the default mode: set it after the write, or create
  with `0o666` and let the umask apply as now.

### M2. Paths: the model and the host disagree outside `Path.parse`'s output
`Files.sw:25` (`Path` is a public record), `files.rs:40-47`
(`host_path` joins the parts as they are), and `Disk.*` (parts taken as
they are). Repro (scratchpad `sw3338rev/edge`, the same script on the
pretend disk and on a real folder holding `a/k`):

| operation | model | host |
|---|---|---|
| `write ".."` | ok (a file named `..`) | `NotAFile` |
| `write "a/.."` | ok | `NotAFile` |
| `write {parts = ["a", ""]}` | ok (a file named `""`) | `NotAFile` (host path `a/`) |
| `write {parts = ["a/q"]}` | ok (one part `a/q`, at the top) | ok, `a/q` inside `a` |
| `write {parts = ["."]}` | ok (a file named `.`) | `NotAFile` |
| `list "."` afterwards | `., .., a, a/q` | `a` |

`..` is documented as the one known difference (Files.sw:22-24, :240;
syntax.md). The rows built by hand aren't documented, and they will come
up: with no way to join paths (see §6), users will write
`{ path | parts = path.parts ++ [name] }`, and `name` may contain `/`. On
`..`, the model succeeds where the host refuses, which is the wrong way
round for a test oracle: a test can pass on behaviour the host doesn't
have.

Fix (orchestrator's call; my recommendation):
- The runners and the `Disk` operations both take a path through one
  normalisation: re-split each part at `/`, then drop `""` and `.`. Write it
  in std (`Path.normal`), and use it in `host_path` too. The two then agree
  on every hand-built path.
- The model refuses any path with a `..` part with `OtherError path "the
  pretend disk has no .."`, rather than treating `..` as a name. That keeps
  the model no more permissive than the host until F3's `Files.under`
  decides how `..` is handled. Update the doc lines that say "takes it as a
  name".
- Add `..` and a hand-built path to the conformance script's `PATHS`, once
  both sides agree.

### M3. The playground: `printError` vanishes, and a `Files` main gives a confusing error
`crates/web/src/project.rs:391` and `lib.rs:497` run `main` through the
machine on `wasm32-unknown-unknown`.
- `host::print_error` (`host.rs:192`) writes to `io::stderr()`. On that
  target, stderr is a sink that discards everything, so `IO.printError`
  prints nothing in the playground.
- A `{Files, IO}` main gets past `main_named`, and every operation answers
  `OtherError path "operation not supported on this platform"`. That is
  safe (there is no disk), but it is the error a user is least likely to
  understand. The paper puts the playground's in-memory disk in F2.

Fix: route `printError` through the runner's output abstraction (a second
sink, or a method on `Terminal`), so the playground can show it, styled as
an error. Until F2, refuse a `Files` main in the playground's load, with a
diagnostic like `E-JS-FILES`'s. Either can be a ticket for F2, if it's
filed now.

### M4. The tour page teaches a pattern that destroys files
`web/guide/42-files.sw:8`: `Files.read path |> .getOrElse ""` treats every
error as "missing". On `NotText` (a binary file), `NotPermitted` or
`OtherError`, `append` then writes the file again with only the new line,
throwing away what was there. Newcomers copy what the feature tour shows.

Fix: match `NotFound` only:
`match Files.read path with | Ok t => t ++ … | Err (NotFound p) => … | Err e => Err e`,
or a small `Files.readOr`-style helper in the example.

### M5. No test of the four-ability row
`MainRow::layout` (`ir.rs:619`) and the comment at `ir.rs:533-537` rely on
the elaborator ordering the row as `Plus Fail (Plus Files (Plus IO NoOp))`
("library abilities first, by name"). Every `Files` test uses
`{Files, IO}`. Nothing runs a main where both a `Fail.stop` and a `Files`
operation reach the runner.
- I checked by hand, and it works: on the machine, `--reference` and
  `--native`, a `{IO, Fail, Files, Partial}` main writes, `printError`s and
  then fails with exit 1 (scratchpad `sw3338rev/row`).
- But a change to row ordering would misroute operations silently. In the
  machine it panics with "outside the row"; in the reference runner it
  goes through `unreachable!`.

Fix: add that program to `running/files.rs` (machine, reference, native),
and to `build.rs` for the built executable. Point the comment at
`ir.rs:533` to the code in the elaborator that orders rows.

---

## Low

- **L1** `files.rs:125-128`: the clean-up after a failure removes
  `temporary` even when `create_new` failed with `AlreadyExists`, so it can
  delete a file this call didn't create. Remove it only after a successful
  open.
- **L2** Atomic replacement splits hard links: in the `sw3338rev/fifo`
  repro, `hard.txt` keeps `old`. It also drops the owner, xattrs and ACLs,
  and there is no fsync of the folder after the rename. All are inherent
  or acceptable, but syntax.md's "an existing file keeps its permissions"
  should add "(not its other hard links or its owner)".
- **L3** `files.rs:107`: the temporary file's name adds about 20 bytes to
  the target's, so a name near `NAME_MAX` fails with `OtherError` where a
  direct write would succeed. Fall back to a short name (`.sw-{pid}-{n}.tmp`).
- **L4** `files.rs:139`: names that aren't UTF-8 are converted lossily, so
  two names can list as the same, and a listed name can't be read back.
  This is documented. Consider skipping such entries, or an `OtherError`
  entry kind, at F4 (bytes).
- **L5** `IO.printError` doesn't leave keys mode, where `print` does
  (`driver/src/run.rs:296`, `rt/src/run.rs` `print_error` branch). In raw
  mode a bare `\n` gives a staircase, and it draws over a TUI frame.
- **L6** `Disk.fromList [("a", …), ("a/b", …)]` builds a disk where `a` is
  both a file and a folder. `Disk.list` then lists it twice, and `read` and
  `list` disagree about what it is. Document it, or make `fromList` drop the
  folder.
- **L7** `Files.sw:62-63`: the doc for `Path.instOrd` puts two facts in one
  sentence. "Relative before absolute" is the second key. "A folder sorts
  just before what is in it" follows from the list order, not from that.
  Split them.
- **L8** `Path.extension`: `"a."` and `".."` both give `Some ""`. Arguably
  this should be `None` for an empty extension. A small call; either way,
  say it in the doc.
- **L9** `driver/src/run.rs:253`: the E-RUN-TYPE note ends "…or
  `() -> ()`, say". Reword it: "for example `() -> {IO} ()`, …".
- **L10** Missing law: write then read. A `Disk` lemma
  `disk.write p t = Ok after → after.read p = Ok t` (and that the other
  paths are unchanged) is what a proof of a file loop needs next. File it
  as a std ticket for F3.

---

## The focus questions

### 1. Do check, test, the editor and the playground ever touch real files?
No, on every path I could find.
- A `Files` operation is performed in only two places:
  `Session::perform_files` (the reference runner) and `rt::run::perform_files`
  (the machine, native, standalone executables).
- Both are reached only from a `Main` built by `main_calls`, through
  `main_named` and `find_main`. The callers are the CLI's `run` and `build`,
  `rt_run` (an example), the bench (AoC mains) and the playground.
- The counterexample search lowers with `MainRow::IO`, and its checker term
  is pure. A `Files` operation there would panic, not perform.
- A `test` body and a constant can't have `Files` in their row: I checked
  that both are `E-ABILITY`. So neither test running nor constant folding
  can reach a host operation.
- Native compile-time evaluation: I didn't read it, but anything it could fold is a constant or test-like term, and those can't carry `Files` (above).
- The language server never builds a `Main`. The lane's LSP test covers it,
  and so does `checking_and_testing_never_touch_files`.
- The playground does run `main`, but on `wasm32-unknown-unknown`, where
  `std::fs` is unsupported. It is safe, with the poor behaviour in M3.

### 2. Host correctness (`crates/rt/src/files.rs`)
- Atomic write:
  - The temporary file is in the target's folder (after canonicalising a
    link), so it is on the same filesystem, and `create_new` refuses a
    planted symlink.
  - It is synced before the rename.
  - The problems are H1, H2, M1, L1, L2 and L3.
- UTF-8: checked once by `String::from_utf8`, and `NotText` on failure. Good.
- Listing order: sorting by Rust `String`, i.e. by byte, is code-point order
  for UTF-8. That equals `Text.compare`, which compares lexicographically
  by `Char.compare` (`CompareData.sw:161`). The host test checks `Z < a < é`.
- Error mapping:
  - `NotFound`, `PermissionDenied` and `ReadOnlyFilesystem`,
    `IsADirectory` and `NotADirectory` map to the four specific kinds, and
    the rest to `OtherError`. This is fine on toolchain 1.99.
  - The `read` fallback for hosts that open folders is sensible.

### 3. `Files.simulate` against the host
- The model is faithful on paths `Path.parse` produces without `..`. The
  conformance test agrees with that: 4 seeds × 24 operations over 8 paths,
  covering missing paths, a folder, a file inside it, a file in the middle
  of a path, a missing parent, `.`, and UTF-8 sizes.
- It doesn't cover `..`, absolute paths, trailing slashes, hand-built parts,
  `NotPermitted`, `NotText` or `Other` kinds. The last three are host-only,
  so model comparison can't cover them; the host unit tests do. The path
  cases are M2.
- The laws state what their names say:
  - `simulatePure`, `simulateRead`, `simulateList` and `simulateInfo` are
    exact.
  - `simulateWriteOk` and `simulateWriteErr` are conditioned on
    `disk.write`.
  - `simulateReadThen` runs the rest on `disk.read path` with the disk
    unchanged, which is right because a read doesn't change the disk.
  - None is vacuous; every hypothesis can be satisfied.
  - Missing law: L10.

### 4. `main`'s row as a set; the hash snapshots
- `MainRow` is now a struct of two flags. The tag is bit 0 for `Fail` and
  bit 1 for `Files`, and `from_tag` rejects values of 4 and up. The codec
  and linked format versions are bumped. The driver tries the rows smallest
  first.
- E-MAIN-TYPE and E-RUN-TYPE were reworded, and the snapshot and
  `project.rs` were updated.
- The runners agree on every row (M5 is about a missing test, not a bug).
- Snapshots:
  - Outside `prelude.snap`, every changed line in the 62 snapshots is a
    `name <64-hex>` hash line (checked by script).
  - `prelude.snap` loses only IO's hash and the hashes downstream of it
    (`IO.%elim`, `%res`, `simulate`, `simulateWith`, `readAllLines`, and
    `Terminal.toIO`, `drawFrame`, `printLines`, `scriptedHost`). It gains
    the new `Files` declarations.
  - Registering `Result`, `Ok` and `Err` as built-ins left `Result`'s hash
    unchanged.
- Should IO's hash change? Yes. `IO.printError` is a new constructor of
  `IO`, as paper §2.1 asks, so IO's hash, and every program that mentions
  `IO`, has to change. It was appended last, so the existing constructor
  indexes keep their positions.

### 5. The `%write` name clash in the JS runner
There is no live clash.
- `IoWrite` and `FilesWrite` are both `"%write"`, under different parents.
  The registry allows that (`names_are_distinct_per_kind` compares
  constructors only within one parent), and `bind_data` matches
  constructors within the type being bound.
- The JS runner's shape table uses keys written by hand (`ctor("write", io, …)`),
  not constructor names, and `Files` isn't wired into it.
- `E-JS-FILES` refuses a `Files` main before code generation
  (`driver.rs:1035`). A pure `{IO}` main that uses `Files.simulate` runs the
  same under `--js` as on the machine; I checked that by hand.
- F2 must give its keys distinct names (`filesWrite`, …). Note that in
  F2's brief.

### 6. Std names beyond the paper
These are Matt's: std names users will write.
- **Joining paths.** The paper promises `path / "Main.sw"`. The lane added
  no join at all, because `/` is fixed to numbers. Without one, users build
  `Path` records by hand, which leads into M2. Recommendation: decide before
  the formatter lane. Either a named method now (`path.child "Main.sw"`,
  short and unambiguous), with `/` later if operators become overloadable,
  or make operator overloading the dependency.
- **`Entry` and `Disk`** in the flat `Std` namespace. These are the paper's
  names, and the paper calls its names open to review. `Entry` is generic
  enough to collide with a future `Map` or `Graph` entry type.
  Recommendation: keep `Disk`, and rename `Entry` to `FolderEntry` only if
  Matt prefers. Not urgent.

These are small calls (the orchestrator's):
- `FileKind.position`, `ofPosition` and `fromPosition`, and
  `FileError.parts`, `ofParts` and `fromParts`, are plumbing for the
  hand-written `DecEq`. They are public and show in the API docs. Std has
  no private mechanism, so I'd say "internal: for `==`" in their doc lines
  (they currently have none, or a terse one). Better: a ticket for derived
  instances in std, so they can go.
- `Disk.utf8Size` is generic. It belongs in std Text as `Text.utf8Length`
  (or `byteLength`), with a lemma, and `Disk.info` should call that.
- `Disk.missing` returns a `FileError`, not a `Bool`, which its name hides.
  Call it `Disk.missingError`.
- `Disk.foldersAbove`, `blocked`, `isChild`, `isFolder` and `isFile` are
  model internals, but proofs that unfold `Disk.write` need them, so
  public is right.
- `Path.name`, `parent` and `extension` returning `Option`: fine, and
  consistent with `List.last`. Their docs say what `None` means.
- `Text.toPath` is in the paper. Fine.

### Code quality
- The code is clean, and the comments say why rather than what.
  `split_op` replacing the two hand-written decoders in `rt/src/run.rs` is
  a real simplification.
- The reference runner's `perform_files` and the machine's are close
  copies over different value representations. That is acceptable, and
  each is small.
- `ir.rs` `MainRow::ALL` and `abilities()` duplicate `layout()`'s order. A
  single `const ORDER: [Ability; 3]` would keep the three in step.
- The lane's notes (T1's join point, at `files.rs:71` and `perform_files`)
  are well placed for SW-3337.
