# File access and fast text

**Status:** proposed, 14 November 2026 (SW-3234, for D3579; replaces
SW-3150, the earlier design ticket for the same gap). Paper lane: nothing
is built. The probes were throwaway `.sw` files run with the main
checkout's release binary ([Appendix A](#appendix-a-the-probes)). It stops
for Matt's decisions ([§8](#8-questions-for-matt)).

Claims are marked **[measured]** (run for this note on Speedwell, one run
each, with the machine's load between 18 and 33, so rough), **[ran]** (a
probe that checks or runs today), **[source]** (read in the code at
`dc26a104f`) or **[estimated]** (my reasoning, not tested).

## In plain words

**The problem.** A Stitchwort program can only talk to the console. It
can't open a file, save one or list a folder, so a tool such as a formatter
has to be fed files through standard input by a script. And `Text` is slow
in exactly the ways a tool needs it to be fast. Reading every character of
a 20,000-character text by position takes 24 seconds [measured], because
each read rebuilds the text as a list. Cutting a short piece out of a text
copies the rest of it. Asking a text's length counts it again every time.
Building a text piece by piece with `++` copies everything built so far at
each step.

**The change, in two halves.**

1. *Files.* A new ability, `Files`, beside `IO`: read a file, write a file,
   list a folder, ask what a path is. Every operation returns a `Result`,
   so "no such file" is a value the program handles, not a crash. `main`
   may use `Files` as it may use `IO`. A function whose type says `{IO}`
   and not `{Files}` cannot touch the disk, and one that says `{Files}`
   cannot print. In tests, `Files.simulate` runs the same code against a
   pretend disk held in memory, and proofs are about that. Smaller
   handlers narrow what code may do: `Files.readOnly`, `Files.under
   folder`. Checking, testing and the editor never touch real files; only
   `stitchwort run` and built executables do. The playground gets the
   open project's files as its disk, in memory.
2. *Text.* No new type and no new syntax. `Text` stays, to proofs, a list
   of characters, and every theorem about it stands. Underneath, the
   runtime stores a text as a shared block of characters with a start and
   an end, so `get`, `take`, `drop`, the new `slice` and `length` take
   constant time and a slice copies nothing. `++` grows a text in place
   when nothing else holds it, as `Array.push` already does, so a loop of
   appends is the builder.

**What it should do.** A formatter's file loop becomes ordinary code:
read, format, write if changed, with a test that runs it on a pretend disk.
A lexer can hold positions and cut tokens out of the source for nothing.
Reading each character of a million-character text by position should take
about 0.3 s [estimated from today's `Array` figure, measured], where today
20,000 take 24 s. Nothing here changes the kernel, a hash, or a proof.

**How much.** About 9–12 lane hours gets the toy formatter everything it
needs (executables that start, fast text on the runtime, `Files` on the
runtime). About 8–10 more covers JavaScript, the playground, the sandbox
handlers and in-place `++` [estimated; §6].

## 1. What is there today

### 1.1 `IO` and how it reaches the host

- **`IO` is one ability with nine operations**, all about the console:
  `print`, `readLine`, `readAll`, `console`, `keysMode`, `readBytes`,
  `write`, `randomSeed`, `args` [source: `crates/elab/src/std/core/IO.sw`].
  There is no standard error, no file and no folder.
- **An ability is data.** A computation is a tree of operations, and a
  handler is a fold over it (docs/guide/08-abilities.md, "How it runs").
  The checker can evaluate a handler written in Stitchwort; it never
  performs an operation for real [source: `crates/driver/src/run.rs`, "the
  type checker never calls it"].
- **Only a runner performs `IO`,** and there are four: the reference runner
  (`crates/driver/src/run.rs`), the machine (`crates/rt/src/run.rs`, which
  `run --native`, built executables and the playground share), and the
  JavaScript runner (`crates/js/src/run.rs`). Each operation is a built-in
  constructor (`crates/core/src/registry.rs`) that each runner matches by
  hand: `randomSeed` is named in 15 files [source: `grep`].
- **`main`'s row is one of two fixed shapes,** `{IO}` or `{Fail, IO}`, with
  or without `Partial` [source: `MainRow`, `crates/rt/src/ir.rs`, named in
  12 files]. The runner needs to know the shape because an operation at run
  time is only a constructor index.
- **`Terminal` is the precedent for a library ability** (D1246):
  `Terminal.toIO` turns keys and frames into raw `IO` operations, and
  `Terminal.simulate` is its test handler [source:
  `std/Terminal/Terminal.sw`]. Its reason was that decoding keys and
  drawing frames are real code worth writing once in Stitchwort.
- **Errors stop the program.** A failed read or write is `E-IO`, exit 2
  [source: `crates/rt/src/host.rs`]. text-and-io.md said "recoverable
  errors, through `Result`-returning operations, can come later". This is
  later.
- **Handlers can wrap partial code** [ran: `Fail.toResult` round a
  `{IO, Fail, Partial}` loop recovers the failure], so a file handler can
  wrap a tool's main loop. (The guide still says otherwise; see Findings.)

### 1.2 `Text`

- **To the kernel and to proofs,** `Text` is `MkText (chars: List Char)`,
  and every operation is defined on that list [source:
  `std/core/Text.sw`]. A literal is stored compactly while checking
  (compact-text.md, stage 2).
- **At run time a text is one string:** `Value::Text(Rc<str>)`, UTF-8, in
  the machine and native code [source: `crates/rt/src/value.rs`], and a JS
  string under `--js`. Seventeen operations have native versions, tied to
  their definitions by content hash [source: `TEXT_NATIVES`,
  `crates/rt/src/natives.rs`].
- **What is slow, and why** [source: `crates/rt/src/prims.rs`]:
  - `Text.get` has no native version. It runs its definition:
    `text.toList.get index`, which builds the whole list first.
  - `Text.take` and `Text.drop` are native, but each walks to the position
    and copies the piece into a new string. SW-3150 said they "go through
    `toList`"; that is true of the definitions, not of what runs.
  - `Text.uncons` copies everything after the first character.
  - `Text.length` counts characters each time it is called.
  - `Text.append` copies both sides.

**Measured** (`stitchwort run`, minus 0.33 s to check and start; the text
is `"abcdefghij"` repeated; [Appendix A](#appendix-a-the-probes)):

| Loop, on a text of n characters | n = 100,000 | 200,000 | 400,000 | Grows |
|---|---|---|---|---|
| `text.get i` for every i | 5,000: 1.5 s; 10,000: 5.9 s; 20,000: 24.4 s | – | – | n² |
| a 5-character slice at every position (`drop i`, `take 5`) | 3.1 s | 12.4 s | 48.8 s | n² |
| `text.length`, n times | 0.5 s | 1.8 s | 6.9 s | n² |
| `acc ++ "ab"`, n times | 0.5 s | 1.7 s | 7.9 s | n² |
| `uncons` until empty | 0.4 s | 0.9 s | 2.3 s | n², a small constant |
| for comparison: `toList` once, then walk the list | 1,000,000: 0.24 s | | | n |
| `toList.toArray` once, then `array.get i` for every i | 1,000,000: 0.30 s | | | n |
| a list of n two-character pieces, joined once | 1,000,000: 1.1 s | | | n |

`run --native` gives the same shapes (`get`, 10,000: 2.8 s; the others
within 10%), since native code calls the same runtime functions. Under
`--js`, `++` and `uncons` are fast (V8 shares strings: 200,000 in 0.1 s),
slices are slower (100,000: 8.6 s), `get` is 1.2 s at 10,000, and
`length` 200,000 times on 200,000 characters did not finish in 60 s.

So today a fast program converts a text to a list or an array once and
never goes back, which is what the formatter probes did. That works, but
tokens then have to be rebuilt character by character, and nothing can
point into the source.

### 1.3 Built executables

SW-3149 (built executables fail to start from the main checkout) still
reproduces, and for plain `build` as well as `build --native` [ran: "this
executable's program can't be read: written by a different build of the
runtime"; the runtime library is from 14:28, the CLI from 15:46]. Every new
host operation changes that library, so this is fixed first.

## 2. Files

### 2.1 The ability

A sketch; names are open to review, the shape is the proposal.

```
-- std/Files/Files.sw (sketch)

type Path = { parts: List Text, absolute: Bool }

type FileKind = | File | Folder | Other
type Entry = { name: Text, kind: FileKind }
type FileInfo = { kind: FileKind, size: Nat }

type FileError =
  | NotFound (path: Path)
  | NotPermitted (path: Path) -- by the system, the runner's flags or a handler
  | NotAFile (path: Path) -- read or write of a folder
  | NotAFolder (path: Path) -- list of a file, or a file in the middle of a path
  | NotText (path: Path) -- the bytes aren't UTF-8
  | OtherError (path: Path) (message: Text) -- the host's own words

ability Files where
  read: Path → {Files} (Result Text FileError) -- the whole file, as UTF-8
  write: (Path, Text) → {Files} (Result () FileError) -- replaces the file, or creates it
  list: Path → {Files} (Result (List Entry) FileError) -- a folder's entries, sorted by name
  info: Path → {Files} (Result FileInfo FileError)

-- For tests and proofs: the same program against a disk held in memory.
def Files.simulate (disk: Disk) (prog: () → {Files | e} a): {e} (Disk, a)

-- Narrower worlds, as handlers that pass on what they allow.
def Files.readOnly (prog: () → {Files | e} a): {Files | e} a
def Files.under (folder: Path) (prog: () → {Files | e} a): {Files | e} a
```

A formatter's outer loop (a sketch, not checked; the prototype in
[Appendix A](#appendix-a-the-probes) is the checked version):

```
def formatFile (path: Path): {Files} (Result Bool FileError) := match Files.read path with
  | Err error => Err error
  | Ok source =>
    let formatted := format source
    if formatted == source then Ok False else Files.write (path, formatted) |> .map (_ => True)

def main(): {Files, IO, Fail} () :=
  let paths := IO.args().map Path.parse
  …

test "a formatted file is left alone" :=
  let (disk, changed) := Files.simulate tidyDisk (() => formatFile "a.sw".toPath)
  changed == Ok False ∧ disk == tidyDisk
```

The choices in it:

- **Whole files.** No handles, no streaming, no seek. A file is read or
  written in one operation, so there is no "forgot to close" and no state
  between operations for a proof to carry. Source files, AoC inputs and
  generated output all fit. Streaming a file too big for memory is left
  out until something needs it.
- **Text first, bytes later.** `read` gives `Text` and fails with `NotText`
  on bytes that aren't UTF-8. Reading bytes needs a compact `Bytes` type,
  which doesn't exist (`IO.readBytes` gives a `List Nat`, 24 bytes or more
  a byte at run time [source]). It is its own small design (model: a list
  of `Fin 256`; storage: one buffer, as `Array` does it), staged after the
  formatter (§6, F4). Nothing in D3579's next steps reads bytes.
- **`write` is all or nothing.** The host writes a temporary file beside
  the target and renames it over, so a formatter that crashes halfway
  never leaves a truncated source file. It creates the file if missing and
  does not create missing folders (`NotFound`).
- **`list` is sorted** by name, in `Text.compare`'s order, so the same
  folder gives the same answer on every runner and machine. The host's own
  order is arbitrary. One level only; walking a tree is library code
  (`Files.walk (maxDepth := 64) folder`), which keeps it total: a folder
  tree is finite, but the checker can't know that, so the walk counts down
  a depth.
- **Errors are values, with few kinds.** The Rust and JavaScript hosts
  each map their own error codes onto the same six constructors, and a
  test holds them to one table. `OtherError`'s message is the host's own
  wording and is left out of comparisons between runners. `FileError.show`
  gives a message for people, and `result.orFail` (existing, once the
  error is mapped to text) turns "can't read it" into `Fail` for a script
  that doesn't want to recover.
- **Paths are a small record,** not bare `Text`, so a path can't be mixed
  up with a file's contents, and the operations are methods:
  `path / "Main.sw"`, `path.parent`, `path.name`, `path.extension`,
  `Path.parse`, `path.show`. Separators are `/` on every host. They are
  pure functions on a list of parts, with lemmas, which is what makes
  `Files.under` provable (§3). Relative paths are relative to the folder
  the program was started in.
- **One argument per operation.** An ability's operation takes exactly one
  argument today, and an anonymous record type isn't accepted there [ran:
  `E-ABILITY`, `E-PARSE`], so `write` takes a pair. See Findings.
- **Left out for now:** remove, rename, create a folder (F3, small);
  modified times (there is no clock type); permissions; symbolic links as
  things in themselves (they are followed); watching for changes;
  environment variables; running other programs; the network.
- **One addition to `IO`: `IO.printError`,** a line on standard error. A
  tool that prints formatted text on standard output has nowhere to put a
  warning today. The exit code stays as it is: 1 through `Fail`, which is
  what `fmt --check` needs.

### 2.2 Where it lives: three options

| | A. More operations in `IO` | B. A library ability over raw `IO` operations (the `Terminal` pattern) | C. `Files` as a second ability the runners perform |
|---|---|---|---|
| A script reads a file with | `IO.readFile path` | `Files.toIO (() => Files.read path)`, or the raw `IO.readFile` | `Files.read path`, with `Files` in `main`'s row |
| What `{IO}` in a type means | console, files, and whatever is added next | the same: the raw operations are reachable from any `{IO}` code | the console only |
| What `{Files}` in a type means | – | files only, by convention | files only, guaranteed |
| Test handler | `IO.simulate` grows a disk | `Files.simulate` | `Files.simulate` |
| Sandbox handlers | no: they would have to handle all of `IO` | yes, for code that asks for `{Files}` | yes |
| Runner work | each operation in four runners | the same, plus a forwarding handler in std | the same, plus `main`'s row becomes a set rather than two fixed shapes |

**Recommendation: C.**

- **The type is the capability.** Stitchwort's types already say what code
  may do; C extends that to the disk with nothing to remember. A day's
  solution typed `{IO}` provably writes no file. A formatter's file loop
  typed `{Files}` provably prints nothing. Under B that is a habit, since
  the raw operations sit in `IO` for anyone to call.
- **`Terminal`'s reason doesn't apply.** `Terminal.toIO` contains real
  work (decoding keys, drawing frames). A `Files.toIO` would forward each
  operation to a raw twin and do nothing else: boilerplate that exists
  only so the runners needn't learn a second ability.
- **It is where the next host abilities go.** A clock, environment
  variables, the network or running a program will each want the same
  treatment. C makes "an ability the runner performs" a small table
  instead of a special case, and each can then be allowed or refused on
  its own. Under A, `IO` ends as one ability that means "anything".
- **Cost** [estimated]: `MainRow` (two cases, named in 12 files) becomes "which
  of `Fail` and `Files` are present, then `IO`", in the driver, the machine
  and the JS runner. That is the extra over A, about 2 hours of the F1
  lane. Counted as an end state, not as migration (D2303).

`IO.simulate` is unchanged. A test of a program that uses both nests them:
`IO.simulate input (() => Files.simulate disk prog)`.

### 2.3 The backends

| Backend | How `Files` is performed |
|---|---|
| `stitchwort run`, `run --native`, built executables | One implementation in `crates/rt/src/host.rs` over Rust's `std::fs`, shared as `IO`'s is. `read` validates UTF-8 once and hands the buffer to the text value without a second copy |
| `run --reference` | The same host functions, as today for `IO` |
| `run --js` (Node) | `fs.readFileSync`, `writeFileSync` and `renameSync`, `readdirSync`, `statSync`, in the generated runner; errors mapped from `err.code` |
| Exported JavaScript (`extract`) | Nothing. Exports stay pure: `Files` must be handled before the boundary, for example with `Files.simulate` over files the caller passes in |
| The playground (WebAssembly, no file system) | The machine's host gets a table of files in memory: the open project's files (the playground already holds them, `MemoryFiles` [source: `crates/web/src/project.rs`]), plus what the run writes. Writes are kept for the run and capped like output is (`max_output`); showing them in the page is later work. A loose file's disk is empty, so reads give `NotFound` |

All runners must agree: the existing rule that the three ways to run print
the same and fail the same (guide, chapter 11) extends to a script of file
operations on a temporary folder.

### 2.4 Security

- **Checking never touches a file.** `check`, `test`, `doc`, `search`, the
  language server and the playground's Check tab evaluate handlers as
  data and never perform an operation [source]. That stays an invariant,
  and gets a test: a project whose `main` deletes its own source is
  checked, tested and opened in the server, and the file is still there.
  So opening or checking someone else's project is safe, whatever it
  says.
- **No file access at check time, by design.** Something like "embed this
  file's text as a constant" would be useful for AoC inputs, but it makes
  a check's result depend on files the cache key doesn't cover. It is a
  separate design if wanted; this note doesn't propose it.
- **Tests can't reach the disk.** A test is a pure term; code with `Files`
  in its row has to be handled first, and the only handlers a test can
  use are in Stitchwort (`Files.simulate` and the narrowing ones).
- **Running is the user's own act.** `stitchwort run` and a built
  executable may do what the user may, as a program in any other language
  can (D3586 asks). Two flags narrow it at the host, after the real path
  is resolved, so a symbolic link can't step outside:
  `--files none` and `--files under=DIR` (and `read=DIR` for read-only).
  A refused operation gives `NotPermitted`, a value, so the program can
  say so.
- **Handlers narrow it inside a program.** `Files.under folder` rewrites
  each path to sit inside `folder` and refuses `..` that climbs out;
  `Files.readOnly` refuses writes. They are checked by the type system
  (the code inside has only `{Files}`) and provable (§3), but they compare
  paths as text, so only the host flags guard against links.
- **The playground has no real disk** to protect; its table of files is
  the sandbox. The cap on written bytes protects the page's memory.

## 3. Files and proofs

- **A pure core in a thin shell.** The interesting part of a tool is
  `format: Text → Text`, a pure function with ordinary theorems (it loses
  no token, it is idempotent). `Files` appears only in the loop round it.
  The design keeps that shell small enough to read.
- **The pretend disk is ordinary data,** a `Map Path Text` (plus folders),
  so "what the program did to the disk" is a value a test compares and a
  theorem states.
- **The handler's laws hold by computing** [ran, on a prototype with a
  list-backed disk]:

  ```
  theorem Files.simulatePure ∀ (disk: Disk) (x: a):
      Files.simulate disk (() => x) = MkPair disk x := rfl
  theorem Files.simulateRead ∀ (disk: Disk) (path: Text):
      Files.simulate disk (() => Files.read path) = MkPair disk (Disk.read disk path) := rfl
  theorem Files.simulateWrite …  := rfl
  ```

  and a statement about a real function, for every disk and every
  formatter, took one `rewrite`:

  ```
  theorem formatMissing ∀ (format: Text → Text) (disk: Disk) (path: Text)
      (missing: Disk.lookup path disk.files = None):
      Files.simulate disk (() => formatFile format path) = MkPair disk False :=
    rewrite missing in rfl
  ```

- **Narrowing handlers compose and test as expected** [ran]: `formatFile`
  under `Files.readOnly` under `Files.simulate` changes nothing on the
  disk.
- **A law about every program is harder.** "Under `readOnly` the disk
  never changes, whatever the program" states and type-checks, and its
  inductive step is the theorem itself applied to the rest of the
  program, but that direct recursion is refused (`E-TERMINATION`) because
  the rest comes from `match reify`, not from a pattern [ran]. std's
  existing route is induction on `Effect.AlwaysTree`, as
  `std/Parse/Runs.sw` does. The F3 lane should prove `readOnly`'s and
  `under`'s laws that way; the friction is a finding.
- **What a proof doesn't cover.** Proofs are about `Files.simulate`'s
  disk. The real disk can change under the program, fill up, or belong to
  someone else. What ties the two together is a conformance test: random
  scripts of operations run against a temporary folder and against the
  model must give the same replies, on each runner. The host code is
  trusted to that extent, as the text natives are trusted against their
  definitions.

## 4. Text

### 4.1 What is added

No new type. In `std/Text`, each defined on `toList` with its lemmas, as
the rest of `Text` is:

| | Definition (the spec) | Lemmas to ship |
|---|---|---|
| `Text.slice (text) (from to: Nat): Text` | `text.drop from \|> .take (to - from)` | `sliceToList`; `lengthSlice` (`from ≤ to ≤ length` gives `to - from`); `sliceAppend`: `from ≤ mid ≤ to` gives `slice from mid ++ slice mid to = slice from to`; `sliceAll` |
| `Text.get` (exists) | `text.toList.get index` | `getToList` (exists); `getSlice` |
| `Text.getOr`, `Text.getLt` | as `Array`'s: a fallback, or a proof the index is in range | as `Array`'s |
| `Text.skipWhile (text) (from: Nat) (test: Char → Bool): Nat` | the first position at or after `from` whose character fails the test, or the length | `from ≤ skipWhile … ≤ length`; every character between passes |
| `Text.concat (texts: List Text): Text` | `joinWith ""` | `concatToList` |

`sliceAppend` is the lexer's theorem in miniature: tokens cut at
increasing positions, joined, give back the source. `skipWhile` is there
so a lexer's inner loop is one native call, not a closure call per
character; it goes in only if the T1 lane's measurements want it.

A lexer can then be written either way, and both are cheap:

- structurally on `text.toList`, counting positions, with each token cut
  out at the end as `source.slice start end` (no characters rebuilt); or
- over positions, `source.get pos`, with `decreasing source.length - pos`.

### 4.2 The representation at run time

**Today:** one reference-counted UTF-8 string per text. Positions are in
characters, so finding position `i` means walking from the start, and a
piece of a text has to be a copy.

**Proposed:** a text value is a reference to a shared buffer plus a start
and a length, counted in characters. The buffer stores every character at
one fixed width, chosen when it is made from its largest character: 1
byte (all below U+0100), 2 bytes (all below U+10000) or 4. This is
Python's string layout (PEP 393).

- `get`, `slice`, `take`, `drop`, `uncons` and `length` are arithmetic on
  the start and length: constant time, no allocation, no copy.
- Positions in the buffer are the positions the spec talks about (indexes
  into `List Char`), so the trusted native code is bounds arithmetic that
  mirrors the definitions line for line.
- A buffer pointer and two 32-bit numbers fit where `Rc<str>`'s pointer
  and length are now, so a `Value` stays three words [source: `value.rs`].
  That caps one text at 4 billion characters.
- Stitchwort source is not ASCII (`→`, `∀`, `λ`), so the formatter's own
  inputs would use 2 bytes a character: at most 13 MB for the 6.5 MB of the
  repo,
  against about 500 bytes of heap per input byte for the rest of a
  formatter (self-hosted-fmt.md §5). Memory is not the constraint.
- Reading a file decodes UTF-8 into the buffer and writing encodes it:
  one pass each way, which `read` needs anyway to validate.

**The alternative considered:** keep UTF-8 and add to each buffer an
"all ASCII" flag plus, for other texts, an index from character positions
to byte offsets built on first use. It is more compact and needs no
transcoding, but the indexed path is more trusted code, and it is the
path Stitchwort's own source takes. A third, four bytes a character
always (what the checker's compact literals use), is the simplest and
costs four times the memory for ASCII. All three give the same results,
so the choice between them is an implementation call for the T1 lane,
made with measurements and logged in the performance log (D3447, D3444).
I'd start with the fixed-width layout.

**Slices keep their buffer alive.** A 3-character token cut from a 1 MB
source holds the megabyte until the token goes. For a formatter that is
what's wanted (the tokens live as long as the file's work). A program that
keeps one short piece of a huge text for a long time pays for it; the fix
is the checker's own rule for compact literals: a native that makes a
slice shorter than some fraction of a large buffer copies it. The lane
picks the threshold by measuring.

**The builder is `++`.** `Text.append` on a text that nothing else holds,
and that ends where its buffer's contents end, writes into the buffer's
spare room and returns the same buffer, growing it by doubling: what
`Array.push` does today [source: `Array.sw`, "change the buffer in place
when nothing else holds the array"]. A loop of `acc ++ piece` becomes
linear with no new API and nothing new to prove, because the meaning is
still `Text.append`. When something else does hold the text, it copies,
as now. `stitchwort run` already counts and reports array copies; text
copies in a long append loop get the same line. `joinWith` and `concat`
stay the one-shot way (a million pieces in 1.1 s today [measured]).

A separate builder type or a rope was considered and not proposed: either
is a second text type with its own spec, its own lemmas and conversions at
every boundary, to get what in-place `++` gives the type people already
use. JavaScript engines already store `++` as a rope [measured: 200,000
appends in 0.1 s].

### 4.3 The other backends

- **The checker and the reference runner: no change.** They run the
  definitions, so `Text.slice` there costs what `take` and `drop` cost
  today. Proofs by `rfl` on literals keep working through compact
  literals. Native text operations in the checker remain
  compact-text.md's stage 3, with its own decision.
- **Tests** run on the fast runtime by default, so they get the fast text.
- **JavaScript** keeps a `Text` as a JS string (the export boundary
  depends on it). A JS string is indexed by UTF-16 unit, which is the
  character position exactly when the text has nothing above U+FFFF. The
  natives for `get`, `slice`, `take`, `drop` and `length` use that fast
  path, remembering for the last text checked whether it qualifies, and
  walk otherwise. So `--js` is constant-time on ordinary text and correct
  on all of it. Staged after the runtime (T3), measured before promising
  more.

### 4.4 How it is specified and tested

Exactly as the existing text natives are: each native is tied to its
definition's content hash, a changed definition falls back to running as
written, and a test fails until the native is re-checked. The tests follow
compact-text.md's three tiers: every text of up to 3 or 4 characters over
an awkward alphabet (one from each width class, a combining accent, the
ends of the surrogate gap, U+10FFFF) with every pair of positions,
compared with the definition; medium random texts and slices of slices;
and a million characters for the complexity claims, with a time bound
loose enough not to flake. The checks that matter most for the new
layout: slices of slices, appends that cross a width boundary (a
1-byte buffer meeting `→`), in-place append when the text is and isn't
shared, equality and comparison across widths, and the round trip
through a file.

## 5. Calls I made

Each is reversible and inside the design; say if any should be a
question.

- Whole-file operations only; no handles or streaming.
- Text files only in the first stages; bytes with a `Bytes` type later.
- `write` replaces a file atomically and doesn't create folders.
- `list` is sorted and one level deep; walking is library code with a
  depth limit.
- `Path` is a record, with `/` as the separator on every host.
- No file access at check time.
- No builder or rope type; `++` in place is the builder.
- Text positions stay counted in characters (scalar values), as `length`
  is today; no byte offsets in the API.
- The buffer layout (fixed width, or UTF-8 with an index) is the T1
  lane's call by measurement.
- `IO.printError` is added; exit codes are not.

## 6. Staging

Lane hours are estimates. "Opus" follows D2506: the runtime's value
layout, natives bound to std core, and the runners' handling of `main`
are core changes.

| Stage | What | Model | Hours |
|---|---|---|---|
| S0 | SW-3149 (built executables fail to start): rebuild or check the runtime library with the CLI | Sonnet | 1 |
| T1 | The text value becomes a shared buffer with a start and length; `get`, `take`, `drop`, `uncons`, `length` constant-time; `Text.slice`, `getOr`, `getLt`, `concat` in std with lemmas; native code's view of a text (`native_abi.rs` reads the length at a fixed offset [source]); the three test tiers; a performance-log entry | Opus | 5–6 |
| F1 | `Files` with `read`, `write`, `list`, `info`; `Path`, `FileError`; `main`'s row as a set; the machine, native, built executables and the reference runner; `Files.simulate` and its laws; `IO.printError`; guide chapter 8 and `docs/syntax.md` | Opus | 4–5 |
| — | **The toy-language formatter can start here** (S0, T1, F1: 10–12 hours) | | |
| T2 | `++` in place when unshared, with the copy counter; `Text.skipWhile` if T1's numbers want it | Sonnet | 2–3 |
| F2 | `run --js` (Node) and the playground's in-memory files; the runners-agree test extended to file scripts | Sonnet | 3 |
| F3 | `Files.readOnly`, `Files.under` with their laws (by `AlwaysTree`), `Files.walk`; remove, rename, create folder; the `--files` flags | Sonnet, Opus review of the flags | 3 |
| T3 | JavaScript natives for `get`, `slice`, `length` | Sonnet | 2 |
| F4 | `Bytes`: a short design, then `readBytes`/`writeBytes` and UTF-8 decoding with its round-trip theorem | Opus design 1, Sonnet 3 | 4 |

T1 and F1 touch different files except `crates/rt/src/host.rs` and the
wire format's version, so they can run side by side. T1 first if only one
runs: F1's `read` should hand its buffer straight to the new text value.

**What the toy formatter exercises, and how it is tested.** It is the
first real user of both halves, so its tests are the design's acceptance
tests:

- its lexer cuts tokens with `slice`, and a theorem (or at least a
  property test) says the tokens joined give back the source;
- its file loop is `{Files}`-typed and tested under `Files.simulate`:
  rewrites what needs it, leaves a formatted file alone (and doesn't
  write it), reports a missing file as a value;
- one end-to-end test runs the built executable on a temporary folder
  and compares the folder afterwards, on the machine and native;
- a timing: a 1 MB input lexed by position, against today's
  list-based 0.11 s [measured, self-hosted-fmt.md], to confirm slices
  cost nothing rather than assume it.

**Tests for the stages themselves:** T1 as in §4.4. F1: each operation and
each error kind on a temporary folder (missing, a folder where a file is
wanted, not UTF-8, no permission); atomic write (the target is whole or
untouched when the write is interrupted); sorted listing; the invariant
test that checking and testing a file-deleting `main` deletes nothing; the
model-conformance test of §3; `Files.simulate`'s laws as theorems in std.

## 7. What it doesn't do

- It doesn't make the checker's own text fast (compact-text.md stage 3).
- It doesn't add text patterns (`| "def" => …`) or let `Std.Parse` read
  tokens; both are in SW-3228's findings (the formatter plan) and the
  generic-parse design (D3579's other paper lane).
- No clock, environment, network or subprocess; C makes room for them.
- No streaming, so a file larger than memory can't be processed.
- No promise about `--js` speed on text with characters above U+FFFF.

## 8. Questions for Matt

**D3585: is `Files` its own ability that `main` may use, beside `IO`?**
*The problem:* file access has to live somewhere. Put in `IO`, every
`{IO}` function may touch the disk, and `IO` turns into "anything at
all" as clocks and networks follow.
*The change:* a second ability the runners perform, `Files`; `main` may
have `{Files, IO}`. It costs about 2 hours more than adding to `IO`
[estimated], for letting `main`'s row be a set.
*What it should do:* a type says whether code can reach the disk;
`Files.simulate`, `Files.readOnly` and `Files.under` test and confine
file code without touching console code; later host abilities follow the
same pattern. **[rec: yes; option C of §2.2]**

**D3586: may a program you run read and write any file you can, by
default?**
*The problem:* once `Files` exists, `stitchwort run prog.sw` can change
files. Checking, testing and the editor never will (§2.4), but running
does.
*The change:* allowed by default for `run` and built executables, as in
every mainstream language, with `--files none`, `--files under=DIR` and
`--files read=DIR` to narrow it. The alternative is Deno's: refused
unless a flag allows it, so every AoC run and every tool carries a flag.
*What it should do:* tools and scripts work with no ceremony; running
someone else's program can be boxed in with one flag; checking it is
always safe. **[rec: yes, allowed by default]**

**D3587: build S0, T1 and F1 next, then the toy formatter?**
*The problem:* D3579 asked for the foundation before the formatter. This
note has eight stages; the formatter needs three.
*The change:* SW-3149's fix (Sonnet, 1 h), fast text on the runtime
(Opus, 5–6 h) and `Files` on the runtime (Opus, 4–5 h), the last two side
by side; the rest (JavaScript, playground, sandbox handlers, in-place
`++`, bytes) queued behind, not blocking.
*What it should do:* in about 10–12 lane hours a Stitchwort program can
read, slice and write real files at linear cost, and the toy formatter
starts on the real thing rather than on standard input. **[rec: yes]**

## Findings worth tickets

- **SW-3149 (built executables fail to start) also breaks plain `build`,**
  not only `build --native` [ran]: "this executable's program can't be
  read: written by a different build of the runtime". Stage S0.
- **`Text.get` has no native version** while `take` and `drop` do: 1.2 ms
  a read on a 20,000-character text [measured]. T1 fixes it; if T1 is
  delayed, a native `get` on today's string is a one-hour win.
- **`Text.length` counts every time** on every runner, and under `--js` a
  loop calling it 200,000 times on 200,000 characters did not finish in
  60 s [measured]. T1 and T3.
- **`Text.uncons` and `Text.drop` copy the rest of the text,** so peeling
  a text character by character is quadratic [source, measured: 2.3 s at
  400,000]. T1.
- **The guide is out of date on handlers and partial code.**
  docs/guide/08-abilities.md says "a handler still can't go around partial
  code, so `Fail.toResult` can't catch a failure from inside `sumLines`";
  it can [ran].
- **An ability's operation takes exactly one argument,** and an anonymous
  record type isn't accepted as that argument: `write: Path → Text →
  {Files} …` is `E-ABILITY`, and `write: { path: Text, contents: Text } →
  …` is `E-PARSE` with a message about record updates ("expected `|` and
  the fields to update") [ran]. Worth a design ticket for operations of
  several arguments, and a better message for the second meanwhile.
- **Induction over a program isn't seen as terminating.** A theorem about
  every computation (`∀ prog`, by `match reify prog`) can't call itself
  on the rest of the program: `E-TERMINATION`, though the goal it would
  close is exactly its own statement [ran]. The `AlwaysTree` route works
  but is indirect. Worth a look by whoever owns the effects proof
  tooling, and a paragraph in the proving guide either way.
- **`IO` has no standard error.** A tool can't print a warning apart from
  its output. `IO.printError` is in F1.
- **There is no `Bytes` type;** `IO.readBytes` gives a `List Nat`. F4.
- **Slices under `--js` are slower than on the machine** (100,000
  five-character slices: 8.6 s against 3.1 s) [measured], the opposite of
  the usual order. T3.
- **Hand-matched host operations.** Each `IO` operation is matched by hand
  in four runners and named in about 15 files [source]. F1's lane should
  say whether a table of host operations, shared by the Rust runners,
  would shrink that; if so, a follow-up ticket.

## Appendix A: the probes

In the lane's scratchpad; not committed. Run with the main checkout's
release binary (built 15:46 on 14 November), each mode once, with
`timeout`, while other lanes were building (load 18–33).

- **`probe.sw`** (70 lines): `main` reads a mode and a size from
  `IO.args`, makes the text with `Text.repeat "abcdefghij" (n / 10)`, and
  runs one `@[tailrec]` loop: `get` (sum of the code points read with
  `text.get i`), `slice` (`text.drop i |> .take 5 |> .length` at each
  `i`), `uncons`, `length`, `append` (`acc ++ "ab"`), `join` (a list of
  pieces, `joinWith ""`), `list` (walk `text.toList`) and `array`
  (`text.toList.toArray`, then `get i`). Mode `none` builds the text and
  prints its length: 0.33–0.40 s, which is the start-up subtracted in
  §1.2. It checked first time.
- **`files.sw`** (95 lines): a `Files` ability with `read` and `write`, a
  list-backed `Disk`, `Files.simulate`, a host handler with the host
  operations passed in as functions (the shape of option B's `toIO`),
  `Files.readOnly`, a stand-in `formatFile`, four tests (all pass), the
  three handler laws and `formatMissing` (all check), and
  `readOnlyKeepsDisk`, whose statement checks and whose recursion is
  refused.
- **`part.sw`**: `Fail.toResult` round a `{IO, Fail, Partial}` loop, fed
  `1`, `2`, `x`: prints "recovered: expected a whole number, got 'x'".
- **`hello.sw`**: built with `build` and `build --native`; neither
  executable starts (SW-3149).
