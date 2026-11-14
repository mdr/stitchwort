# How fine should abilities be? Files, `IO`, and a name for "everything"

**Status:** design note, 14 November 2026 (SW-3262, after Matt's question
on SW-3234's file design). Paper lane: nothing is built. The probes were
throwaway `.sw` files run with the main checkout's release binary
([Appendix A](#appendix-a-the-probes)). It stops for Matt's decisions
([§8](#8-questions-for-matt)).

Claims are marked **[ran]** (a probe that checks or runs today),
**[measured]** (counted for this note), **[source]** (read in Stitchwort's
code at `f13f1b301`), **[cited]** (read in the named language's own source,
docs or paper for this note; links in [§2](#2-what-other-languages-do)) or
**[estimated]** (my reasoning, not tested).

## In plain words

**The problem.** File access has to live somewhere. The file design
(file-io-and-text.md, D3585) put it in a new ability, `Files`, beside `IO`.
That was a surprise: in most languages `IO` means "anything that touches
the outside world", and here `{IO}` would mean "the console, but not
files". The question is which is right for Stitchwort, and whether Koka's
arrangement (small separate effects, plus `io` as one word for all of them)
gives both.

**What I found.** Languages split into two groups, and the split explains
the surprise.

- Where `IO` is a built-in that programs can't take apart (Haskell, Lean,
  Idris, Roc, Unison's `IO`), it is one big thing. Nothing is lost by its
  size, because nobody writes a handler for it or proves anything through
  it.
- Where effects are things a program can handle (Flix, Unison Cloud's
  abilities, Haskell's effect libraries, Idris's `App`), designers split
  the outside world into parts, file access among them. Koka splits it
  too, and adds `io` as one word for the bundle.

Stitchwort is firmly in the second group, more so than any of them: an
ability here is what a test replaces and what a proof is about. A handler
must answer every operation of the ability it handles, and so must a proof
that takes a program apart [ran]. So the size of an ability is a cost paid
by every handler and proof that touches it. One big `IO` would mean a
pretend disk in every console test's world, and every handler anyone has
written for `IO` breaking each time `IO` learns a new trick.

**The change.** Three parts.

1. *Keep `Files` separate* (D3585's answer stands), with a rule for the
   abilities that follow: one ability for each part of the outside world
   that has its own pretend version for tests (the console, the disk, the
   clock, the network), and no finer. "Read-only" and "only this folder"
   are handlers, not more abilities.
2. *Add names for sets of abilities,* a small language feature:
   `ability IO = {Console, Files}`. A name is replaced by its members
   where a row is read. The kernel, hashes and proofs never see it.
3. *Make `IO` that name:* everything the runner can perform. Today's
   console ability becomes `Console`. Then `{IO}` means what it means
   everywhere else, a script's `main` says `{IO}` however many host
   abilities exist, and a function that says `{Files}` or `{Console}` is
   making a narrower, checked promise.

**What it should do.** `main(): {IO} ()` can read a file, as Matt expected.
A formatter's file loop says `{Files}` and is tested against a pretend
disk with no console in sight; a day's `{Console}` solution provably
writes no file. Adding a clock later breaks no existing handler and no
proof. Part 1 costs nothing beyond the file design's own lane. Parts 2 and
3 are about 8–10 lane hours [estimated; §7] and do not block the formatter.

**What it doesn't do.** It doesn't make ability names into security: a
program you run can still do what its `main` says. The file design's host
flags (`--files under=DIR`) remain the guard against a program you don't
trust.

## 1. What Stitchwort has, and what follows from it

Five facts about abilities here decide most of the question.

1. **An ability is the unit of handling.** A handler names one ability and
   must have a clause for each of its operations: a handler for `IO` with
   only a `print` clause is refused, "this handler has no clause for
   `readLine`" [ran: `E-HANDLER`, `p2.sw`]. There is no way to handle part
   of an ability and pass the rest on, other than writing a clause for each
   operation that performs it again.
2. **It is the unit of proof too.** `match reify`, the way a theorem takes a
   program apart, needs a clause for every operation of the row: on an
   `{IO}` program with only a `print` clause it lists the eight it is
   missing [ran: `E-NONEXHAUSTIVE`, `p3.sw`].
3. **A row is a set.** `{Files, IO}` and `{IO, Files}` are the same type:
   the elaborator sorts a row's abilities by name, the library's first, and
   refuses a repeat [source: `effect_type`, `crates/elab/src/effects.rs`].
   There is at most one row variable, `{Files | e}`.
4. **Smaller rows fit into larger ones without ceremony.** An `{IO}`
   function is called from `{Files, IO}` code, passed where a
   `{Files, IO}` callback is wanted, and run under a `{Files | e}` handler
   that it never uses, with no annotation [ran: `p7.sw`]. So "subsumption"
   is already there; nothing new is needed for a narrow function to be
   used in a wide place.
5. **Rows are written, not inferred.** Every `def` states its row. In Koka
   effects are inferred and a signature is optional [cited], so a long row
   costs a Koka programmer nothing until they choose to write it. Here
   every function on the path from `main` to a file read says `Files`.

And three about what is there today:

- **Rows are short** [measured: `grep` over `aoc/`, `games/`, std and
  `examples/`]: of 1,688 written rows, 1,513 name one ability, 167 two,
  and 8 three or four.
- **`IO` is already a mixture.** Seven of its nine operations are the
  console; `randomSeed` is the host's entropy and `args` is the command
  line [source: `std/core/IO.sw`]. The cost shows in std's two `IO`
  handlers: `Terminal.scriptedHost`, a pretend terminal, has to say what
  `randomSeed` and `args` give [source: `std/Terminal/Terminal.sw`].
- **`main`'s row is one of two fixed shapes** [source: `MainRow`,
  `crates/rt/src/ir.rs`], and anything else is `E-MAIN-TYPE` [ran:
  `p6.sw`]. The file design's F1 lane already replaces that with "a set of
  the abilities the runner performs".

**What follows.** Fact 1 means that adding an operation to an ability
breaks every handler of it, and fact 2 every proof that takes such a
program apart. With one `IO` that grows (files now; a clock, environment
variables and the network later), each addition breaks them all. With
separate abilities, adding `Clock` breaks nothing. This is the argument
the file design didn't make, and I think it is the strongest one.

Fact 5 is the argument the other way. Written rows grow along the whole
call path, and a helper that gains `Clock` forces an edit to each caller's
row up to `main`. That cost is real, it is what Haskell programmers call
the complaint behind Roc's return to plain "effectful" [cited], and it is why a bundle name matters more here than in Koka.

## 2. What other languages do

Read for this note on 14 November 2026. Signatures and quotes are from the
linked source files or documents, fetched and searched directly, unless
marked *(as reported)*: those came through a summarising fetch, so the
wording may not be exact and they are paraphrased here. "Not found" means
I looked and didn't find it, not that it doesn't exist.

### 2.1 Koka

- **The grain is fine, and the bundle is a type alias.** From
  [`lib/std/core.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/core.kk):

  ```
  pub type net :: X    // "signifies a function may access the network"
  pub type fsys :: X   // "signifies a function may access the file system"
  pub type ui :: X
  pub type blocking :: X
  pub alias pure = <exn,div>
  pub alias ioc-total = <ndet,console,net,fsys,ui,st<global>>
  pub alias ioc = <div,ioc-total>
  pub alias io = <exn,ioc>
  ```

- **The library's own signatures are exact:**
  `read-text-file(path): <fsys,exn> string`,
  `list-directory(dir): <fsys,exn> list<path>`, `is-file(path): fsys bool`
  ([`std/os/file.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/os/file.kk),
  `dir.kk`); `println(s): console ()`; `readline(): <console,exn> string`.
  The environment, the arguments and the clock are `ndet`:
  `get-args(): ndet list<string>`, `now(): <ndet,utc> instant`. Where it
  would be a long list it says `io`: `run-system(cmd): io int`
  (`std/os/process.kk`).
- **These effects are labels, not handlers.** `fsys`, `net`, `console`
  and `ui` are bare type constants (`:: X`) with no operations, so a Koka
  program can't handle `fsys` and there is no pretend file system. The
  console is redirected for tests through a global mutable reference
  (`print-redirect` in `std/core/console.kk`), not a handler. Compare
  `random`, a real `effect` with a default handler and a pure one
  (`pseudo-random(seed, action: () -> <random|e> a): e a`,
  `std/num/random.kk`).
- **Effects are inferred.** The
  [book](https://koka-lang.github.io/koka/doc/book.html) (§3.2): "A novel
  part about Koka is that it automatically infers all the side effects
  that occur in a function", and "The 'worst' effect is `io` and means
  that a program can raise exceptions, not terminate, be
  non-deterministic, read and write to the heap, and do any input/output
  operations." Its examples annotate with `console` where they print and
  `io` in the specification chapter.
- **What I didn't find:** any statement by Daan Leijen on why this grain,
  or an issue asking for coarser or finer.

So Koka's design is: fine labels for documentation, exact in the library,
inferred in user code, with `io` as the word for "all of it". It is not a
model for testing, because the labels can't be handled.

### 2.2 The rest, by what they chose

**One `IO` that programs can't take apart.**

- **Haskell.** `IO` is one type. Splitting is done in libraries: classes
  such as `MonadFileSystem` for test mocks
  ([Alexis King, 2017](https://lexi-lambda.github.io/blog/2017/06/29/unit-testing-effectful-haskell-with-monad-mock/)),
  with a known cost in boilerplate
  ([Matt Parsons, 2018](https://www.parsonsmatt.org/2018/03/22/three_layer_haskell_cake.html),
  *as reported*).
- **Lean 4.** `BaseIO`, `EIO ε` and `IO := EIO Error` differ only in the
  error type; `readFile (fname : FilePath) : IO String`
  ([`Init/System/IO.lean`](https://github.com/leanprover/lean4/blob/master/src/Init/System/IO.lean)).
- **Idris 2.** One `IO` and a `HasIO` interface;
  `readFile : HasIO io => String -> io (Either FileError String)`.
- **Agda, F\*.** `IO`, and `ML` (F\*'s effects order divergence, state and
  exceptions, not kinds of input and output).
- **Roc.** Types say only pure (`->`) or effectful (`=>`, names ending
  `!`); which operations exist is the platform's choice, so a browser
  platform has no file operations at all
  ([platforms](https://www.roc-lang.org/platforms)). Roc tried finer and
  went back. Richard Feldman, in the
  [purity inference proposal](https://docs.google.com/document/d/1siZalWbCI8dkW5wWRg_0KOXqiPMofkbwy0KdfQzp1H4/):
  "We experimented with granular effect tracking in the past: a version of
  Task which had a third type parameter, namely a tag union describing the
  various effects the task would perform", and "The conclusion based on
  that experiment was that the normal two-parameter Task was nicer in
  practice", because passing the operations in as module parameters gives
  real sandboxing and doesn't "balloon function signatures". The same
  document says Roc's effects have no handlers. Testing effectful code was
  still an open gap in January 2025 (Roc's Zulip, *as reported*).
- **Unison's `IO`.** One built-in ability for files, sockets and the clock,
  paired with `Exception`:
  `readFileUtf8 : FilePath ->{IO, Exception} Text`,
  `Instant.now : '{IO, Exception} Instant`
  ([base](https://share.unison-lang.org/@unison/base)). It is the only
  ability whose handler is the runtime
  ([docs](https://www.unison-lang.org/docs/fundamentals/abilities/using-abilities-pt2/),
  *as reported*).

**Fine abilities that a handler turns into a raw `IO` underneath** (the
file design's option B).

- **Unison, in practice.** base has `Clock` and `Random` abilities, each
  with a real handler into `IO` and a pure one for tests:
  `Clock.runClock : (a ->{g, Clock} b) -> a ->{g, IO, Exception} b` and
  `Clock.test : '{g, Clock} t ->{g} t`. The docs recommend the pattern:
  "write a handler that interprets the Cache ability into the IO ability"
  ([FAQ](https://www.unison-lang.org/docs/fundamentals/abilities/faqs/)).
  Whether base has a file ability: not checked. Named sets of abilities:
  not found.
- **Unison Cloud** goes all the way: user code gets about a dozen
  abilities and no `IO`. `Cloud.submit` takes a
  `'{Config, Exception, Http, Blobs, Services, Storage, Remote,
  HttpWebSocket, WebSockets, Random, Log, Scratch} a`
  ([cloud](https://share.unison-lang.org/@unison/cloud)), and
  `Cloud.main.local` runs the same code on one machine. That twelve-item
  row is what a signature looks like with no name for the bundle.
- **Flix** is the furthest along this road, and recent. `IO` remains as a
  primitive: "primitive effects cannot be handled and never go out of
  scope"
  ([book, primitive effects](https://github.com/flix/book/blob/master/src/primitive-effects.md)).
  Above it, library effects with default handlers that `main` may use:
  `Console`, `Clock`, `Env`, `Http`, `Process` and, since March 2026, a
  file hierarchy: `FileSystem` containing `FileRead`, `FileWrite`,
  `FileStat`, `DirList`, `Glob`, and below them single-operation effects
  such as `ReadFile`
  ([book, file system](https://github.com/flix/book/blob/master/src/filesystem.md)).
  So read and write are separate: `def main(): Unit \ { FileRead,
  FileWrite, IO }`. Narrowing to a folder or to read-only is done by
  handlers (`withChroot`, `withReadOnly`), not types. The book's reason is
  style and supply-chain safety: giving every function `IO` "is not
  effect-oriented programming", and "`IO` effect should be _close_ to the
  `main` function"
  ([effect-oriented programming](https://github.com/flix/book/blob/master/src/effect-oriented-programming.md)).
  There is no declaration for a set of effects (a `type alias` can name
  one). A statement of why this fine: not found.
- **Haskell's effect libraries.** `effectful` ships a `FileSystem` effect
  (`readFile :: FileSystem :> es => FilePath -> Eff es ByteString`) whose
  handler needs the raw `IOE`. It can't be given a pure meaning (it is a
  static effect), so it marks permission only. Of `IOE` its source says:
  "it is not recommended to use this effect in application code as it is
  too liberal. Ideally, this is only used in handlers of more fine-grained
  effects"
  ([`Effectful/Internal/Monad.hs`](https://github.com/haskell-effectful/effectful/blob/master/effectful-core/src/Effectful/Internal/Monad.hs)).
  polysemy, fused-effects and cleff ship no file effect; their standard
  example is a user-defined `Teletype` with a pure handler for tests.
  Bluefin has no file effect either: `withFile` takes the `IOE` handle.
- **Idris 2's `Control.App`.** `Console` and `FileIO` interfaces over one
  `PrimIO`: `readFile : FileIO e => String -> App e String`,
  `Has [Console, State Counter Int] es => App es ()`
  ([`Control/App/FileIO.idr`](https://github.com/idris-lang/Idris2/blob/main/libs/base/Control/App/FileIO.idr)).
  Idris 1's `Effects` library had `FILE` and `STDIO`; it is not in Idris
  2's base.
- **Effekt.** Real input and output is one built-in resource, `io`,
  tracked beside the type and not as an effect:
  `def helloWorld() at {io} = println("hello, world")`
  ([tour](https://effekt-lang.org/tour/captures)). File functions carry
  only their error: `readFile(path: String): String / Exception[IOError]`.
  A handleable `interface Files` with `readFile` and `writeFile` together
  is offered as well
  ([`io/filesystem.effekt`](https://github.com/effekt-lang/effekt/blob/master/libraries/common/io/filesystem.effekt)).
  It has names for effect sets: `effect Bar = { Foo, Foo }`
  ([`effectalias.effekt`](https://github.com/effekt-lang/effekt/blob/master/examples/pos/effectalias.effekt)).

**Research languages.** Frank's built-in interfaces are `Console` and
`RefState`; Eff has an effect for each primitive (`Print`, `Read`,
`Write`, `RandomInt`); Links tracks one effect, `wild`, for everything
that can't run in the database. None has a file design to learn from.

**No effect types; the right to touch files is a value.**

- **OCaml 5 with Eio.** Effects aren't in types: "effect handlers in OCaml
  do not provide effect safety"
  ([manual](https://ocaml.org/manual/5.3/effects.html)). Eio passes
  capabilities from `main`'s `env`: `fs` is the whole file system, "`cwd`
  restricts access to files beneath the current working directory", and
  `open_subtree` narrows further. "Because external resources are provided
  to `main` as arguments, we can easily replace them with mocks for
  testing." The admitted limit: "Since OCaml is not a capability language,
  code can ignore Eio and use the non-capability APIs directly"
  ([README](https://github.com/ocaml-multicore/eio/blob/main/README.md)).
  There is no read-only folder and no mock file system in its mock
  library. Thomas Leonard's
  [case for it](https://roscidus.com/blog/blog/2023/04/26/lambda-capabilities/)
  says threading values is less trouble than feared, and that defaults
  (a TLS library's certificate folder) are the awkward case (*as
  reported*).
- **Pony** (`AmbientAuth` → `FileAuth` → `FilePath` with flags such as
  `FileRead`), **Austral** (linear `Filesystem` and `Path` values;
  [spec](https://austral-lang.org/spec/spec.html)), **E** (file objects
  held by reference), **WASI** (a program gets
  [preopened folders](https://github.com/WebAssembly/wasi-filesystem) and
  opens paths relative to them) and Rust's cap-std. All split read from
  write, and all narrow to a folder. Pony's docs note that its narrowing
  is textual and doesn't resolve links (*as reported*). **Deno** does the
  same at run time, with flags for a whole process.

### 2.3 What the survey says

| Language | Grain for the outside world | Files separate? | Can a program give files a pretend meaning? | One word for all of it |
|---|---|---|---|---|
| Koka | labels: `console`, `fsys`, `net`, `ui`, `ndet` | yes | no (labels can't be handled) | `io`, an alias |
| Flix | library effects over a primitive `IO` | yes, and read apart from write | yes, by handler | `IO` (the primitive underneath) |
| Unison base | one `IO`; `Clock`, `Random` beside it | no | no; yes for `Clock`, `Random` | `IO` |
| Unison Cloud | about twelve abilities, no `IO` | storage abilities instead | a local handler | none; rows of twelve |
| Haskell | one `IO` | in libraries (`effectful`: yes, as a marker) | only with a user-defined effect or class | `IO` |
| Idris 2 | one `IO`; `Control.App` has `Console`, `FileIO` | in `App`, yes | in principle (another instance) | `IO`, `PrimIO` |
| Lean 4, Agda, F\* | one `IO` (`ML`) | no | no | `IO` |
| Roc | pure or effectful; the platform chooses the operations | no (tried finer, went back) | planned through module parameters | `=>` |
| Effekt | one `io` resource; optional `Files` interface | optional | yes, the interface | `io`; and `effect X = {…}` |
| Frank, Eff, Links | console only, or one effect | no | – | – |
| OCaml 5 + Eio | values: `fs`, `cwd`, `net`, `clock` | yes | by passing a mock (none shipped for files) | `env` |
| Pony, Austral, E, WASI | values, narrowed by folder and by right | yes, read apart from write | – | a root authority |

Four things stand out.

1. **One `IO` is what a language has when `IO` is a given.** In Haskell,
   Lean, Idris, Roc and Unison's base, no program handles `IO`, so its
   size costs nothing and splitting it needs machinery. That is where the
   expectation "files are part of `IO`" comes from.
2. **Where effects can be handled, the outside world gets split,** and
   file access is one of the parts: Flix, Unison Cloud, `effectful`,
   Idris's `App`, Effekt's `Files`. The stated reasons are the file
   design's: tests, and types that say what code touches.
3. **Nearly all of them keep a raw `IO` underneath** and then warn people
   off it (Flix: keep it close to `main`; `effectful`: "too liberal").
   They need it because any foreign function could do anything. Stitchwort
   has no foreign functions: the runner performs a fixed table of
   operations. So it can do what they can't, and have no raw layer at all,
   which is what makes `{Files}` a guarantee and not a habit.
4. **The cost of fine grain is long signatures, and the cure is a name or
   inference.** Roc gave up granular effects over signatures that grow
   whenever a callee does; Unison Cloud's rows show the length; Koka
   avoids both by inferring effects and by `io`. Nobody reports regretting
   the split itself. Koka and Effekt are the two with a declaration for
   naming a set.

Stitchwort's own choice of grain differs from Flix's and the capability
languages' in one way: they split read from write in the type. Here that
is a handler (`Files.readOnly`), because a row entry is paid for on every
signature and a handler is paid for once.

## 3. The options for Stitchwort

| | 1. One `IO` | 2. Separate abilities | 3. Separate abilities and a set name |
|---|---|---|---|
| File access is | more operations in `IO` | `Files`, beside `IO` | `Files`; `IO` is the name for `{Console, Files, …}` |
| `{IO}` in a type means | anything the host can do | the console only | anything the host can do |
| A narrower promise | none | `{Files}`, `{IO}` | `{Files}`, `{Console}` |
| A script's `main` | `{IO}` | `{Files, IO}`, growing with each host ability it uses | `{IO}`, or the exact list if it wants to say |
| Test of a file loop | `IO.simulate` with a world: input lines and a disk | `Files.simulate disk` | `Files.simulate disk` |
| Test of console code | the same world, its disk empty | `IO.simulate lines` | `Console.simulate lines` |
| A handler that narrows files (`readOnly`) | a clause for every `IO` operation, forwarding all but two | two clauses and a forward | the same |
| Adding `Clock` later | breaks every `IO` handler and every proof that takes an `IO` program apart | breaks nothing | breaks nothing; `{IO}` code may now read the clock |
| New language feature | none | none | names for ability sets (§4) |

There is a fourth, which the file design called B: one raw `IO` with every
host operation, and library abilities (`Files`, `Console`) whose handlers
forward to it. It is what Flix, Unison and Haskell's effect libraries do
(§2.3, point 3), because their `IO` must stand for any foreign call. The
file design rejected it and I agree: the narrow abilities are then a
habit, not a guarantee, since the raw operations sit in `IO` for any
`{IO}` code to call, and every forwarding handler is boilerplate.
Stitchwort has no foreign calls, so it has no need of the raw layer.

### The same program in each

A small tool: read a file, tidy it, print a summary, write it back.
`Files`' operations are the file design's (§2.1 there); the option 2
version was checked on a cut-down `Files` [ran: `p1.sw`], the others are
sketches.

**Option 1, one `IO`:**

```
def tidyFile (path: Path): {IO} () := match IO.readFile path with
  | Err error => IO.print error.show
  | Ok source =>
    let tidied := tidy source
    IO.print "${path.show}: ${tidied.lines.length} lines"
    IO.writeFile (path, tidied) |> .orPrint

def main(): {IO} () := IO.args().each (arg => tidyFile arg.toPath)

test "tidies a file" :=
  let world: World := { input = [], disk = Disk.of [("a.txt", "  hello  ")] }
  let (after, _) := IO.simulate world (() => tidyFile "a.txt".toPath)
  after.printed == ["a.txt: 1 lines"] ∧ after.disk.read "a.txt".toPath == Ok "hello"
```

Short to write. `tidyFile`'s type says only "does something outside".
Every test builds a `World`, and every theorem about a console program is
stated about one.

**Option 2, separate abilities:**

```
def tidyFile (path: Path): {Files, IO} () := match Files.read path with
  | Err error => IO.print error.show
  | Ok source =>
    let tidied := tidy source
    IO.print "${path.show}: ${tidied.lines.length} lines"
    Files.write (path, tidied) |> .orPrint

def main(): {Files, IO} () := IO.args().each (arg => tidyFile arg.toPath)

test "tidies a file" :=
  let disk := Disk.of [("a.txt", "  hello  ")]
  let (printed, (after, _)) := IO.simulate [] (() => Files.simulate disk (() => tidyFile "a.txt".toPath))
  printed == ["a.txt: 1 lines"] ∧ after.read "a.txt".toPath == Ok "hello"
```

The body is the same, one word aside. The types say more, and they nudge
the code towards a better shape, where the file work and the printing come
apart:

```
def tidyFile (path: Path): {Files} (Result Nat FileError) := match Files.read path with
  | Err error => Err error
  | Ok source =>
    let tidied := tidy source
    Files.write (path, tidied) |> .map (_ => tidied.lines.length)

def main(): {Files, IO} () := IO.args().each (arg =>
  match tidyFile arg.toPath with
    | Ok lines => IO.print "${arg}: ${lines} lines"
    | Err error => IO.print error.show)

test "tidies a file" :=
  Files.simulate (Disk.of [("a.txt", "  hello  ")]) (() => tidyFile "a.txt".toPath)
    == (Disk.of [("a.txt", "hello")], Ok 1)
```

Now the test needs only a disk, and `tidyFile` provably prints nothing.
Under option 1 the same refactoring is possible but the type doesn't
record it and the test still needs the world.

**Option 3, a set name:**

```
def tidyFile (path: Path): {Files} (Result Nat FileError) := …  -- as above

def main(): {IO} () := Console.args().each (arg =>
  match tidyFile arg.toPath with
    | Ok lines => Console.print "${arg}: ${lines} lines"
    | Err error => Console.print error.show)
```

`tidyFile` and its test are option 2's. `main` says `{IO}`, as in option
1, and keeps saying it when the tool later reads the clock. A `main` that
wants to promise more writes the list: `{Console, Files}`.

**Capability values** (§6), for comparison:

```
def tidyFile (files: FileAccess e) (path: Path): {e} (Result Nat FileError) := match files.read path with
  …

def main(): {IO} () := IO.args().each (arg => … tidyFile IO.files arg.toPath …)
```

The disk is an argument, passed down every call. The row is still there
(`{e}`), so the value has bought nothing the row didn't already say [ran:
`p5.sw`].

## 4. Names for ability sets

### 4.1 The feature

A declaration that gives a name to a closed set of abilities:

```
ability IO = {Console, Files}
ability Chars = {Parse Char}
ability App = {Log, Store, Fail}
```

(The syntax is a sketch: `ability Name =` beside `ability Name where`. The
lane settles it in a short syntax note; `abilities` as a new keyword is
the alternative.)

- **Meaning: replacement.** Where a row is read, a set's name is replaced
  by its members: `{IO, Fail}` is `{Console, Files, Fail}`. Rows are
  already sets sorted by name (§1, fact 3), so the result is the same row
  however it was written. A member named twice, once through the set and
  once directly, is merged, not an error, so `{IO, Clock}` keeps checking
  on the day `Clock` joins `IO`.
- **No subsumption rule is needed.** A `{Files}` function is already
  usable in `{IO}` code (§1, fact 4).
- **A set is not an ability.** It has no operations of its own and can't
  be handled as one thing: `handle … with | IO.… ` is an error that says
  to handle its members. A library can still offer one handler for a set
  by nesting its members' handlers (`IO.simulate`, §5).
- **Cost to the checker:** one lookup for each name in a written row, in
  `effect_type` [source]. Nothing in unification, inference or the
  translation to trees changes, because they see the row after
  replacement.
- **Cost to proofs and the kernel: none** [estimated, from the source: the
  term built from `{IO}` is the term built from its members, so its hash
  is too]. No theorem mentions a set's name.
- **Messages** print a row with its members, as the kernel sees it. Folding
  a printed row back to a name in scope (`{IO, Fail}` for
  `{Console, Files, Fail}`) is a nicety the lane should try and measure
  against confusion.
- **Not included:** sets with parameters (`ability Stateful s = {State s,
  Fail}`), sets with a row variable, or reaching a member's operations
  through the set's name (`IO.print` for `Console.print`). Each is a
  possible later step; the last would keep `IO.print` working and the lane
  should weigh it.

### 4.2 Who would use it

- **The host bundle,** `IO` (§5).
- **Applications.** A real program's own abilities travel together: a
  roguelike's `{Terminal, Random, Log}`, a service's `{Log, Store, Fail}`.
  A name for the bundle is one place to add the next one.
- **`{Parse}` for `{Parse Char}`.** generic-parse.md (D3588) looked for
  exactly this and found it missing; it recommended writing `{Parse Char}`
  out. With sets, `ability Parse.Chars = {Parse Char}` is available if the
  68 AoC files' signatures are wanted shorter. I would still write it out.

### 4.3 What can go wrong

- **Everyone writes `{IO}` and the detail is lost.** Flix's book warns
  against exactly this for its primitive `IO` [cited]. Here the
  narrow row pays its own way: a `{Files}` function is tested with a disk
  and nothing else, and a proof about it handles four operations, where
  the same function typed `{IO}` needs the whole world and a clause for
  every host operation. So the place `{IO}` is cheap to write is the place
  it does no harm: `main` and the few functions near it.
- **`{IO}` changes meaning when the set grows.** That is its purpose. Code
  that handles `{IO | e}` member by member would start passing the new
  ability through; the library's `IO.simulate` is the one handler that
  must grow with the set.
- **One more thing to learn.** It arrives late in the guide, after
  handlers, as "a name for a list you are tired of writing".

### 4.4 Now or later

Until a third host ability exists the feature saves almost nothing: rows
today are short (§1), and with files the longest common row is
`{Files, IO, Fail}`. What it buys at once is the naming: `{IO}` meaning the
outside world from the day files arrive, so that the guide's file chapter
is written once. So: **decide the end state now, build F1 as designed, and
build the set feature and the rename straight after**, beside the
formatter's work, not before it. If the answer to D3596 is no, nothing in
F1 changes.

## 5. `main`, tests and proofs

**`main`'s row.** Any set of the abilities the runner performs, with or
without `Fail` and `Partial`. In the end state: `{Console}`, `{Files}`,
`{Console, Files, Fail}`, or `{IO}` for all of them. Hello world can be
either of these, and the guide should pick the first, which says what it
does:

```
def main(): {Console} () := Console.print "hello"
```

**The row as a statement of what a program can do.** With separate
abilities, `main`'s row is checked evidence: a program whose `main` is
`{Console, Fail}` cannot touch a file, and `stitchwort check` knows that
without running it. `stitchwort run` could show it for a program you
didn't write, and the file design's `--files none` is then a no-op the
runner can confirm. Under one `IO` the row says nothing. A `main` that
says `{IO}` gives this up, which is its author's choice.

**Tests.**

- One part of the world: `Files.simulate disk prog`,
  `Console.simulate lines prog` (today's `IO.simulate`).
- Two: nest them, in either order; both orders give the same answers [ran:
  `p1.sw`].
- All of it, for code typed `{IO}`: a library handler `IO.simulate world
  prog`, which is the members' handlers nested, over a record with a field
  for each (`input`, `disk`, later `now`). It grows when the set does.

**Proofs.**

- A theorem about a `{Files}` function is about a disk: `Files.simulate`'s
  laws hold by `rfl` and a statement about a real function took one
  `rewrite` (file-io-and-text.md §3, [ran] there).
- The same function typed with one `IO` is the same proof with a world
  record round it, and nine more clauses wherever a program is taken apart
  by `match reify` (§1, fact 2). Lemmas about `print` gain a disk they
  don't use and must say is unchanged.
- "This code doesn't write files" is a theorem about a handler under one
  `IO` (the disk afterwards equals the disk before, for every program). With
  separate abilities it is the type: the row has no `Files`.
- Nothing here needs a new proof method. The friction the file design
  found (induction over a program by `match reify` isn't seen as
  terminating) is the same in every option.

**The runners.** F1 already turns `main`'s two fixed shapes into a set
[file-io-and-text.md §2.2]. Each further host ability is then a row in
that table. An operation in a row of several abilities is wrapped once for
each ability before it [source: the `Plus` chain, `effects.rs`], so a
wider `main` row costs a few constructor steps an operation [estimated];
worth one measurement in F1, on a print loop.

## 6. Capability values

In Eio, Pony, Austral, E and WASI, the right to touch files is a value: a
directory handle that a function must be given, and that can be narrowed
to a sub-folder before it is passed on (§2). It works there because those
languages have no checked effects (or, for WASI, no types at all at that
boundary): the value is the only evidence there is.

Stitchwort can write the same thing, a record of functions over a row
variable [ran: `p5.sw`]:

```
type FileAccess (e: Effects) = {
  read: Path → {e} (Result Text FileError),
  write: (Path, Text) → {e} (Result () FileError)
}
```

but it adds little:

- **The row still decides.** A pure function handed a `FileAccess e` can't
  call it: "its row variable isn't part of the enclosing function's
  abilities" [ran]. So the value is not what grants access; the row is.
- **A handler already is a scoped grant.** `Files.under folder` gives the
  code inside it a narrower disk for the length of a block, checked by the
  types, without an argument on every function between. Flix narrows the
  same way (`withChroot`, `withReadOnly`) [cited].
- **What values can do that one ability can't:** two different grants at
  once, told apart by the types (`source: Dir` read-only and `output: Dir`
  writable). With one `Files` ability a block has one disk; the two folders
  are told apart by path. If that ever matters, the answer in this family
  of languages is named handler instances (Koka's named effects, Effekt's
  capability values; neither read for this note), which is its own design and not needed for a
  formatter.
- **For real confinement,** neither handlers nor values see through
  symbolic links; the host does. The file design's flags
  (`--files under=DIR`, resolved by the runner after links) are WASI's
  preopened folders by another name, and they stay.

So: **no capability values in std.** Paths as plain data, abilities for
access, handlers for narrowing inside a program, host flags for a program
you don't trust.

## 7. Staging

Lane hours are estimates. "Opus" follows D2506 for syntax, the elaborator's
rows and the prelude.

| Stage | What | Model | Hours |
|---|---|---|---|
| F1 | As file-io-and-text.md §6, unchanged: `Files` beside `IO`, `main`'s row as a set | Opus | 4–5, already counted there |
| G1 | Names for ability sets (§4): a one-page syntax note first, then the parser, replacement in `effect_type`, merge of repeats, the error for handling a set, messages, the formatter, hover and go-to-definition, guide chapter 8 and `docs/syntax.md`, accept and reject examples | Opus | 4–6 |
| G2 | `IO` becomes the set; the console ability becomes `Console` (the built-in's name in the registry, the prelude, std, `aoc/`, `games/`, examples, the guide's chapters 1, 8, 9 and 11); `IO.simulate` becomes `Console.simulate`, and a new `IO.simulate` over a world record | DeepSeek for the sweep, Opus for the registry, the prelude and the review | 3 + 1 |
| G3 | `randomSeed` and `args` leave the console ability for their own small host abilities, when a clock or environment variables are designed | Sonnet | 2–3 |

G1 and G2: 8–10 hours. G3 is not part of the recommendation's core and
waits for its neighbours. None of it blocks the toy formatter, which needs
only F1.

## 8. Questions for Matt

D3595 **replaces D3585**: the recommended answer is the same, so F1 can
start on a yes to either, but it adds the rule for what comes after.
D3586 and D3587 in file-io-and-text.md are untouched.

**D3595: is each part of the outside world its own ability, starting with
`Files` beside the console?**
*The problem:* a handler, and a proof that takes a program apart, must
answer every operation of an ability [ran]. If file access goes into `IO`,
every console test's pretend world carries a disk, a "read-only" handler
has to forward every console operation by hand, and each later addition
(a clock, the network) breaks every `IO` handler anyone has written.
*The change:* one ability for each part of the outside world that has its
own pretend version: the console, `Files`, later `Clock` and others. No
finer than that: read-only and "this folder only" are handlers. This is
what languages with handlers do (Flix, Unison Cloud, Haskell's effect
libraries; Koka in its types; §2); one big `IO` is what languages have
where `IO` can't be handled at all.
*What it should do:* a file loop is tested with a disk and nothing else;
`{Files}` and the console's row are checked promises about what code can
touch; adding a host ability later breaks no handler and no proof. No
cost beyond F1's own 4–5 hours [estimated]. **[rec: yes]**

**D3596: add names for ability sets, and make `IO` the name for
everything the runner performs?**
*The problem:* with D3595, `{IO}` would mean "the console, not files",
which is not what `IO` means anywhere else, and a script's `main` grows a
longer row with each host ability it uses (`{Clock, Console, Files,
Fail}`). Rows are written on every function here, not inferred as in Koka,
so the length is paid along the whole call path.
*The change:* a small language feature, `ability IO = {Console, Files}`: a
name replaced by its members where a row is read, invisible to the kernel,
hashes and proofs. Today's console ability is renamed `Console`
(`Console.print`), and `IO` is the set of all host abilities. The
alternatives: no set names, with `IO` staying the console's name; or set
names with the bundle called something else (`Host`) and `IO` left as it
is.
*What it should do:* `main(): {IO} ()` can read a file and keeps its type
as host abilities are added; `{Console}` and `{Files}` say exactly what
they mean; applications get the same tool for their own bundles. About
8–10 lane hours after F1, not blocking the formatter [estimated].
**[rec: yes, with `IO` as the set and `Console` as the ability]**

## Findings worth tickets

- **`IO` already mixes three things:** the console, the host's entropy
  (`randomSeed`) and the command line (`args`). `Terminal.scriptedHost`, a
  pretend terminal, has clauses for both [source]. Stage G3; worth a
  ticket whatever D3596's answer.
- **`main`'s row could be shown before a program runs.** With separate
  host abilities, `stitchwort check` knows what a program can touch. A
  line in `run`'s `--verbose` output or a `stitchwort doc Main.main` note
  ("may: print, read and write files") is small, and makes the file
  design's `--files none` checkable without running. After F1.
- **`return _` isn't accepted in `match reify`:** "expected a name for the
  result, but found `_`" [ran: `E-PARSE`]. A handler's `return` clause may
  want the same check. Small.
- **A row can't be given a name with `type`,** and the message is about
  records: `type World = {IO, Fail}` is `E-PARSE`, "expected a field name,
  but found `IO`" [ran: `p4.sw`]. Until G1, a note saying that rows can't
  be named would help; G1 replaces it with a pointer to the right
  declaration.
- **A handler can't forward "every other operation of this ability".** A
  narrowing handler writes a clause for each operation, including those it
  passes on unchanged [ran: `E-HANDLER`]. Small abilities keep that
  cheap; a `| other, resume => …` forwarding clause is a possible design
  if a large ability ever appears. Not proposed here.
- **Two folders with different rights at once** can't be told apart by
  type with one `Files` ability (§6). If a tool needs it, named handler
  instances are the design to look at. A research ticket, not work.
- **The guide's chapter 8 says "the design behind Unison's abilities and
  Koka's effects".** Worth one more sentence once F1 lands: unlike both,
  there is no raw `IO` under the host abilities, so a row is a guarantee.
- **Cost of a wide `main` row at run time** is unmeasured: an operation is
  wrapped once for each ability before its own in the row [source]. One
  measurement in F1 (a print loop under `{Console}` and under a row of
  five).

## Appendix A: the probes

In the lane's scratchpad; not committed. Run with the main checkout's
release binary (built 14 Nov, 16:53).

| Probe | What it shows | Result |
|---|---|---|
| `p1.sw` | A cut-down `Files` with `Files.simulate`; a `{Files, IO}` function tested under both handlers, nested in either order | 2 tests pass |
| `p2.sw` | A handler for `IO` with only a `print` clause | `E-HANDLER`: "no clause for `readLine`" |
| `p3.sw` | `match reify` on an `{IO}` program with only a `print` clause | `E-NONEXHAUSTIVE`, naming the other eight |
| `p4.sw` | `type World = {IO, Fail}` | `E-PARSE`: "expected a field name" |
| `p5.sw` | A record of file functions over a row variable, used from `{IO \| e}` code; the same record used from a pure function | checks; `E-ABILITY` for the pure one |
| `p6.sw` | `main(): {Files, IO} ()` | checks; `run` gives `E-MAIN-TYPE` |
| `p7.sw` | An `{IO}` function passed as a `{Files, IO}` callback, by name and in a lambda; an `{IO}` thunk under a `{Files \| e}` handler | checks |
