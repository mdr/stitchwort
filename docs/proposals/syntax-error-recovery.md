# Syntax error recovery: working through a broken declaration

**Status:** design note, 14 November 2026 (SW-3161, for D3563). Paper lane:
nothing is built. D3580 decided (Fable's split, revised in here); D3581
decided (Matt, 14 Nov 2026: yes): the extra errors show in `check` too.
It builds on, and in part replaces, [parse-recovery.md](parse-recovery.md)
(SW-1917, D2780–D2785, none of it built), and sits inside the end state of
[syntax-tree-architecture.md](syntax-tree-architecture.md) (D3562: one
lossless tree, the compiler's tree lowered from it).

Claims are marked **[source]** (read at `051fe154a`), **[measured]** (a
probe with the main checkout's release binary, files in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3161/`),
or **[estimated]**.

## In plain words

**The problem.** While you type, the declaration you are typing in almost
never parses. Today the parser gives up on that whole declaration at its
first syntax error. If its header parsed, the header is kept, so other
declarations can still use it. Everything below the header is dropped: no
type errors, no hovers, no completion from this check, and no second syntax
error. In VS Code and the playground, the declaration you are working on
goes blank at the moment you most need help.

**The change.** The parser carries on after a syntax error inside a
declaration. It puts a marked gap where the broken text is: an `Error` node
in the lossless tree, and a *missing expression* in the compiler's tree. The
checker treats that gap like `?`: it checks around it and never sends the
declaration to the kernel. Anything whose type depends on the gap is not
reported, so one typo doesn't set off a pile of errors after it.

How much a broken line costs depends on what kind of line it is (D3580):

- **A binding line** (a `let`, a local `def`, a `match` arm, the inside of
  a bracket) costs only that line. The lines after it are checked as
  usual.
- **A proof-step line** (`rewrite … in`, a `calc` head or step, a line
  ending in an operator) owns the lines below it: they are its body. So the
  gap covers them too. They are still read and checked, for hovers and
  their own local errors, but against an unknown goal, so nothing that
  depends on the goal is reported. The editor shows the goal at the gap:
  what is left to prove there.

**What it should do** (the scenarios are probes of today [measured]; the
"after" column is the design):

| You are typing | Today, in the editor and `check` | After |
|---|---|---|
| **A half-typed `let`.** Line 2 of a four-line `let` block reads `let k := h.` | One error, "expected a field name after `.`". Lines 1, 3 and 4 have no hover. The type error on line 3 (`let bad: Nat := "text"`) isn't shown. The outline item stops at the header | The same syntax error, plus line 3's type error. Hover works on every line, `h` included, and completion offers `h` and the parameters from this check. `k` is in scope below with an unknown type, and nothing that uses `k` is reported |
| **A missing `)`.** `let a := (xs.length + 1` with the next line starting `let b` | "expected `)`, but the line starting with `let` … starts a new statement", pointing at line 3 | "expected `)`" at the end of line 2, with a second label on the `(`. The bracket counts as closed there, so `a: Nat` is checked and shows on hover. Line 3's own type error is shown too |
| **An unfinished `match` arm.** `\| 1 =>` with nothing after it, then `\| _ => "many"` in a `Nat` function | "expected an expression, but found `\|`" on the next arm, and nothing else | "expected an expression after `=>`" at the end of the `\| 1 =>` line. The other arms are checked, so `"many"`'s type error is shown. The editor's goal view shows `Nat` as what the empty arm must give |
| **A stray token.** `let a := n + ) 1` | "expected an expression, but found `)`", and nothing else in the declaration | "unmatched `)`" on the `)`. The rest of the line reads as `n + 1`, and later lines are checked |
| **Two broken lines** (`let a := n +` and `let b := (n`) | Only the first error | Both errors, and the type errors of the other lines |
| **A broken step in a proof.** Line 2 of `rewrite h1 in` / `rewrite h2) in` / `rfl` | "expected the end of the declaration, but found `)`", and nothing else; no hovers in the body | The syntax error. Hovers on all three lines. `rfl` is not judged (no false "`rfl` can't prove this"), and the goal view shows `b + 1 = c + 1` at the gap |

Nothing changes for a file without syntax errors: same trees, same hashes,
same messages. A file with a syntax error still never passes, is never
cached, never runs its tests, and is never formatted (D1021). A declaration
with a syntax error never gets a kernel term or a hash, whatever the
recovery made of it (§4.1).

## 1. What happens today

**Parsing** [source]. `parse_tokens` (`crates/syntax/src/parser.rs:162`)
cuts the file into declarations at column 0 (`split_decls`, `:600`) and
gives each one a fresh `Parser`. Each parsing function returns `Result`, and
the first `Err` unwinds to the loop at `:300–355`. There a `def`, `theorem`,
`export` or `opaque` whose header parsed keeps its signature, with
`body_error` set and no equations (`:335–352`; the header waits in
`Parser::header`, `declarations.rs:351–356`). Any other declaration is
dropped, and the names it would have declared go in `Module::failed`
(`declared_names_of`, `:403`). Only the first error of a declaration is
ever produced. The parser never backtracks (parse-recovery.md §1.2
checked this; I didn't recheck all of it).

**Layout does most of the work already** [source]. A block (`block`,
`:2612`) sets `limit` to its column, and `peek` (`:1249`) returns `None` at
a *stop*: a token that starts a line at or left of `limit` and doesn't
continue a bracket or an operator (`is_stop`, `:1110`). So a parse that
runs out of line sees "nothing", and `unexpected` (`:1390`) words the error
as "the line starting with … starts a new statement". Arms work the same way
at the arms' column (`arms`, `declarations.rs:660`), and so do `calc` steps
(a `_` starting a line, `:1103`). Every bracket's partner is worked out
before parsing starts (`match_brackets`, `:806`). These are the
synchronisation points recovery needs, and they are already computed.

**The lossless tree** [source, measured]. Built from marks beside the
compiler's tree (`crates/syntax/src/tree.rs`, step 1 of D3562, finished). A
declaration that fails is one `NodeKind::Error` node holding all its tokens
flat, even when its signature was kept: `dev tree --print` on the
half-typed-line probe gives `Error` with 40 bare tokens under it. The
tree's doc already describes the end state this note fills in
(`tree.rs:90–98`). A file with a lexical error has no tree (SW-3185).

**Checking** [source]. A kept signature fails with `E-UNPARSED-BODY`
(`elab/src/module.rs:3025`), which is never reported: the driver folds it
into the parser's error (`merge_recovered`, `driver/src/driver.rs:1047`).
The signature stands in for the declaration, so its users are checked
against it. `?` (`Expr::Goal`) is already a hole that is checked around: a
frozen metavariable that unification never solves, applied to the
variables in scope (`elab/src/goals.rs:420`). A term containing one can't be
zonked, so it never reaches the kernel (`goals.rs:14–18`).

**The editor** [source, measured]. Hover, go to definition and semantic
colouring come from the check's navigation index. For the half-typed-line
probe the index has 11 entries in the file, all in the header; the same
declaration with a type error instead has 17, covering the body. The
outline item's full range ends at the header (`[0,0,0,44]`), so folding and
the outline lose the body too. Three workarounds exist because of this:

- `WorkspaceNav::store` (`crates/lsp/src/lib.rs:563`) keeps the last
  answers from when the file parsed, and completion takes locals from them
  (`crates/lsp/src/complete.rs:1–9, 97`).
- Member completion after `.` re-checks the file with a dummy name after
  the dot (`lib.rs:1755`, `driver/src/at.rs:1100`).
- `goals_kept` (`lib.rs:5023`) keeps goals that were in a declaration that
  stopped parsing, so they don't flicker.

The playground runs the same server in a worker (`crates/web/src/lsp.rs`)
and its `check` goes through the driver (`crates/web/src/lib.rs:112`), so
it behaves the same.

**The formatter** refuses a file with any syntax error (D1021, D2783;
`crates/fmt/src/lib.rs:4`).

## 2. Where recovery happens

### 2.1 The rule

At each recovery point the parser catches an error from inside it,
records the error, puts a gap in the tree, moves forward to a token it can
carry on from, and returns success. The innermost point that applies wins,
so a broken token deep in a line costs at most that line. Every move is
forward, and **any choice is safe: the error is already reported, so a
different choice changes only how much is checked, never what a correct
file means** (parse-recovery.md's rule, kept). Resource limits are never
recovered from (`E-RESOURCE` from `deeper()`, D2543).

### 2.2 The points, innermost first

| | Where | Moves to | Puts in the tree | Notes |
|---|---|---|---|---|
| **R1 Ran out** | An expression or a closing token is wanted and `peek()` is `None`: a stop, the end of the declaration | Nowhere: consumes nothing | No node: the parent lacks that child (§3) | The commonest case: `:=` or `=>` with nothing after it, a trailing operator, `rewrite h in`, `let x :=`. A missing closer (`)`, `]`, `}`) or joining keyword (`then`, `else`, `with`, `=>`, `in`) counts as present there; the expression after a missing keyword is missing too |
| **R2 Inside brackets** | An error inside `( … )`, `[ … ]` or `{ … }` whose partner is in the declaration | The partner (from `matching`) | `Error` node over the skipped tokens inside the brackets | Independent of layout, so it works on one long line. The bracket expression becomes missing; the code around it carries on |
| **R2b Stray closer** | A `)`, `]` or `}` with no partner, where an operand should start | One token on | `Error` node over the token | Then the operand is tried again. Only where an operand *starts*, never after a finished one (§3.2). Several on one line report once |
| **R3 Block line** | A statement of a block fails | The next stop of this block, or a token that ends blocks (`\|`, `where`, `:=`, `decreasing`, `unfolding`; `ends_blocks`, `:2688`) | A binding line: `Error` node over it, inside the `Block`. A proof-step line: a `Gap` node holding that `Error` node and the rest of the block (§2.3) | D3580's split. A binding line: later lines are checked as usual; a `let` whose name (or simple pattern) was read keeps it, bound to a missing value. A proof-step line: later lines are parsed and checked against an unknown goal (§4.3) |
| **R4 Arm** | An arm of a definition, a `match`, a clause lambda or a handler fails | The next `\|` at the arms' column, or the end of the arms | `Error` node over the arm, or over its body | Patterns read: the arm is kept with a missing body. Patterns broken: the arm is dropped, and the match is marked *incomplete*, so coverage isn't checked (§4.2) |
| **R5 Calc step** | A `calc` head or step fails | The next `_` starting a line (`starts_calc_step`) | A `Gap` node: the step's `Error` node and the steps after it | A proof-step line (§2.3). The later steps are checked on their own (each relation against its written sides); the chain's ends are not compared with the goal |
| **R6 Body** | Nothing inside caught it: the `:=` body or the arms as a whole | The end of the declaration | `Error` node over the rest | Replaces today's "signature only" (`body_error`): one equation with the header's patterns and a missing body. Never no body, which would make a primitive (`declarations.rs:423`) |

**Not recovered** (as today, D2782): errors in a header's parameters and
inside `type`, `interface`, `ability`, `namespace` and `import`. The
declaration fails whole and its names go in `Module::failed`. The one
exception is R1 in a header's result type (`def f (n: Nat):` with nothing
more), which can come in a later stage (S6 in §6): the body is then checked
against an unknown type for its hovers, and the declaration gives no stand-in.

### 2.3 Binding lines and proof-step lines (D3580)

Proofs are terms, and some lines take the lines below them as their body:
`rewrite h in` (`expr` and `block`, `parser.rs:2590–2660`), a `calc` head
and its steps, and a line ending in an operator, which the next line at the
block's column continues. Fable's probes [measured, files in
`…/scratchpad/fable-d3580/`, `p5.sw`] on a correct three-line `rewrite`
proof with its middle line broken:

- **Skip only the line:** the correct last line `rfl` is checked against
  the wrong goal and gets a false "`rfl` can't prove this".
- **A gap, then the last line as a new statement** (R3 as first written):
  a false `E-REWRITE-NO-GOAL` on the first line.
- **One gap over the rest:** the right goal, and no false error.

In a program block, skipping a broken `let` worked as intended. So R3
looks at the failed line's form:

- **Binding line**: it starts with `let`, a local `def` or `theorem`, or
  it is an arm (R4) or the inside of a bracket (R2). Any other statement
  that is not a proof-step line (a sequence statement, the result line)
  counts here too: nothing below reads its value. Cost: the line.
- **Proof-step line**: one that isn't a binding line and starts with
  `rewrite`, `calc` or a calc step's `_`, or ends in an operator (with the
  line after it). Cost: a gap whose scope is the rest of its block. The
  lines below are parsed as a block and kept under the gap.

The binding test comes first, so `let a := n +` is a binding line, and the
line continuing it is skipped with it (R3 resumes at the next stop, which a
continuation isn't).

In the lossless tree the second kind is a `Gap` node with two children: the
`Error` node over the broken line, and the `Block` (or the steps) below it.
Lowering turns it into `Expr::Missing { span, rest: Some(…) }` without
looking inside the `Error` child (§3.1). A node rather than a rule on
`Error` nodes, so lowering never has to guess from skipped tokens. My call.

### 2.4 What layout buys

Declarations, blocks, arms and calc steps are all laid out by column. So
the place to resume is almost always "the next line at or left of this
construct's column", and the parser already knows where that is (`is_stop`)
without guessing from keywords. A parser for a language with braces has to
guess (rust-analyzer's recovery sets). Here only R2 and R2b work inside a
line, and both rely on the bracket partners already computed. One case
weakens this: an unclosed `(` makes `continues_bracket` (`:1234`, which
counts brackets from the start of the declaration) treat a later line
starting with `)` or `,` as a continuation. That costs at most a few more
skipped lines in a declaration that is already reported, so I'd leave it.

### 2.5 Parser state at a recovery point

The parser has eight mode fields (`in_list`, `limit`, `allow`,
`calc_depth`, `rewrite_rule`, `guard_start`, `rewrite_at`, `let_value`;
`parser.rs:703–732`). Each site saves and restores the ones it changes by
hand, and some don't restore them on the error path (parse-recovery.md
§1.2; not rechecked), which is harmless only because an error throws the
parser away today. On top of those there is
now the marks state: `open` (operators waiting for their right operand,
`:753`) and `header`. Each recovery point snapshots one `Copy` struct of
the modes plus `open.len()` before it tries, and on an error restores the
modes and truncates `open`. Marks already recorded stay: they are finished
constructs inside the skipped range, and they nest inside the new `Error`
node (§3). (parse-recovery.md's `Modes` struct, SW-1982; my call to keep
it.)

### 2.6 How many errors are reported

One per recovery point that fires. What a point skips isn't parsed, so it
can't produce more. In practice that means at most one syntax error per
line, and no limit per declaration [estimated: a line that triggers R2b
and then R3 would give two; I'd merge errors that land on the same line
into the first]. My call. A cap per declaration isn't needed: every
reported error is at a different place the author has to visit.

### 2.7 Error positions

An R1 error points at the end of the last token read, which is usually
where the cursor is. If a stop ended the expression, a second label goes on
the token that ended it. Today the error points at that token, often on the
next line (the probes show this on every R1 case). A missing closer gets a
second label on its opening bracket. The current "the line starting with …
starts a new statement" wording becomes a note on the R1 error, since it
still explains *why* the line ended. My call; the 82 reject examples with
`E-PARSE` [measured] get new snapshots (migration cost doesn't count, D2303).

## 3. Error nodes in the lossless tree

- **A proof-step gap** (R3's second kind, R5) is a `Gap` node: the
  broken line's `Error` node, then the lines below it as ordinary nodes
  (§2.3).
- **Skipped tokens** (R2–R6) go in an `Error` node *where they were*: a
  `Block`'s child between two `Let`s, an `Arm`'s body, a `Paren`'s inside.
  The finished constructs inside the skipped range keep their nodes,
  nested in the `Error`. The declaration's root is its real kind (`Def`,
  `Theorem`), not `Error`. `decl_kind` (`parser.rs:381`) is then given the
  kept declaration.
- **Missing parts** (R1) get no node: the parent lacks the child. A `Let`
  with no value node, an `Arm` with no body. Lowering (and, before it, the
  parser) reads "required child absent" as a missing expression placed at
  the end of the parent's last token. No node with zero tokens, so the
  tree still reads back byte for byte with no special case, and
  `check_spans` needs no change for R1. (rust-analyzer does the same.) My
  call.
- **A declaration that fails whole** (header errors, D2782's kinds, and
  lexical errors after SW-3185) stays one `Error` root, as today.
- **The span check** (`SyntaxFile::check_spans`) gets one rule: a missing
  expression's span (a point) is exempt, like the other synthetic spans
  (`tree/spans.rs`).

### 3.1 Before lowering and after

**Before SW-3160's lowering** (architecture B, today), each recovery point
does both jobs. It records the `Error` mark and returns the compiler's
node: `Expr::Missing { span, rest }`, a `Stmt::Error`, an `Alt` with a
missing body, or a `Match` with `incomplete: true`. **After lowering**, the
parser only records marks, and lowering turns an `Error` node, a `Gap` node
or an absent required child into the same compiler nodes. The recovery logic (where to resume and
what to skip) lives in the parser either way. Only the few lines that build
the compiler's nodes move from the parser into lowering when step 4
deletes direct construction. So recovery can go first and lose almost
nothing ([§6](#6-stages)). SW-3160's oracle ("lowering gives exactly the
tree the parser builds") then has to cover recovered declarations too.
The recovery corpus (S5) gives it the files.

### 3.2 A marks hazard

An operator finds its left operand from the last mark that ends where it
stands (`operand_start`, `parser.rs:965`). An `Error` mark that ended just
before an operator would be taken for its operand. R2b therefore skips
only where an operand *starts* (before any atom), and the other points end
at stops, closers or the end of the declaration, where no operator follows.
A test in S3 covers `f ) * 2` and `a + ) b * c`.

## 4. The checker: a gap that causes no cascade

### 4.1 The node, and why the declaration fails

`Expr::Missing { span, rest: Option<Box<Expr>> }` in `ast.rs` (a variant
rather than a flag on `Goal`, so every match on `Expr` is made to handle
it). `rest` is the block a proof-step gap covers (§2.3), `None` otherwise.
The elaborator handles the gap itself like `Expr::Goal` (`check.rs:2108,
5004`):

- **Checked against `T`**: a frozen metavariable applied to the scope, as
  `goals::hole` makes, flagged as an *error hole*. It isn't printed as a
  goal diagnostic.
- **Inferred**: its type is a fresh metavariable, also flagged.
- **`rest`** is checked against an unknown goal (§4.3), and its value is
  thrown away.
- **The goal at a gap** goes to the editor's goal view and hover, not to
  `check`'s output (D2781, decided): at an R1 gap (where you are typing) and
  at a proof-step gap (what is left to prove from there). Gaps over skipped
  binding lines show no goal; hovering over them shows "didn't parse;
  expected `T` here" when `T` is known.

**The declaration fails because the parser says so**, not because a hole
was found. Not every recovery leaves a hole: R2b reads `n + ) 1` as
`n + 1`, a dropped binding line leaves none, and R4's dropped arm leaves a
`match` with one arm fewer. Each of those could otherwise check cleanly and
produce a kernel term for text that isn't what was written. So every
recovery point marks its declaration as failed, as `body_error` does today
(`module.rs:3020`), and the module fails a marked declaration with
`E-UNPARSED-BODY` whatever its body checks to. The signature stands in for
it, and the driver folds the error into the parser's (D2781; `driver.rs:1060`).
The zonk failing on an error hole stays as a second line of defence. So
`check` can never pass a file with a syntax error, and no kernel term or
hash is ever made for such a declaration. (Fable's safeguard 1.)

### 4.2 Stopping the cascade

Three layers, at the source first:

1. **The unifier stays strict.** An error hole does *not* unify with
   anything: that would break `unify`'s precondition that both sides have
   the same type (`elab/src/unify.rs:50`), and could hand the evaluator an
   ill-typed value, a possible panic in the editor server or the
   playground. Instead, where a term is checked against an expected type
   and the two don't unify, and either side mentions an error hole, the
   term is silently replaced by a new error hole of the expected type. Lean
   does this with its synthetic `sorry` [from memory]. What flows on is
   always well typed. (Fable's safeguard 2.)
2. **Error sites that inspect a type's head without unifying** return an
   error hole, silently, when that head is flagged: a field or method after
   `.`, applying something that isn't a function, `match` on an unknown
   scrutinee type, instance search, "can't infer this type", and the
   goal-dependent sites of §4.3. Expect **20–30 such sites over time**
   [estimated, Fable], not the 6–10 I first guessed; S1 does the ones the
   oracle (§6) shows first.
3. **A backstop at emission**: one place where the elaborator's errors are
   collected drops any error whose types mention a flagged hole. It catches
   what layer 2 hasn't reached yet; each error it drops is a candidate for a
   layer-2 site. (Fable's safeguard 3.)

Plus two rules in the parser's output:

- **Names a broken line may have bound.** R3 keeps a `let`'s name when it
  got that far. Otherwise the `Error` node lists the lowercase names in its
  skipped tokens. An unknown name later in the same block that is on that
  list is not reported: it may have been bound by the line that broke. My
  call.
- **An incomplete match** (R4 dropped an arm whose patterns broke) skips
  the missing-cases and unreachable-arm checks. So the quick fix "add
  missing arms" (`lsp/src/arms.rs`) doesn't offer itself there either.

What is still reported in a broken declaration is everything that doesn't
depend on a gap: line 3's `"text"` against `Nat`, an unknown name on a good
line, a wrong argument to a good call. That is D3563's "errors … for its
other lines".

### 4.3 Checking against an unknown goal

A proof-step gap's `rest` is checked against a fresh error hole as its
expected type. The goal-dependent sites see a flagged goal and give an
error hole silently: `rewrite`'s search for its left side (no
`E-REWRITE-NO-GOAL`), `rfl` and other closing terms, a `calc` chain's ends
against the goal, and the final mismatch against the expected type (layer
1 above). Everything else in `rest` is checked as usual, so a misspelt
hypothesis, a wrong argument to a lemma or a step's relation against its
written sides is still reported, and every name gets its hover. This mode
is just layers 1–2 meeting an expected type that is a hole; it is built
with R3's split in S2.

### 4.4 What doesn't change

The check cache (a namespace with a syntax error has no key), importers
(skipped with one `E-NAMESPACE-FAILED`, D2785), tests (a failed declaration
never runs), and the trust story (no kernel term). A broken declaration's
check now costs what a good one's does, where today it costs nothing past
the header. That is per keystroke in the declaration being typed, and
under the time of checking the rest of the file [estimated].

### 4.5 What other tools do [from memory, Fable's review]

Lean 4 is closest to this design: it elaborates the partial syntax up to
the error, puts a synthetic `sorry` in the gap, and suppresses errors that
mention one when they are emitted. Agda and Idris stop at the file's first
syntax error. rust-analyzer, rustc and TypeScript recover per statement
and give the gap an error type. TypeScript's `tsc` may print only the
syntax errors when there are any [medium confidence], while its editor
server shows both (D3581).

## 5. The editor, the playground, the formatter

**Free, once the checker sees the body:** hover, go to definition, semantic
colouring, inlay hints and signature help in the broken declaration's good
lines. The outline and folding cover the whole declaration, since the
declaration's span now includes its body. All of these come from the
navigation index and the module.

**Changes in `crates/lsp`** [source; stage S4]:

- `WorkspaceNav::store` and completion's locals (`lib.rs:563`,
  `complete.rs:97–150`): take locals from the current check first, and from
  the last parsed one only for a position inside an `Error` node that the
  current check has no scope for. The rule that keys the fallback on "any
  `E-PARSE` in the file" becomes "this position is in a gap".
- Member completion after `.` (`lib.rs:1755`): unchanged at first. The
  dummy-name re-check still works. Once `h.` is a field with a missing name
  that the check records with `h`'s type, it can answer without the
  re-check (a follow-up, not needed).
- `goals_kept` (`lib.rs:5023`): still needed for declarations that fail
  whole (a broken header). Narrow it to those.
- Hover on a gap: the "didn't parse; expected `T`" text, and the goal
  view at a proof-step gap (§4.1).
- LSP tests (`crates/lsp/tests/it/features.rs`): hover on a name in the
  line after a broken one; the goal at a broken `rewrite` step; completion
  of a local bound above a broken line;
  the outline's range covering a broken body; no diagnostic other than the
  syntax error for a use of a broken `let`'s name.

**`crates/web`:** nothing beyond the server. One playground test (the
existing worker tests) that a broken declaration still gets hovers. The
lossless tree's readers in the playground, if any, need the `Error` nodes
handled; I didn't check whether there are any.

**The formatter keeps refusing** a file with any syntax error (D1021,
D2783, both decided; not reopened here). Error nodes don't change the
reasons Matt gave. Its refusal now lists every syntax error instead of the
first. If format-on-save while typing becomes wanted, the tree now makes
"format the declarations without `Error` nodes, keep the others as
written" a small change. The formatter already keeps a declaration that
fails its own check as written (`fmt/src/lib.rs:7–9`).

## 6. Stages

Lane hours [estimated]. Parser and checker work is core language work, so
Opus (D2506). The tests are named tests and the one reject example each
lane adds. The verifier runs the example kinds and hash snapshots.

**The one-line-break oracle** (Fable's, S1's gate, then every stage's):
take every correct declaration in the repo, break one line of it at a
time (drop the line's last token; insert a stray `)` mid-line), and check
it. The syntax error is expected; **any other error reported is a false
one**, since the declaration was correct. The tool (a `dev` subcommand,
built in S1) counts breaks and false errors per recovery point and lists
the worst. A lane runs it on the one namespace it is working in; the run
over the repo is an Overmind job. The budget: at most 2% of breaks give a
false error at any point [estimated target; reset from S1's first run],
and no later stage raises a point's rate.

| Stage | What | Gate | Needs SW-3160? | Model | Hours |
|---|---|---|---|---|---|
| **S0** | Groundwork, no behaviour change: the modes struct, an error list on `Parser`, `recover_to(snapshot)` (modes, `open`), strict entry points fail on a non-empty list (SW-1982, rescoped). Fold in SW-3185: a declaration that doesn't lex is an `Error` root over its raw text | Parser unit tests by name; hash snapshots unchanged; `dev tree --spans` on one std namespace | No | Opus | 3–5 |
| **S1** | `Expr::Missing` and the checker (§4.1–4.2): error holes; the parser's failed flag replacing `body_error` as the reason a declaration fails; the error hole at a mismatch (strict unifier); the first silent sites; the emission backstop; the editor goal at R1 gaps. Parser points **R1 and R6**. The oracle tool | `examples/reject/recover-ran-out.sw` (a broken `let` and a type error on a later line, both reported and nothing else); `recover-body.sw`; `def f: Nat :=` is not a primitive; the crash probe (a gap in a type position, then arithmetic on the name it binds: no panic, no false error); the fuzz invariant "a declaration with a syntax error has no kernel term or hash"; **the oracle over the repo within budget** (Overmind) | No | Opus | 9–12 |
| **S2** | **R3** with D3580's split (binding lines; proof-step lines as `Gap` nodes), **R5** (calc), and **checking against an unknown goal** (§4.3); a broken `let`'s name kept; the "may have been bound" names | `recover-two-lines.sw` (two broken lines and one type error give three errors); `recover-rewrite-step.sw` (the proof scenario: no error on `rfl`, none on line 1); the oracle within budget per point | No | Opus | 6–9 |
| **S3** | **R4** (arms, incomplete match), **R2** and **R2b** (brackets, stray closers); the operand hazard test (§3.2) | `recover-arm.sw`, `recover-stray.sw`; the plain-words scenarios as reject examples; the oracle within budget per point | No | Opus | 5–7 |
| **S4** | The editor (§5): locals from the current check, gap hover, the goal at proof-step gaps, `goals_kept` narrowed, LSP tests; the playground test | LSP tests: hover after a broken line; goal at a broken step; completion of a local above it; outline range | No (after S2) | Sonnet | 4–6 |
| **S5** | Recovery corpus and typing simulation (SW-1985, rescoped): cut a sample of declarations at each token and check that every other declaration's tree is unchanged, and that a cut past the header keeps the declaration; the fuzz invariant "errors are empty exactly when the tree has no `Error` node and no missing child" | The new corpus test by name; the fuzz test at its default count. The repo-wide simulation is for Overmind | No (after S3) | Sonnet | 4–6 |
| **S6** (optional) | R1 in a header's result type: the body is checked for hovers, with no stand-in | One reject example | No | Opus | 3–4 |
| **S7** | Lowering of `Error` and `Gap` nodes and absent children, inside SW-3160's lowering lane; the parser's direct `Missing` construction goes with step 4 | SW-3160's oracle over the S5 corpus | **Yes** (is part of it) | Opus | +3–5 on SW-3160 |

Order: S0, S1, S2, then S3 and S4 side by side, then S5. Total S0–S5:
31–45 lane hours (was 27–39), against D3563's 15–25. The increase is
Fable's safeguards and the oracle in S1, and the unknown-goal mode in S2.
**Recommendation (my call, sequencing): go before SW-3160.** In A2
the recovery logic lives in the parser anyway (§3.1), so going first
throws away only S7's few lines. D3563 can then land while lowering is
still at the design stage. If SW-3160 is already running when S1 starts,
S7's rules (the `Gap` node included) should be in its brief so lowering is
written knowing about gaps.

## 7. Risks and what I didn't check

- **Cascades that get through** are the main risk. Each one is an extra
  error that goes away when the syntax error is fixed: noise, never a wrong
  answer. The oracle measures them from S1 on, per recovery point, and the
  emission backstop catches what the silent sites miss. A real error
  hidden behind a gap shows up once the syntax is fixed.
- **A wrong answer is ruled out by the parser's flag**, not by the holes
  (§4.1): recoveries that leave no hole can't make a kernel term. S1's
  fuzz invariant watches it.
- **A crash in the editor** from an ill-typed value reaching the
  evaluator. The strict unifier and the error hole at a mismatch keep
  every value well typed; S1's crash probe tests the likeliest path.
- **Misclassified lines** (§2.3): a proof-step line read as a binding line
  gives false goal errors below it; the other way round only loses some
  checking. The oracle shows the first kind.
- **An error hole leaking into a stand-in**, through a metavariable shared
  with the signature. The signature's metavariables are settled before the
  body is checked [source, from memory of the order; not rechecked]. S1
  should assert that a stand-in never contains a flagged metavariable.
- **Mode-field restoration bugs** give strange parses of later lines in a
  broken declaration. That is safe by the rule in §2.1, but noisy. The
  oracle and S5 are the net.
- **Agents see more errors per run** from `check` (D3581). If cascades
  leak, an agent may chase one. Mitigation: the oracle's budget.
- Not checked: the site count in §4.2 (Fable's estimate); the other
  tools' behaviour in §4.5 (from memory); whether anything in `crates/web`
  or `crates/js` reads the lossless tree; and the playground in a browser.
  All probes were `check` and `dev tree` on single files; no editor session.

## 8. Questions for Matt

**D3580, decided (Matt, 14 Nov 2026): "I'm happy with Fable's proposed
split."** A broken binding line costs only that line; a broken proof-step
line becomes a gap over the rest of its block, whose lines are read and
checked against an unknown goal (§2.3, §4.3). With it, Fable's three
safeguards (§4.1, §4.2) and the oracle as S1's gate (§6). It replaces
D2780 point 2 for binding lines and keeps it, with the rest still read, for
proof-step lines.

**D3581: the extra errors show everywhere, in `stitchwort check` as well as
the editor.** *Decided (Matt, 14 Nov 2026): "D3581, yes."* *The problem:* D3563 is about the editor, but the checker
under VS Code, the playground and `check` is one checker. Showing the extra
errors only in the editor would mean two behaviours to test, and the
reject examples couldn't show them. *The change:* `check` reports every
syntax error and the other errors of a broken declaration, as the editor
does. The goal at a gap stays editor-only (D2781). *What it should do:* an
agent or a person running `check` sees every syntax error in a declaration
in one run, not one per run: with five broken lines, one run instead of
five. The risk is a leaked cascade error. *Fable's TypeScript point*
(`tsc` may print only syntax errors when there are any, while its editor
shows both; medium confidence) is a real precedent for the alternative,
but it doesn't change the recommendation: the oracle now measures the
false-error rate before any stage merges, which `tsc` has no equivalent
of, and the reject examples need the errors in `check`'s output. If the
oracle stays over budget, the fallback is TypeScript's: `check` prints
every syntax error and holds back the other errors of a broken
declaration. **[rec: yes, the same everywhere]**

**Decided here as implementation** (say if you disagree): R1 gaps have no
node, only an absent child. A proof-step gap is a `Gap` node, and lines
are classified by their form (§2.3). Errors are at most one per line. "May
have been bound" names are not reported as unknown. An incomplete match
skips its coverage checks. The modes struct is restored by a snapshot at
each point. Recovery goes before SW-3160's lowering. The formatter keeps
refusing (D1021 stands). Recovery stays out of `type`, `interface` and
`ability` (D2782 stands).

## Findings worth tickets

- **The outline and folding lose a broken declaration's body today**
  [measured: the full range ends at the header, `[0,0,0,44]`]. S1 fixes it
  as a side effect. Folding over the declaration's column-0 range, which
  is known without parsing, could fix it now in about an hour [estimated].
- **R1 errors point at the next line, not where the text ran out**
  [measured on every R1 probe]. This is independent of recovery and could
  be done alone. It is in S1 here.
- **A kept signature's lossless tree has no structure:** an `Error` root
  with every token flat, even though the header parsed [measured]. Header
  marks are discarded with the failed body. S0 or S1 keeps them.
- **parse-recovery.md's status should be "superseded in part"** by this note
  (its Design B decision D2780 point 2, its "no lossless tree" premise
  replaced by D3562). Its tickets SW-1982 to SW-1986 should be rescoped to
  S0–S5 or closed. SW-1873 looks done by SW-3156: worth closing after a
  check.
- **For the SW-3160 lane:** lowering must turn `Error` nodes, `Gap` nodes
  (§2.3) and absent required children into `Expr::Missing`, `Stmt::Error`, missing arm bodies
  and incomplete matches (§3.1), and its oracle should include the S5
  corpus.
- `syntax-tree-architecture.md` isn't listed in `docs/proposals/README.md`.
