# Syntax error recovery: working through a broken declaration

**Status:** design note, 14 November 2026 (SW-3161, for D3563). Paper lane:
nothing is built. Waits for Matt on D3580 and D3581 ([§8](#8-questions-for-matt)).
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

**What it should do** (the scenarios are probes of today [measured]; the
"after" column is the design):

| You are typing | Today, in the editor and `check` | After |
|---|---|---|
| **A half-typed line in a proof.** Line 2 of a four-line `let` block reads `let k := h.` | One error, "expected a field name after `.`". Lines 1, 3 and 4 have no hover. The type error on line 3 (`let bad: Nat := "text"`) isn't shown. The outline item stops at the header | The same syntax error, plus line 3's type error. Hover works on every line, `h` included, and completion offers `h` and the parameters from this check. `k` is in scope below with an unknown type, and nothing that uses `k` is reported |
| **A missing `)`.** `let a := (xs.length + 1` with the next line starting `let b` | "expected `)`, but the line starting with `let` … starts a new statement", pointing at line 3 | "expected `)`" at the end of line 2, with a second label on the `(`. The bracket counts as closed there, so `a: Nat` is checked and shows on hover. Line 3's own type error is shown too |
| **An unfinished `match` arm.** `\| 1 =>` with nothing after it, then `\| _ => "many"` in a `Nat` function | "expected an expression, but found `\|`" on the next arm, and nothing else | "expected an expression after `=>`" at the end of the `\| 1 =>` line. The other arms are checked, so `"many"`'s type error is shown. The editor's goal view shows `Nat` as what the empty arm must give |
| **A stray token.** `let a := n + ) 1` | "expected an expression, but found `)`", and nothing else in the declaration | "unmatched `)`" on the `)`. The rest of the line reads as `n + 1`, and later lines are checked |
| **Two broken lines** (`let a := n +` and `let b := (n`) | Only the first error | Both errors, and the type errors of the other lines |

Nothing changes for a file without syntax errors: same trees, same hashes,
same messages. A file with a syntax error still never passes, is never
cached, never runs its tests, and is never formatted (D1021).

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
| **R3 Block line** | A statement of a block fails | The next stop of this block, or a token that ends blocks (`\|`, `where`, `:=`, `decreasing`, `unfolding`; `ends_blocks`, `:2688`) | `Error` node over the failed line, inside the `Block` | Later lines are parsed and checked (D3580). If the line was a `let` whose name (or simple pattern) was read before the error, the name stays bound to a missing value |
| **R4 Arm** | An arm of a definition, a `match`, a clause lambda or a handler fails | The next `\|` at the arms' column, or the end of the arms | `Error` node over the arm, or over its body | Patterns read: the arm is kept with a missing body. Patterns broken: the arm is dropped, and the match is marked *incomplete*, so coverage isn't checked (§4.3) |
| **R5 Calc step** | A step of a `calc` fails | The next `_` starting a line (`starts_calc_step`) | `Error` node over the step | The chain carries on from the step's written right side if it parsed, otherwise from a missing one |
| **R6 Body** | Nothing inside caught it: the `:=` body or the arms as a whole | The end of the declaration | `Error` node over the rest | Replaces today's "signature only" (`body_error`): one equation with the header's patterns and a missing body. Never no body, which would make a primitive (`declarations.rs:423`) |

**Not recovered** (as today, D2782): errors in a header's parameters and
inside `type`, `interface`, `ability`, `namespace` and `import`. The
declaration fails whole and its names go in `Module::failed`. The one
exception is R1 in a header's result type (`def f (n: Nat):` with nothing
more), which can come in a later stage (S6 in §6): the body is then checked
against an unknown type for its hovers, and the declaration gives no stand-in.

### 2.3 What layout buys

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

### 2.4 Parser state at a recovery point

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

### 2.5 How many errors are reported

One per recovery point that fires. What a point skips isn't parsed, so it
can't produce more. In practice that means at most one syntax error per
line, and no limit per declaration [estimated: a line that triggers R2b
and then R3 would give two; I'd merge errors that land on the same line
into the first]. My call. A cap per declaration isn't needed: every
reported error is at a different place the author has to visit.

### 2.6 Error positions

An R1 error points at the end of the last token read, which is usually
where the cursor is. If a stop ended the expression, a second label goes on
the token that ended it. Today the error points at that token, often on the
next line (the probes show this on every R1 case). A missing closer gets a
second label on its opening bracket. The current "the line starting with …
starts a new statement" wording becomes a note on the R1 error, since it
still explains *why* the line ended. My call; the 82 reject examples with
`E-PARSE` [measured] get new snapshots (migration cost doesn't count, D2303).

## 3. Error nodes in the lossless tree

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
node: `Expr::Missing(span)`, a `Stmt::Error`, an `Alt` with a missing body,
or a `Match` with `incomplete: true`. **After lowering**, the parser only
records marks, and lowering turns an `Error` node or an absent required
child into the same compiler nodes. The recovery logic (where to resume and
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

### 4.1 The node

`Expr::Missing(Span)` in `ast.rs` (as in parse-recovery.md; a variant
rather than a flag on `Goal`, so every match on `Expr` is made to handle
it). The elaborator handles it like `Expr::Goal` (`check.rs:2108, 5004`):

- **Checked against `T`**: a frozen metavariable applied to the scope, as
  `goals::hole` makes, flagged as an *error hole*. It isn't printed as a
  goal diagnostic.
- **Inferred**: its type is a fresh metavariable, also flagged.
- **The declaration fails**, not "unfinished": the zonk fails on the frozen
  metavariable as for `?`, and the module turns that into `E-UNPARSED-BODY`
  when the declaration has an error hole. So the signature stands in for it
  and the driver folds the error into the parser's (D2781; today's path,
  `module.rs:3020`, `driver.rs:1060`). It never reaches the kernel.
- **The goal at an R1 gap** (the place you are typing) goes to the editor's
  goal view and hover, not to `check`'s output (D2781, decided). Gaps over
  skipped tokens (R2–R6) show no goal; hovering over them shows "didn't
  parse; expected `T` here" when `T` is known.

### 4.2 Stopping the cascade

Two mechanisms, both at the source of the errors rather than filtered
afterwards:

1. **An error hole equals anything in the elaborator's unifier**
   (`elab/src/unify.rs:56`). When one side is headed by a flagged
   metavariable, the pair succeeds without solving anything, or by solving
   the other side's unknown to the hole, which spreads the flag. This is
   rust-analyzer's `{unknown}` and Lean's synthetic `sorry`. It is safe
   because only the elaborator's unifier does it: the kernel is not
   touched, and a declaration holding an error hole never reaches the
   kernel. A unifier test of "can these be equal" (used to choose between
   ways of elaborating) will pick the first way when a hole is involved.
   That makes types shown inside a broken declaration slightly off at
   worst, and only there.
2. **A few error sites inspect a type's head without unifying**: a field
   or method after `.`, applying something that isn't a function, `match`
   on an unknown scrutinee type, instance search, and "can't infer this
   type" at the end. Each returns another error hole, silently, when the
   head it looks at is flagged [estimated: 6–10 sites; S1 counts them
   using the reject corpus].

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
depend on the gap: line 3's `"text"` against `Nat`, an unknown name on a
good line, a wrong argument to a good call. That is D3563's "errors … for
its other lines".

### 4.3 What doesn't change

The check cache (a namespace with a syntax error has no key), importers
(skipped with one `E-NAMESPACE-FAILED`, D2785), tests (a failed declaration
never runs), and the trust story (no kernel term). A broken declaration's
check now costs what a good one's does, where today it costs nothing past
the header. That is per keystroke in the declaration being typed, and
under the time of checking the rest of the file [estimated].

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
- Hover on a gap: the "didn't parse; expected `T`" text (§4.1).
- LSP tests (`crates/lsp/tests/it/features.rs`): hover on a name in the
  line after a broken one; completion of a local bound above a broken line;
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

| Stage | What | Gate | Needs SW-3160? | Model | Hours |
|---|---|---|---|---|---|
| **S0** | Groundwork, no behaviour change: the modes struct, an error list on `Parser`, `recover_to(snapshot)` (modes, `open`), strict entry points fail on a non-empty list (SW-1982, rescoped). Fold in SW-3185: a declaration that doesn't lex is an `Error` root over its raw text | Parser unit tests by name; hash snapshots unchanged; `dev tree --spans` on one std namespace | No | Opus | 3–5 |
| **S1** | `Expr::Missing` and the checker (§4): error holes, the unifier rule, the silent sites, failure as `E-UNPARSED-BODY`, the editor goal at R1 gaps. Parser points **R1 and R6** | `examples/reject/recover-ran-out.sw`: a broken `let` line and a type error on a later line, both reported and nothing else; `examples/reject/recover-body.sw`; a `def f: Nat :=` must not become a primitive | No | Opus | 6–8 |
| **S2** | **R3** (block lines) and **R5** (calc steps); a broken `let`'s name kept; the "may have been bound" names | `examples/reject/recover-two-lines.sw`: two broken lines and one type error in one declaration give three errors | No | Opus | 5–7 |
| **S3** | **R4** (arms, incomplete match), **R2** and **R2b** (brackets, stray closers); the operand hazard test (§3.2) | `examples/reject/recover-arm.sw`, `recover-stray.sw`; the four scenarios of "In plain words" as reject examples | No | Opus | 5–7 |
| **S4** | The editor (§5): locals from the current check, gap hover, `goals_kept` narrowed, LSP tests; the playground test | LSP tests: hover after a broken line; completion of a local above it; outline range | No (after S2) | Sonnet | 4–6 |
| **S5** | Recovery corpus and typing simulation (SW-1985, rescoped): cut a sample of declarations at each token and check that every other declaration's tree is unchanged, and that a cut past the header keeps the declaration; the fuzz invariant "errors are empty exactly when the tree has no `Error` node and no missing child" | The new corpus test by name; the fuzz test at its default count. The repo-wide simulation is for Overmind | No (after S3) | Sonnet | 4–6 |
| **S6** (optional) | R1 in a header's result type: the body is checked for hovers, with no stand-in | One reject example | No | Opus | 3–4 |
| **S7** | Lowering of `Error` nodes and absent children, inside SW-3160's lowering lane; the parser's direct `Missing` construction goes with step 4 | SW-3160's oracle over the S5 corpus | **Yes** (is part of it) | Opus | +3–5 on SW-3160 |

Order: S0, S1, S2, then S3 and S4 side by side, then S5. Total S0–S5:
27–39 lane hours, against D3563's 15–25. The difference is per-line
recovery (D3580) and the cascade work, which the earlier estimate didn't
include. **Recommendation (my call, sequencing): go before SW-3160.** In A2
the recovery logic lives in the parser anyway (§3.1), so going first
throws away only S7's few lines. D3563 can then land while lowering is
still at the design stage. If SW-3160 is already running when S1 starts,
S7's rules should be in its brief so lowering is written knowing about
gaps.

## 7. Risks and what I didn't check

- **Cascades that get through** are the main risk. Each one is an extra
  error that goes away when the syntax error is fixed: noise, never a wrong
  answer. The reject examples' snapshots show them, and S5's simulation
  finds more. A real error hidden behind a gap shows up once the syntax is
  fixed.
- **The unifier rule could leak.** An error hole solved into a metavariable
  shared with the signature would put a gap into the stand-in. The
  signature's metavariables are settled before the body is checked
  [source, from memory of the order; not rechecked]. S1 should assert that
  a stand-in never contains a flagged metavariable.
- **Mode-field restoration bugs** give strange parses of later lines in a
  broken declaration. That is safe by the rule in §2.1, but noisy. S5 is
  the net.
- **Agents see more errors per run** from `check` (D3581). If cascades
  leak, an agent may chase one. Mitigation: the reject snapshots and S5.
- Not checked: the exact count of error sites in §4.2; whether
  `goals::hole`'s frozen metavariable already gets through `unify` without
  a mismatch error at every call site (`?` is used where the type is known,
  so that path is less exercised); whether anything in `crates/web` or
  `crates/js` reads the lossless tree; how SW-3160's design note
  (`docs/proposals/syntax-tree-lowering.md`, being written beside this one)
  plans to represent absent children; and the playground in a browser. All
  probes were `check` and `dev tree` on single files; I ran no editor
  session.

## 8. Questions for Matt

**D3580: a broken line costs only that line; the lines after it are still
checked.** *The problem:* the earlier plan (D2780, point 2, decided on 7
Nov) put one hole over the broken line *and everything after it in its
block*. That shows what is left to prove at that point, but it keeps the
blank-declaration problem for every line below the cursor. D3563 asked for
the opposite. *The change:* R3 skips only the broken line. A `let` it
broke keeps its name, with an unknown type, and later lines are checked
and keep their hovers and errors. When the broken line is the last one,
the goal you see is the same as under the old plan. *What it should do:*
in the half-typed-line scenario, lines 3 and 4 keep hovers and line 3's
type error shows [design; today none do, measured]. It costs about 2–3
lane hours more than the old plan, mostly in cascade suppression
[estimated]. **[rec: yes, per line]**

**D3581: the extra errors show everywhere, in `stitchwort check` as well as
the editor.** *The problem:* D3563 is about the editor, but the checker
under VS Code, the playground and `check` is one checker. Showing the extra
errors only in the editor would mean two behaviours to test, and the
reject examples couldn't show them. *The change:* `check` reports the
syntax errors and the other errors of a broken declaration, as the editor
does. The goal at a gap stays editor-only (D2781). *What it should do:* an
agent or a person running `check` sees every syntax error in a declaration
in one run, not one per run. With five broken lines, that is one run
instead of five. The risk is a leaked cascade error, which the snapshots
watch for. **[rec: yes, the same everywhere]**

**Decided here as implementation** (say if you disagree): R1 gaps have no
node, only an absent child. Errors are at most one per line. "May have been
bound" names are not reported as unknown. An incomplete match skips its
coverage checks. The modes struct is restored by a snapshot at each point.
Recovery goes before SW-3160's lowering. The formatter keeps refusing
(D1021 stands). Recovery stays out of `type`, `interface` and `ability`
(D2782 stands).

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
- **For the SW-3160 lane:** lowering must turn `Error` nodes and absent
  required children into `Expr::Missing`, `Stmt::Error`, missing arm bodies
  and incomplete matches (§3.1), and its oracle should include the S5
  corpus.
- `syntax-tree-architecture.md` isn't listed in `docs/proposals/README.md`.
