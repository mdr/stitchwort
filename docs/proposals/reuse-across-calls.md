# Reuse across calls: letting a cell taken apart in one function be rebuilt in another

SW-2384, 8 November 2026. Paper lane: code, papers and other compilers' source
read, nothing built or run. Status: proposed; the questions in §7 are open.

Labels: **[measured]** a number from a run (the run is named), **[cited]** read
in the source or paper named, **[checked]** read in our code for this note,
**[inferred]** my reasoning, untested, **[not re-checked]** from memory of
another system, not looked up today.

**In short.** Today a cell can only be reused by a constructor in the same
compiled body as the `match` that took it apart. In `Std.Map.Tree` the node is
taken apart in `insertWith` or `minView` and rebuilt two calls further down, in
`rebuild`, so dijkstra builds about 25 M fresh `Bin` cells and reuses almost
none. The fix proposed here is in the compiler, not std. When the cell taken
apart is not rebuilt locally, its emptied cell (our *reuse token*) is passed
as a hidden extra argument to a copy of the callee that rebuilds it, and so on
down the calls. Tokens are already ordinary values in registers, so this
needs no new instruction, no change to the native calling convention and no
`unsafe` code. Step counts don't change. Estimated gain: 8–15% on dijkstra.
The same change helps every persistent structure and every record or tree
updated through a helper, including user code. Reshaping std (SW-2383)
becomes unnecessary for reuse. What reshaping would still win, fewer calls
per tree level, is better got from targeted inlining afterwards if a
measurement shows it's worth it (§6).

## 1. The problem, with our numbers

**Where reuse happens today** **[checked]**, `crates/rt/src/code.rs`:

- A `match` whose scrutinee is dead in an arm compiles to `Instr::Unpack`.
  The unpack keeps the emptied cell as a token only if `builds(&arm.body,
  arity) > 0`, that is, only if the arm itself contains a constructor with as
  many fields. `Expr::Ctor` claims a token from `self.tokens` of the body
  being compiled.
- `builds` counts only `Expr::Ctor`. A `Call` contributes only what its
  arguments build, so a constructor inside a callee is invisible.
- A token is a plain `Value` in a register: the cell with its fields set to
  `Erased` when it was unique, or `Erased` when it was shared
  (`machine.rs`, `Instr::Unpack`; native `n1.rs` `unpack`/`ctor_reuse` do the
  same inline). `CtorReuse` checks at run time that the token is a `Data`
  cell with as many fields and a count of 1, and otherwise allocates.

**What that costs on `Std.Map.Tree`** (SW-2371, interpreter counts on 2021
day 15's real input, **[measured]** there):

| Where the `Bin` is built | Fresh | Reused | Why not reused |
|---|---:|---:|---|
| `Map.Tree.rebuild`, `Keep` arm (`bin l key value r`) | 22.29 M | 0 | The node was unpacked in `insertWith`/`minView`; `rebuild` is two calls down (`balance` → `rebuild`). |
| `singleL`/`doubleL`/`doubleR` rotations | 2.21 M | 0.35 M | Each rotation reuses the subtree it unpacks itself, but not the caller's node. |
| `insertWith`'s `Tip` and `Equal` arms | 1.22 M | 0 | `Equal` builds in the lifted `%match1` body, not where the node was unpacked (below). |
| **Total** | **≈ 25.7 M** | **0.35 M** | |

Of dijkstra's 40.4 M cells, 25.7 M are these `Bin`s. Allocation and freeing
are 33% of its self time (SW-2369 **[measured]**). The two causes that kept the
cells shared, the queue held twice and arguments copied instead of moved,
are fixed (SW-2382, SW-2388). After SW-2388, `insertWith` and `minView`
meet unique cells on every step of the p1 micro-benchmark, and dijkstra runs
at 44.0 G instructions **[measured, SW-2388]**. So the cells are now unique,
and what stands between them and reuse is the function boundary alone.

**The lifted `match`.** The elaborator lifts a `match` written inside an arm
into a definition of its own (`Map.Tree.insertWith.%match1`,
`crates/elab/src/lift.rs`). In the runtime IR that is a separate global.
`opt.rs` inlines the outer `insertWith` (small, and not directly
self-recursive) into `%match1`'s recursive calls. So the `Unpack` of a child
node sits in `%match1`, and the arms that rebuild that node are in the next
`%match1` frame down. Even the `Equal` arm, which builds its `Bin` in plain
sight, is in a different body from the unpack **[checked: `opt.rs` `global`,
`recursive`, `INLINE_SIZE = 24`; consistent with SW-2371's pc listing]**.

**A controlled pair** (in-place-reuse.md §2.2, **[measured]**): the same
unbalanced-tree insert reuses 80.6% of its cells with the constructor in the
arm, and 6.9% with it in a non-inlined helper. On `bench/native/set_nat.sw`,
`Set.fromList` of 1,000 keys reuses 11.7% of cells.

**The std workaround** (SW-2371 fix B, ticket SW-2383) is to build the `Keep`
node inline in `insertWith` and `minView`. It needs `if` instead of `match`,
so that nothing gets lifted, and a lemma `balance l k v r = Bin …` under the
two size tests, so that every theorem that unfolds `balance` can be
re-proved. In a scratch copy that reused 17.7 M of about 25 M `Bin`s and saved
0.45 s of 7.15 s **[measured, SW-2371]**. This is the "distorting our code"
Matt would rather avoid: the algorithm is written around a limit of the
optimiser.

## 2. How other languages do it

### 2.1 Lean 4

- **Reset/reuse runs late and is intraprocedural.** In the current compiler
  (LCNF), `insertResetReuse` is the second impure pass, after every
  inlining (`simp`, run five times) and specialisation pass of the base and
  mono phases, and before `inferBorrow`, `explicitRc` and `expandResetReuse`
  (`src/Lean/Compiler/LCNF/Passes.lean`) **[cited]**. The pass is
  `Pass.mkPerDeclaration`: one body at a time. Two constructors can share a
  cell when they have the same size, `usize` and `ssize`. A second run with
  `relaxedReuse` allows different types, a `PSigma.mk` cell for a `Prod.mk`
  for example (`src/Lean/Compiler/LCNF/ResetReuse.lean`) **[cited]**. This is
  the algorithm of Ullrich and de Moura, "Counting Immutable Beans" (IFL 2019),
  read for compilation.md card C1 **[not re-read]**.
- **Matches are inlined back.** Lean also compiles a `match` to an auxiliary
  `match_<n>` definition. The compiler's `toLCNF` inlines it
  (`inlineMatcher`), making each alternative a join point so that `simp`
  inlines its single use (Lean API docs, `Lean.Compiler.LCNF.ToLCNF`)
  **[cited]**. So the problem in §1 with our lifted `%match1` doesn't arise
  in Lean.
- **Balancing helpers are inlined, and also hand-fused.**
  - `Lean.RBNode`: `balance1` and `balance2` are `@[inline]`, and `ins` is
    `@[specialize]`. `ins` calls `balance1 (ins a kx vx) ky vy b`
    (`src/Lean/Data/RBMap.lean`) **[cited]**.
  - `Std.DTreeMap`, Lean's weight-balanced tree, uses the same Adams
    algorithm as our `Map.Tree`. Its `balanceL`/`balanceR` are `@[inline]`
    and build `.inner` nodes directly in every arm, rotations included. The
    file says the separate `singleL`/`doubleL`/`bin` definitions "are not
    actually used by the tree map implementation", only by the proofs
    (`src/Std/Data/DTreeMap/Internal/Balancing.lean`) **[cited]**.

  So Lean gets reuse in its trees by a combination: the compiler inlines
  (an attribute asks it to), and std's code is written in the fused shape
  that inlining needs, with proofs relating it to the readable version.

### 2.2 Koka

- **Perceus** (Reinking, Xie, de Moura, Leijen, PLDI 2021; MSR-TR-2020-42 v4):
  reuse analysis is per function, after inlining. For the red-black tree:
  "Moreover, the compiler inlines the bal-left function. At that point,
  every matched Node constructor has a corresponding Node allocation" (§2.4)
  **[cited]**. Reuse specialisation (writing only the changed fields) and
  drop specialisation are local too.
- **Frame-limited reuse** (Lorenzen and Leijen, ICFP 2022; MSR-TR-2021-30 v2)
  places the token by drop-guided analysis. It proves that this holds at
  most a constant number of cells per stack frame, because "before a reuse
  token is used there might be a recursive call" (`map`'s token is held
  across `map(xx, f)`). Lean's original algorithm D is not frame-limited
  (§4.1) **[cited]**. Their analysis again "assume[s] that the lbal and rbal
  functions get inlined" (§2.2.1) **[cited]**.
- **FP², fully in-place** (Lorenzen, Leijen, Swierstra, ICFP 2023;
  MSR-TR-2023-19):
  - A `fip` function may build a constructor only by spending a *reuse
    credit* ⋄k that a destructive `match!` produced in the same body (§2,
    the `reuse` and `dmatch!` rules).
  - Credits cannot be passed implicitly to a call. When an algorithm needs
    one in a callee, the programmer passes an explicit value of the right
    size: `fip fun cons(x : a, u3 : unit3, …)` (§4, "passing reuse credits
    to functions") **[cited]**.
  - For red-black insertion, FP² rewrites the algorithm with a zipper, so
    that rebalancing happens while the tree is rebuilt from the zipper
    (§4.1) **[cited]**.

  So Koka's guarantee comes from reshaping the code, in the open, with the
  checker's help.

### 2.3 Others

- **Mercury** (Mazur, Ross, Janssens, Bruynooghe, "Practical aspects for a
  working compile time garbage collection system for Mercury", 2001,
  arXiv cs/0110037) **[cited]**:
  - The closest precedent for passing reuse across calls. A procedure gets
    a *reuse version* that reuses the cells of an argument the caller has
    proved dead ("indirect reuse"). Calls are redirected to it whenever its
    reuse conditions hold.
  - It is limited to two versions per procedure, one with no conditions
    and one with all reuses (§3.3).
  - The decision is static (alias analysis). The direction is also
    reversed: the callee takes apart the caller's dead data. In ours the
    caller's dead cell is used by the callee's constructor.
- **Roc** **[cited, thin]**: Lean-style reset/reuse in its mono IR
  (`insert_reset_reuse_operations`), with "update modes" decided by its
  Morphic alias analysis for in-place `List` updates. Folkert de Vries wants
  reuse decoupled from reset so that it works for binary trees too (Roc
  Zulip, "Tail Recursion Modulo Cons", 2023). I found no sign that it crosses
  calls.
- **Swift** **[not re-checked]**: ARC with copy-on-write collections written
  by hand around `isKnownUniquelyReferenced`. There is no automatic reuse of
  enum cells, so the library is shaped around uniqueness.
- **Clean** **[not re-checked]**: uniqueness types make destructive update a
  typing fact. It is static, and the programmer annotates. compilation.md
  already ruled uniqueness types out for us, because our effects can resume
  twice.
- **GHC and OCaml** **[not re-checked]**: no reference counts. A generational
  copying collector makes a fresh allocation a pointer bump and a dead node
  free, so there is nothing to reuse. They spend the effort on inlining,
  case-of-case and worker/wrapper instead. OCaml's TRMC
  (`[@tail_mod_cons]`) is the same idea as our `trmc.rs`.
- **Lobster** **[not re-checked]**: compile-time ownership analysis removes
  most count operations. I know of no cell reuse.

### 2.4 Comparison

| System | Where reuse is decided | Crosses a call? | How tree balancing gets reuse | Guarantee |
|---|---|---|---|---|
| Lean 4 | late, per body, after inlining and specialisation | no | `@[inline]` balance helpers; `Std.DTreeMap`'s are also hand-fused | none (dynamic check) |
| Koka (Perceus, FLR) | per body, after inlining; drop-guided placement | no | the compiler inlines `bal-left` | none (dynamic check) |
| Koka `fip` (FP²) | checked per body | only through explicit credit arguments the programmer writes | rewrite with a zipper | static, by the `fip` check |
| Mercury CTGC | static alias analysis | yes: callee "reuse versions" for dead arguments | n/a | static |
| Roc | per body, Lean-style | no (as far as found) | n/a | none |
| Swift, Clean | by hand (COW) / by type (uniqueness) | by hand / by type | written for it | by hand / by type |
| GHC, OCaml | no reuse; cheap allocation by GC | — | — | — |
| **Stitchwort today** | `code.rs`, per body, after inlining | **no** | none (25 M fresh `Bin`s) | none (dynamic check) |
| **Proposed (b)** | `code.rs` plus a variant pass | **yes, hidden token argument** | automatic, std unchanged | none (dynamic check) |

**What this says.** Nobody we can see passes a token across a call
automatically. Lean and Koka don't need to, because their inliners are
built and tuned for this, and their libraries are written in the fused shape
(Lean) or rewritten (Koka `fip`). Our inliner is deliberately small
(`INLINE_SIZE` 24, `FUEL` 200), our std is written for proofs, and Matt wants
std to stay readable. Two things in our runtime make the hidden token cheap
where it would be expensive in Lean's or Koka's C backends:

- A token is already a `Value` in a register. Passing one is passing an
  argument. Nothing changes in the native calling convention or the cell
  layout. in-place-reuse.md §3.2 assumed a custom cell would be needed, but
  that is only for reuse across sizes.
- Every reuse is checked at run time (`CtorReuse` tests the size and the
  count). The analysis can be wrong without being unsound.

## 3. Constraints here

- **Soundness.** A cell may be overwritten only if nothing else can see it.
  Today that is the count test at `Unpack`/`DropReuse` (count 1), plus the
  token register being read by nothing except one `CtorReuse`. Any option must
  keep "the token is never visible to the program": it may only be moved,
  dropped, or spent by `CtorReuse`.
- **Moves (SW-2388).** A token must always be *moved* into a call, never
  cloned. A clone leaves the count at 2, and the callee's `CtorReuse` then
  falls back to allocating. That is sound but wasted. code.rs claims a token
  by removing it from `self.tokens`, so it can't be used twice.
- **Steps (D1253).** A step is a frame entered, and the machine and native
  must run out at the same point. They do, under any option here, because
  both execute the same bytecode. But any option that inlines more changes
  *how many* frames a program enters, as the existing inliner already does.
  The charging rule never changes. Which options change counts is said under
  each.
- **Space.** An unclaimed token holds one emptied cell until its frame ends.
  That is frame-limited in Lorenzen and Leijen's sense, as today's tokens
  held across recursive calls already are.
- **The checker and proofs.** None of this reaches the kernel: everything
  runs on the erased IR after checking. std's statements and proofs don't
  change under the compiler options.
- **JS** uses neither the rt IR nor reference counts, so it is unaffected.

## 4. Options

### (a) Inline the rebalancing helpers before reuse (SW-1812's "inlining for reuse")

**Change.** In `opt.rs` `Simp::call`, allow a larger size for a
non-recursive callee when the call sits in an arm whose scrutinee is dead
and the callee builds a constructor of the scrutinee's arity, as SW-1812
proposes. For `Map.Tree` the chain is `balance` (about 8 nodes), then
`rebuild` (5 arms, about 27 nodes after `bin` is inlined), then `shape`
(about 30 with `size` inlined) **[inferred from the source and `size`]**.
Today only `balance` fits under 24.

**It doesn't work alone**, because of the lifted match (§1). The `Unpack`
of a child is in one `%match1` frame and the `Less` arm that calls `balance`
is in the next. Inlining `balance` and `rebuild` into `%match1` puts the
`Bin` next to the *parent's* `Unpack`, which happened in the caller's frame.
So (a) needs (c) as well, so that `insertWith`'s two matches are one body.

**Soundness.** Nothing new. Inlining is already done, and the existing
local token logic applies.

**Steps.** Change: fewer frames entered (one or two per tree level).
**Native ABI.** None.

**Buys.** On dijkstra, the `Keep` case once (a) and (c) are both in: about
22 M reuses. Rotations stay out (`singleL` and the rest aren't inlined).
`shape`'s inlined reads no longer clone `l` and `r`: about 2
increment/decrement pairs per level go (in-place-reuse.md §2.2's 1.62
increments per cell **[inferred]**). It also saves the frames that SW-2383
would save. Matcher and binary-trees: nothing.

**Limits.** It depends on sizes: a helper a few nodes over the limit, or a
chain one call deeper, loses all reuse. Every call site of `balance` grows
(insertWith, remove, deleteMin, minView, glue: about 6). It gives nothing
for helpers that are recursive.

**Work.** 0.5–1 lane-day, Opus (simplifier correctness), plus (c).

### (b) Pass the reuse token to the callee as a hidden argument (recommended)

**Change.**

1. **A new pass, `crates/rt/src/reuse.rs`**, after `trmc::apply` in
   `lower.rs` (line 186, the only place the IR pipeline is assembled). For
   each function global `g` and constructor size `n`, it decides whether `g`
   *wants* a token of size `n`: on some path, `g`'s body builds a
   constructor of `n` fields that no local token would claim, or calls a
   global that wants one. This is a fixed point over the call graph, and it
   is monotone. The pass is demand-driven: a variant is made only where some
   call site would have a spare token of size `n` in hand. That means a
   `match` arm whose scrutinee is dead, whose arity is `n`, and which calls a
   wanting `g`. It also means the body of a variant, transitively. For each
   such `(g, n)` it makes a copy `g[reuse]` with one more parameter, and
   records it in a side table on `Program`: `reuse_variant[g] = Some((g′,
   n))` and `token_param[g′] = Some((slot, n))`. It follows the existing
   precedents for copies: `opt.rs`'s `specialise` copies (`COPIES` cap 64),
   `trmc.rs`'s twins (which already add hidden parameters, a cell and an
   index), and Mercury's cap of two versions. The variant's IR body is the
   original, its slots renumbered for the extra parameter, which the IR never
   reads.
2. **`code.rs`**:
   - `Compiler::body` for a variant pushes `(n, token_slot)` onto
     `self.tokens` at entry.
   - `builds(e, n)` counts `Expr::Call(g, …)` as 1 when
     `reuse_variant[g]` has size `n`, so an `Unpack` before such a call keeps
     its token (today it gets `NO_REG`).
   - `Expr::Call(g, args)` with a variant and a token of size `n` in hand
     claims the token, the same `rposition` as `Expr::Ctor`, and emits a
     `Call`/`TailCall` to `g′` with the token as a last operand marked
     `MOVE`. With no token in hand it calls `g` as today, so calls without a
     token pay nothing.
   - Prefer local constructors: when an arm has both a local constructor
     and a variant call of size `n`, and fewer tokens than both need, the
     local constructor keeps its token. This is a small change to the claim
     order. It is a heuristic, and safe either way.
   - A token parameter that no path claims is dropped with the frame, as an
     unread parameter is today.
3. **No change** to `Instr`, `machine.rs`, `n1.rs`, `native_abi.rs`,
   `codec`/`wire` or the standalone image format. A variant is a function
   with one more argument, and its `CtorReuse` reads a parameter register
   instead of a temporary. Both runners already do exactly that.
4. **Names.** Variants print as `Std.Map.Tree.balance[reuse]`, as
   specialisations print `[0]` and `[cells]`. `run --profile` and the call
   counts fold them into their definition's row, or show them beside it.

**What it does on `Map.Tree`** **[inferred from the code paths]**:

- In `%match1[reuse]` (from a parent that passed a token), `Less` evaluates
  `insertWith l` first. That is inlined as a `match` on `l`, whose `Unpack`
  makes the child's token and passes it into the recursive
  `%match1[reuse]`. Then `balance[reuse]` gets the parent's token and passes
  it to `rebuild[reuse]`. Its `Keep` arm spends it, and a rotation arm
  passes it to `singleL[reuse]`, which also has its own `r`'s token.
- Each level takes one node apart and rebuilds one in place. The insert
  allocates only the new leaf, plus one node at the top if the outermost
  caller (`Map.insert`) has no token.
- `minView` works the same way: the recursive call takes `l`'s token, and
  `balance` takes the one passed in. At the bottom (`Tip`), the token passed
  in is unused and dropped: that is the one node the pop removes.
- The `Equal` arm spends the passed token directly.
- `remove`, `deleteMin` and `glue` follow without being named: any
  function that ends up building a `Bin` gets a variant on demand.

**Soundness.**

1. A token is created only by `Unpack`/`DropReuse`, from a cell whose count
   was 1, with every field set to `Erased`. Otherwise it is `Erased`.
2. It lives in a register that no IR expression reads. The variant's token
   slot is past the original body's slots, which `validate` can check.
3. code.rs moves it exactly once, into one `CtorReuse` or one variant call's
   argument, or drops it.

   So no reference to the cell exists outside the token's path, and a cell
   in use can never be overwritten. Even if the analysis were wrong (a
   variant that never builds, a size mismatch), the run-time test in
   `CtorReuse` (`Data`, same length, count 1) falls back to allocating.
4. Resumptions and effects: tokens already live in frame registers across
   calls (held across `ins` in the A/B pair). The effect runtime's
   continuations are heap data that never alias frame registers, so passing
   tokens adds no new exposure **[inferred from in-place-reuse.md §3.3 and
   trmc.rs's "Effects" paragraph]**.
5. Space: at most one held cell per token parameter per frame, so it is
   frame-limited.
6. SW-2388's last-use moves are what make the cells unique in the first
   place. This option adds only token moves, which code.rs controls
   directly.

**Steps.** No change: the same calls enter the same number of frames.
Calls go to `g′` instead of `g`. Ticks are unchanged. Allocation traces
change (more `reuse` events), and the machine and native still agree.
**Native ABI.** No change.

**Interactions.**

- TRMC twins (`trmc.rs`) are left alone in the first version. A twin turns
  its recursive calls into a loop that reassigns parameters, and code.rs's
  per-body token list doesn't model a loop. They can be added later.
- Closures and `Apply` aren't covered: only direct `Call`s of globals.
  Lambdas can follow.
- `opt.rs`'s `specialise` copies (`[0]`) come first, so the variants are
  made of the specialised copies.

**What it buys** **[estimated]**:

| Program | Gain | Reasoning |
|---|---|---|
| dijkstra | **8–15%** | About 23 M of the 25.7 M `Bin`s become reuses: all of `Keep` plus the rotations; `doubleL/R` still meet some shared cells. Each saves an allocation and a free. The free path is about 10.5 ns per cell on binary-trees (cell-allocator.md §1 **[measured]** there) plus the drop of an emptied cell, so 10–15 ns × 23 M ≈ 0.25–0.35 s of about 3.0 s. Cross-check: SW-2371's scratch saved 0.45 s for 17.7 M reuses, but that figure also includes saved calls. |
| matcher | **≈ 0** | Its misses are cells shared by the algorithm (backtracking holds the message), so no reuse scheme applies (SW-2361 **[measured]**). |
| disk | **1–3%** | About 11.7 M `rebuild`/`shape` in part 2's `Map`/`Set` `remove`/`add` (SW-2369 **[measured]**), if unique; parsing dominates (47%). |
| binary-trees | **0** | Trees are built by `make` and freed by `check`, and nothing is taken apart and rebuilt. Only a cell cache helps here (d). |
| `set_nat.sw` | reuse share 11.7% → about 85% | From the A/B pair (6.9% → 80.6%) and §2.2's "9 of 9.5 cells per insert". |

**Who else benefits** (beyond what SW-2383 reaches) **[inferred]**:

- every `Map`/`Set` operation that goes through `balance` (`remove`,
  `deleteMin`, `glue`, `alter`-style updates);
- any user tree with a smart constructor (AoC days that write their own);
- and the shape D2363 asks for in application code: a domain record
  updated through a method (`state.withPosition p` on a dead `state`
  reuses its cell when the method rebuilds the record). Option-, pair- and
  list-building helpers do the same.

That is the "stronger language" part: the readable shape of the code stops
costing allocations.

**Work.** About half a lane-day for Opus (2–3 h):

- the pass, about 250 lines;
- code.rs, about 60 lines;
- tests: machine trace tests for an insert path (the A/B pair as a
  snapshot, with the reuse count), a native agreement test, a token held
  across recursion, a variant whose token goes unused, and `Set.fromList`'s
  reuse share;
- `bench:compare` instructions on dijkstra and disk.

Opus, because it sits next to the bytecode's move discipline, which caused
a wrong answer before (stage 4) and a performance bug last night (SW-2388).

### (c) Don't lift a `match` that is used once into a separate body

**Change.** In `opt.rs` (or in `lower.rs` while lowering), inline a lifted
`f.%matchN` called from exactly one place into that place, whatever its size
and even in a recursive group. Break cycles as `crates/core/src/termination.rs`
`inlined` already does for termination ("lifted `match`es occurring exactly
once ... except that where following those occurrences leads round a
cycle, the first member on it isn't"). `fusion.rs` already inlines lifted
matches for state-passing handlers (`MatchBodies`), and `lower.rs` can lower
a case tree inside an expression.

**Soundness.** Inlining is pure; nothing new.

**Steps.** Change: one fewer frame per entry into a lifted match. In
`Map.Tree.insertWith` it changes little, since the outer function is already
inlined into `%match1`.

**Buys.** The `Equal` arm's reuse (0.73 M on dijkstra) and a frame per
lifted match in general. Needed by (a); not needed by (b), which treats
`%match1` as just another callee.

**Work.** 1–2 h, Sonnet or Opus. Worth its own ticket only if a profile
shows lifted-match frames as a cost.

### (d) A per-run cell cache: allocation reuse instead of cell reuse (SW-2363, D3413)

**Change.** As in cell-allocator.md: native code keeps a short list of freed
cells in the run `Context` and pops or pushes them inline. A cell freed in
`insertWith` is popped again by `rebuild`'s `Ctor` a few instructions later.

**Soundness.** It is the allocator's ordinary contract. The cache is
emptied at run end and kept out of traced builds.

**Steps.** No change. **Native ABI.** An internal change (the context gains
a field). The bytecode is unchanged.

**Buys.** Everything that allocates. Binary-trees 25–35% (cell-allocator.md
**[estimated]**). On dijkstra it removes most of the mimalloc share of each
fresh `Bin`, but not the drop of the old cell and the count test, so perhaps
half to two thirds of (b)'s gain there **[inferred]**.

**Work.** 60–90 min, Opus, already on the board.

(b) and (d) are complementary: (b) avoids the free and the allocation where
the structure allows, and (d) makes the rest cheap. With (d) in, (b)'s extra
gain on dijkstra shrinks to perhaps 4–8% **[inferred]**.

## 5. Compiler against std: what each buys

Matt, 8 Nov: "if we could solve this in the compiler, that makes it a
stronger language overall ... it's just a balance."

| | Reshape std (SW-2383, fix B) | (b) token passing | (a)+(c) inlining |
|---|---|---|---|
| dijkstra | -6% measured at the old 7.1 s scale (0.45 s). Both reuse and saved calls | 8–15%, reuse only **[est.]** | reuse of `Keep` plus saved calls; similar to B **[est.]** |
| Rotations reuse the caller's node | no (still `rebuild`) | yes | no |
| `remove`, `deleteMin`, `glue`, `Set` | only if each is reshaped too | yes | if sizes allow |
| User trees, records updated by methods, helpers | no | yes | only small helpers |
| std's code and proofs | changed: inline `Keep`, `if` chains, a `balance = Bin` lemma, proofs re-run | unchanged | unchanged |
| Step counts | change (fewer calls) | unchanged | change |
| Fragility | holds as long as nobody refactors the function | none: any depth, recursion allowed | sizes and the inline budget |
| Work | 60–90 min, Opus (proofs) | 2–3 h, Opus | 0.5–1 day + (c) |

**What reshaping would still win on its own, under (b).** Calls: the `Keep`
path still goes `balance` → `rebuild`, and `shape` reads `l` and `r` through
a call. That is two or three frames and about two increment/decrement pairs
per level that the hand-fused form doesn't pay. SW-2371's 0.45 s was both
effects together. My guess at the part left after (b) is 3–7% on dijkstra
**[inferred: half the scratch's per-node saving]**. That residue is a cost
of calls, not of allocation. The general fix for it is in the compiler too:
inline a small non-recursive helper called in tail position of an arm (a
rescoped SW-1812), or borrowed parameters for read-only calls like `shape`
(in-place-reuse.md stage 3). Lean reaches the same point with `@[inline]`
plus a fused std, which is the reshaping we're avoiding.

## 6. Recommendation

**The compiler fix first, std unchanged.** In order:

1. **(b) token passing**, as one Opus lane (2–3 h). Measure dijkstra, disk
   and `set_nat` instructions, and the per-site reuse counts (the
   interpreter counters SW-2371 used, or SW-1810's profile columns if they
   land first).
2. **(d) the cell cache (SW-2363)** in parallel, whenever D3413 is decided.
   It is independent, touches different code (`n1.rs` allocation paths
   against `code.rs` and a new IR pass), and is the only lever for
   binary-trees.
3. **Then measure the residue.** Write the hand-fused `insertWith`/`minView`
   in a scratch file (no std change) and compare with (b) on dijkstra. If the
   gap is under 3%, close SW-2383 and stop. If it's 3% or more, rescope
   SW-1812 to "inline small non-recursive helpers in an arm's tail
   position" and try that before any std change. Reshape std (SW-2383) only
   if the compiler can't close the gap with a bounded inliner.
4. **(c)** only if a profile shows lifted-match frames as a cost. (b) makes
   it unnecessary for reuse.

**Does SW-2383 become unnecessary?** For reuse, yes: (b) reuses everything
B would, and the rotations and the other `balance` callers too. For the
cost of calls, perhaps not entirely: that is step 3's measurement, and the
compiler is tried first there as well. I'd keep SW-2383 held, not closed,
until step 3.

**Why not reshape std now and do (b) later?** B is cheaper (60–90 min
against 2–3 h). But its end state is worse: std written around the
optimiser, proofs about a less readable `insertWith`, and every other
structure still missing reuse. Once (b) lands, B's reuse is redundant,
leaving only the call savings that step 3 would get anyway. Migration cost
doesn't count against a change (D2303), and the end state favours the
compiler.

## 7. Questions for Matt

1. **Reuse across calls as an invisible optimisation.** Take (b): the
   compiler passes a cell taken apart in one function to the function that
   rebuilds it, with no annotation in the source (no Koka-style `fip`
   keyword, no Lean-style `@[inline]` on std helpers)? **[rec: yes.** It
   keeps std readable, and helps user code and records updated through
   methods as much as std. It changes no step counts and no native ABI, and
   every reuse is still checked at run time. Reporting which sites reuse
   belongs in the profiler (SW-1810), not the language.**]**
2. **Std reshaping as the last resort.** Hold SW-2383 until (b) is measured.
   Then, if a residue of 3% or more remains on dijkstra, try a bounded
   compiler inline (rescoped SW-1812) before changing std's `Map.Tree`?
   **[rec: yes.** The residue is a cost of calls. The same inliner change
   would help every small helper, while a std reshape helps only the
   functions reshaped.**]**
3. **Step counts under inlining.** If step 3 leads to more inlining ((a) or
   (c)), programs enter fewer frames, so they run out of steps later. The
   charging rule (one step per frame) stays, and the machine and native keep
   agreeing. This is the same kind of change the inliner already makes.
   Treat that as an implementation detail, not a decision each time?
   **[rec: yes.** D1253 asks that runners agree, and they do. The count was
   never promised to be stable across compiler versions.**]**

## 8. Tickets to file

- **(b) token passing**, Opus, 2–3 h, comparative-speed epic. Brief: §4 (b),
  the tests listed there, `bench:compare` instructions on dijkstra, disk and
  binary-trees (binary-trees should be unchanged). Supersedes the reuse
  purpose of SW-1812. Blocked by question 1.
- **Measure the residue after (b)**, Sonnet, 30 min: a scratch hand-fused
  `insertWith`/`minView` compared with (b) on dijkstra. Decides SW-2383 and a
  rescoped SW-1812 (question 2).
- **SW-1812 rescope** (on the ticket): from "inlining for reuse" to
  "inlining small helpers in an arm's tail position, for calls", conditional
  on the residue.
- **(c) inline lifted matches used once**, backlog, conditional on a profile.

## 9. What wasn't checked

- Nothing was built or run. Every gain in §4–§6 is an estimate from SW-2369,
  SW-2371, SW-2388 and cell-allocator.md measurements, mostly taken before
  SW-2388, when cells were still partly shared.
- The node sizes of `balance`, `rebuild` and `shape` after simplification are
  estimated from the source, not printed. The IR has no dump flag. A test
  can print it with `Program`'s `Display` (`crates/rt/src/pretty.rs`).
- Whether `balance` is already inlined into `%match1[0]` today: SW-2371's
  listing says `%match1[0]` calls it. Either way the `Bin` is built in
  `rebuild`, a separate body, so the conclusion stands.
- Counting Immutable Beans was not re-read (compilation.md card C1). Lean's
  current pass and pipeline were read from `master` on GitHub on 8 Nov 2026.
- Swift, Clean, GHC, OCaml and Lobster are from memory. Roc was read only
  from a Zulip thread.

## Sources

- Lean 4, `master`, read 8 Nov 2026:
  [LCNF/ResetReuse.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/LCNF/ResetReuse.lean),
  [LCNF/Passes.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/LCNF/Passes.lean),
  [Data/RBMap.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/RBMap.lean),
  [Std/Data/DTreeMap/Internal/Balancing.lean](https://github.com/leanprover/lean4/blob/master/src/Std/Data/DTreeMap/Internal/Balancing.lean),
  [ToLCNF API docs](https://lean-lang.org/doc/api/Lean/Compiler/LCNF/ToLCNF.html).
- Reinking, Xie, de Moura, Leijen, *Perceus*, MSR-TR-2020-42 v4,
  [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2020/11/perceus-tr-v4.pdf).
- Lorenzen, Leijen, *Reference Counting with Frame Limited Reuse*,
  MSR-TR-2021-30 v2, [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/11/flreuse-tr.pdf).
- Lorenzen, Leijen, Swierstra, *FP²: Fully in-Place Functional Programming*,
  MSR-TR-2023-19, [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2023/05/fbip.pdf).
- Mazur, Ross, Janssens, Bruynooghe, *Practical Aspects for a Working Compile
  Time Garbage Collection System for Mercury*, [arXiv cs/0110037](https://arxiv.org/abs/cs/0110037).
- Roc Zulip, [Tail Recursion Modulo Cons](https://roc-lang.github.io/zulip-export/stream/316715-contributing/topic/Tail.20Recursion.20Modulo.20Cons.html).
- Ours: [docs/research/in-place-reuse.md](../research/in-place-reuse.md),
  [docs/reviews/SW-1163-in-place-reuse-fresh-eyes.md](../reviews/SW-1163-in-place-reuse-fresh-eyes.md),
  [docs/reviews/SW-2371-map-rebuild-reuse.md](../reviews/SW-2371-map-rebuild-reuse.md),
  [docs/reviews/SW-2361-ctor-reuse.md](../reviews/SW-2361-ctor-reuse.md),
  [docs/reviews/SW-2369-dijkstra-disk.md](../reviews/SW-2369-dijkstra-disk.md),
  [cell-allocator.md](cell-allocator.md).
