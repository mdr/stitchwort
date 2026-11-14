--| The effect machinery: computations ([`Effect.Comp`], `bind`),
--| signatures and mappings between them, `Rec` and `Delay`.
-- Loaded with the core: The registry's `sigCase` and the `Partial` and `Rec`
-- built-ins use these, so they are checked before any program
-- (docs/proposals/prelude-slim.md §2.1).

-- Computations (docs/proposals/abilities.md)

--| A computation that returns an `a`, performing operations from a signature:
--| `op` is the type of operation calls, and `res o` is what call `o` gives
--| back. Every computation is a finite tree, so folds over it terminate.
type Effect.Comp (op: Type) (res: op → Type) (a: Type): Type =
  | Done (value: a)
  | Call (o: op) (rest: res o → Comp op res a)

--| The fold over a computation. `call` gets each operation together with the
--| results of folding every way it could continue, and may use them any
--| number of times. A deep handler is a fold.
def Effect.foldComp [op: Type] [res: op → Type] [a r: Type] (done: a → r) (call: (o: op) → (res o → r) → r):
    (comp: Comp op res a) → r
  | Done x => done x
  | Call o rest => call o (y => foldComp done call (rest y))

--| Sequencing: run `comp`, then `next` with its result.
def Effect.bind: [op: Type]
      → [res: op → Type]
      → [a b: Type]
      → (comp: Comp op res a)
      → (next: a → Comp op res b)
      → Comp op res b
  | Done x, next => next x
  | Call o rest, next => Call o (y => bind (rest y) next)

-- Rows: signatures side by side, and mappings between signatures.

--| The operations of two signatures: the row `{l, r}`.
type Effect.Plus (l: Type) (r: Type): Type = | L (o: l) | R (o: r)

--| What each operation of the row `{l, r}` gives back: its side's response type.
def Effect.PlusRes [l r: Type] (lres: l → Type) (rres: r → Type): (o: Plus l r) → Type
  | L o => lres o
  | R o => rres o

--| A mapping from one signature into another. Because what an operation
--| returns depends on the operation, a mapping says both where each
--| operation goes and how its response comes back.
type Effect.SigMap (op1: Type) (res1: op1 → Type) (op2: Type) (res2: op2 → Type): Type =
  | MkSigMap (inject: op1 → op2) (reply: (o: op1) → res2 (inject o) → res1 o)

--| Where a mapping sends an operation.
def Effect.sigInject: [op1: Type]
      → [res1: op1 → Type]
      → [op2: Type]
      → [res2: op2 → Type]
      → (m: SigMap op1 res1 op2 res2)
      → (o: op1)
      → op2
  | MkSigMap inj rep, o => inj o

--| How a mapping brings an operation's response back.
def Effect.sigReply: [op1: Type]
      → [res1: op1 → Type]
      → [op2: Type]
      → [res2: op2 → Type]
      → (m: SigMap op1 res1 op2 res2)
      → (o: op1)
      → (reply: res2 (sigInject m o))
      → res1 o
  | MkSigMap inj rep, o, r => rep o r

--| Moves a computation along a mapping. Operations stay in the same order;
--| only their names in the signature change.
def Effect.translate [op1: Type] [res1: op1 → Type] [op2: Type] [res2: op2 → Type] [a: Type]
    (m: SigMap op1 res1 op2 res2):
    (comp: Comp op1 res1 a) → Comp op2 res2 a
  | Done x => Done x
  | Call o rest => Call (sigInject m o) (r => translate m (rest (sigReply m o r)))

--| The mapping from a signature to itself that changes nothing.
def Effect.sigId: [op: Type] → [res: op → Type] → SigMap op res op res := MkSigMap (o => o) (o r => r)

--| One mapping after another, as one mapping.
def Effect.sigCompose: [op1: Type]
      → [res1: op1 → Type]
      → [op2: Type]
      → [res2: op2 → Type]
      → [op3: Type]
      → [res3: op3 → Type]
      → (first: SigMap op1 res1 op2 res2)
      → (second: SigMap op2 res2 op3 res3)
      → SigMap op1 res1 op3 res3
  | MkSigMap i1 r1, MkSigMap i2 r2 => MkSigMap (o => i2 (i1 o)) (o r => r1 o (r2 (i1 o) r))

--| Weakening: a signature into a row with something else on its right.
def Effect.sigLeft: [l r: Type] → [lres: l → Type] → [rres: r → Type] → SigMap l lres (Plus l r) (PlusRes lres rres) :=
  MkSigMap (o => L o) (o x => x)

--| Weakening: a signature into a row with something else on its left.
def Effect.sigRight: [l r: Type] → [lres: l → Type] → [rres: r → Type] → SigMap r rres (Plus l r) (PlusRes lres rres) :=
  MkSigMap (o => R o) (o x => x)

--| An operation of `{l, r}` as the same operation of `{r, l}`.
def Effect.swapOp: [l r: Type] → (o: Plus l r) → Plus r l
  | L o => R o
  | R o => L o

--| A response in `{r, l}` brought back to `{l, r}`.
def Effect.swapReply: [l r: Type]
      → [lres: l → Type]
      → [rres: r → Type]
      → (o: Plus l r)
      → (reply: PlusRes rres lres (swapOp o))
      → PlusRes lres rres o
  | L o, x => x
  | R o, x => x

--| Reordering: the mapping from `{l, r}` to `{r, l}`.
def Effect.sigSwap: [l r: Type]
      → [lres: l → Type]
      → [rres: r → Type]
      → SigMap (Plus l r) (PlusRes lres rres) (Plus r l) (PlusRes rres lres) :=
  MkSigMap swapOp swapReply

-- Support for abilities (docs/proposals/abilities.md). The elaborator
-- translates `ability`, rows `{A | e}`, effectful code and `handle` into these.

--| `()`: the unit type and its only value.
type Builtin.UnitType: Type = | UnitValue

--| The signature with no operations: the end of a closed row.
type Effect.NoOp: Type

--| The responses of the signature with no operations: there are none to give.
def Effect.NoRes: (o: NoOp) → Type
  | ()

--| Where the combined mapping from `{l, r}` sends an operation: by its side's mapping.
def Effect.caseInject [l r t: Type] [lres: l → Type] [rres: r → Type] [tres: t → Type]
    (ml: SigMap l lres t tres)
    (mr: SigMap r rres t tres):
    (o: Plus l r) → t
  | L o => sigInject ml o
  | R o => sigInject mr o

--| How the combined mapping from `{l, r}` brings a response back: by its side's mapping.
def Effect.caseReply [l r t: Type] [lres: l → Type] [rres: r → Type] [tres: t → Type]
    (ml: SigMap l lres t tres)
    (mr: SigMap r rres t tres):
    (o: Plus l r) → (reply: tres (caseInject ml mr o)) → PlusRes lres rres o
  | L o, x => sigReply ml o x
  | R o, x => sigReply mr o x

--| Combining two mappings into one from `{l, r}`.
def Effect.sigCase [l r t: Type] [lres: l → Type] [rres: r → Type] [tres: t → Type]
    (ml: SigMap l lres t tres)
    (mr: SigMap r rres t tres):
    SigMap (Plus l r) (PlusRes lres rres) t tres :=
  MkSigMap (caseInject ml mr) (caseReply ml mr)

--| Where the empty signature's operations go: there are none.
def Effect.noInject: [t: Type] → (o: NoOp) → t
  | ()

--| How the empty signature's responses come back: there are none.
def Effect.noReply: [t: Type] → [tres: t → Type] → (o: NoOp) → (reply: tres (noInject o)) → NoRes o
  | (), _

--| The empty signature maps into anything.
def Effect.sigFromNo: [t: Type] → [tres: t → Type] → SigMap NoOp NoRes t tres := MkSigMap noInject noReply

--| A handler's step for the row `{l, r}`, from steps for each side.
def Effect.handlePlus [l r: Type] [lres: l → Type] [rres: r → Type] [res: Type]
    (fl: (o: l) → (lres o → res) → res) (fr: (o: r) → (rres o → res) → res):
    (o: Plus l r) → (k: PlusRes lres rres o → res) → res
  | L o, k => fl o k
  | R o, k => fr o k

--| A computation that performs nothing is just its result.
def Effect.runPure: [a: Type] → (comp: Comp NoOp NoRes a) → a
  | Done x => x
  | Call () rest

--| The rows of abilities a computation may perform, as type parameters. A row parameter `e` in `{e}` or `{A | e}` is an
--| `Effects`, used only as an index: either the empty row, or the operations
--| and results of a row with at least one ability. Only the library may name
--| the constructors of `Effects` and the definitions below that take a row
--| apart; programs get rows only through `{e}` in types. So code abstract
--| over an effects parameter can't construct, inspect, compare or branch on
--| it. This is not parametricity in the strong sense: the type theory
--| computes differently at the empty row by design (`CompIn Empty a` is `a`).
-- (docs/proposals/effect-polymorphism.md, design C)
-- (D1122)
-- The elaborator never builds `Ops NoOp NoRes`: a row with no abilities is
-- always `Empty` (the canonical form).
type Effect.Effects: Type 1 = | Empty | Ops (op: Type) (res: op → Type)

--| The operation type of a row: what `{A | e}` puts after `A`.
def Effect.rowOp: (row: Effects) → Type
  | Empty => NoOp
  | Ops op res => op

--| The response types of a row's operations.
def Effect.rowRes: (row: Effects) → (o: rowOp row) → Type
  | Empty, o => NoRes o
  | Ops op res, o => res o

--| `{e} a`: a computation in the row `e`. In the empty row it is the plain
--| type, so pure uses of an effect-polymorphic function compute as pure code.
def Effect.CompIn: (row: Effects) → (a: Type) → Type
  | Empty, a => a
  | Ops op res, a => Comp op res a

--| `Done`, in any row.
def Effect.doneIn [a: Type]: (row: Effects) → (x: a) → CompIn row a
  | Empty, value => value
  | Ops op res, value => Done value

--| `bind`, in any row. In the empty row it is application.
def Effect.bindIn [a b: Type]: (row: Effects) → (comp: CompIn row a) → (next: a → CompIn row b) → CompIn row b
  | Empty, computation, next => next computation
  | Ops op res, computation, next => bind computation next

--| A computation in `{e}` as a tree, to move into a row with abilities.
def Effect.liftIn [a: Type]: (row: Effects) → (comp: CompIn row a) → Comp (rowOp row) (rowRes row) a
  | Empty, value => Done value
  | Ops op res, computation => computation

--| The converse: what a handler whose remaining row is `{e}` ends with.
def Effect.lowerIn [a: Type]: (row: Effects) → (comp: Comp (rowOp row) (rowRes row) a) → CompIn row a
  | Empty, computation => runPure computation
  | Ops op res, computation => computation

--| A computation over closed abilities moved into the same abilities
--| followed by a row (`{A, B}` into `{A, B | e}`). `pre t` is the abilities
--| followed by `t`, `preRes` their results. In the empty row it is the
--| computation itself, so a closed computation moved into a row that turns
--| out empty is left as written.
-- (docs/proposals/delayed-translate.md)
def Effect.widenIn [a: Type] (pre: Type → Type) (preRes: (t: Type) → (t → Type) → pre t → Type):
    (row: Effects)
      → (m: SigMap (pre NoOp) (preRes NoOp NoRes) (pre (rowOp row)) (preRes (rowOp row) (rowRes row)))
      → (comp: Comp (pre NoOp) (preRes NoOp NoRes) a)
      → Comp (pre (rowOp row)) (preRes (rowOp row) (rowRes row)) a
  | Empty, m, computation => computation
  | Ops op res, m, computation => translate m computation

-- Laws of computations (docs/proposals/effect-polymorphism.md, "Proof
-- tooling"). A computation passed where a `Comp` is expected is passed as it
-- is, so these apply to computations that don't compute yet. The laws whose
-- proofs need function extensionality (`bindDone`, `bindAssoc`,
-- `foldCompBind`) are in `Effect/Laws.sw`.

--| Folding a finished computation gives `done` of its result.
theorem Effect.foldCompDone ∀ [op: Type] [res: op → Type] [a r: Type] (done: a → r)
    (call: (o: op) → (res o → r) → r) (x: a):
    foldComp done call (Done x: Comp op res a) = done x :=
  rfl

--| Running a sequence that performs nothing runs its first part, then the rest.
theorem Effect.runPureBind ∀ [a b: Type] (computation: Comp NoOp NoRes a) (next: a → Comp NoOp NoRes b):
    runPure (bind computation next) = runPure (next (runPure computation)) :=
  match computation with
    | Done x => rfl
    | Call () rest

-- Partial computations (docs/proposals/partial.md)

--| A recursion request: run the definition being defined again on `x`. A
--| partial definition's body makes these instead of calling itself.
type Effect.Rec (req: Type): Type = | Recur (x: req)

--| What a request is answered with.
def Effect.RecRes [req: Type] (ans: req → Type): (rec: Rec req) → Type
  | Recur x => ans x

--| A computation that may not finish: what `{Partial | e} a` stands for.
--| These have no definitions, and nothing can look inside a `Delay`: only
--| the runtime runs one, a step at a time.
-- The kernel admits them as primitives, after checking their types are
-- exactly these.
def Effect.Delay: (op: Type) → (res: op → Type) → (a: Type) → Type

--| Finished, with this result.
def Effect.now: [op: Type] → [res: op → Type] → [a: Type] → (x: a) → Delay op res a

--| A computation that finishes, as one that might not.
def Effect.lift: [op: Type] → [res: op → Type] → [a: Type] → (comp: Comp op res a) → Delay op res a

--| Sequencing for a computation that may not finish: run `delay`, then `next` with its result, if it finishes.
def Effect.bindD: [op: Type]
      → [res: op → Type]
      → [a b: Type]
      → (delay: Delay op res a)
      → (next: a → Delay op res b)
      → Delay op res b

--| Moves a computation along a mapping between signatures.
def Effect.mapSig: [op1: Type]
      → [res1: op1 → Type]
      → [op2: Type]
      → [res2: op2 → Type]
      → [a: Type]
      → (m: SigMap op1 res1 op2 res2)
      → (delay: Delay op1 res1 a)
      → Delay op2 res2 a

--| The recursive function a description defines: each `Recur y` its body
--| requests is answered by running the body on `y`.
def Effect.pfix: [op: Type]
      → [res: op → Type]
      → [req: Type]
      → [ans: req → Type]
      → (step: (x: req) → Delay (Plus (Rec req) op) (PlusRes (RecRes ans) res) (ans x))
      → (x: req)
      → Delay op res (ans x)

--| The handler fold for a partial computation: `foldComp` with every result a
--| `Delay`, so a handler around partial code is partial. `done` gets the
--| result, `call` each operation and the rest of the computation, still
--| handled.
-- (docs/proposals/partial-handlers.md)
def Effect.foldD: [op1: Type]
      → [res1: op1 → Type]
      → [op2: Type]
      → [res2: op2 → Type]
      → [a b: Type]
      → (done: a → Delay op2 res2 b)
      → (call: (o: op1) → (res1 o → Delay op2 res2 b) → Delay op2 res2 b)
      → (delay: Delay op1 res1 a)
      → Delay op2 res2 b

-- Partiality through a bare row (docs/proposals/partial-stage-3.md, D1213).

--| Whether a computation in a bare row `{e}` may not finish. A signature whose
--| row variable `e` appears only bare takes one of these beside `e`, so a
--| function like `List.map` takes partial callbacks: at `MayDiverge` its
--| computations are `Delay`s. Like `Effects`, only the library may name it,
--| its constructors and the definitions below.
-- (D1214)
-- (D1122)
type Effect.Divergence: Type = | Total | MayDiverge

--| `{e} a` once `e` may be partial: today's `CompIn e a` when total, and the
--| partial computation `{Partial | e} a` when not.
def Effect.CompD: (d: Divergence) → (row: Effects) → (a: Type) → Type
  | Total, row, a => CompIn row a
  | MayDiverge, row, a => Delay (rowOp row) (rowRes row) a

--| `doneIn`, where `e` may be partial.
def Effect.doneD [a: Type]: (d: Divergence) → (row: Effects) → (x: a) → CompD d row a
  | Total, row, value => doneIn row value
  | MayDiverge, row, value => now value

--| `bindIn`, where `e` may be partial.
def Effect.bindDv [a b: Type]:
    (d: Divergence) → (row: Effects) → (comp: CompD d row a) → (next: a → CompD d row b) → CompD d row b
  | Total, row, c, next => bindIn row c next
  | MayDiverge, row, c, next => bindD c next

--| A total computation in `{e}`, moved to where `e` may be partial.
def Effect.liftD [a: Type]: (d: Divergence) → (row: Effects) → (comp: CompIn row a) → CompD d row a
  | Total, row, c => c
  | MayDiverge, row, c => lift (liftIn row c)

--| A computation in `{e}`, moved into the partial row `{Partial | e}`.
def Effect.delayD [a: Type]: (d: Divergence) → (row: Effects) → (comp: CompD d row a) → Delay (rowOp row) (rowRes row) a
  | Total, row, c => lift (liftIn row c)
  | MayDiverge, row, c => c

-- Partiality through a row with abilities, `{A | e}` (docs/proposals/partial-handlers.md
-- §4.2, D1255): `e`'s divergence index is the whole row's.

--| The handler fold, where the handled code may be partial.
--| It is today's `foldComp` when total, so proofs about handlers compute as
--| before, and `foldD` when not, whose result is partial too.
def Effect.foldCompD [op1: Type] [res1: op1 → Type] [a b: Type]:
    (d: Divergence)
      → (out: Effects)
      → (done: a → CompD d out b)
      → (call: (o: op1) → (res1 o → CompD d out b) → CompD d out b)
      → (comp: CompD d (Ops op1 res1) a)
      → CompD d out b
  | Total, out, done, call, c => foldComp done call c
  | MayDiverge, out, done, call, c => Effect.foldD done call c

--| Moves a computation along a mapping between two rows that may be partial:
--| `translate` when total, `mapSig` when not.
def Effect.translateD [a: Type]:
    (d: Divergence)
      → (from to: Effects)
      → (m: SigMap (rowOp from) (rowRes from) (rowOp to) (rowRes to))
      → (comp: CompD d from a)
      → CompD d to a
  | Total, from, to, m, c => lowerIn to (translate m (liftIn from c))
  | MayDiverge, from, to, m, c => mapSig m c

--| Performs operation `o` of a row that may be partial, then goes on with
--| `k`: what a handler does with an operation it doesn't handle.
def Effect.callD [b: Type]:
    (d: Divergence) → (row: Effects) → (o: rowOp row) → (k: rowRes row o → CompD d row b) → CompD d row b
  | Total, row, o, k => bindIn row (lowerIn row (Call o ((y: rowRes row o) => Done y))) k
  | MayDiverge, row, o, k => bindD (lift (Call o ((y: rowRes row o) => Done y))) k
