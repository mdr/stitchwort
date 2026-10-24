-- core/Effect.sw. The effect machinery: computations (`Effect.Comp`, `bind`),
-- signatures and mappings between them, `Rec` and `Delay`. Loaded with the
-- core: The registry's `sigCase` and the `Partial` and `Rec` built-ins use
-- these, so they are checked before any program
-- (docs/proposals/prelude-slim.md §2.1).

-- Computations (docs/proposals/abilities.md)

-- A computation that returns an `a`, performing operations from a signature:
-- `op` is the type of operation calls, and `res o` is what call `o` gives
-- back. Every computation is a finite tree, so folds over it terminate.
type Effect.Comp (op: Type) (res: op -> Type) (a: Type): Type =
  | Done (value: a)
  | Call (o: op) (rest: res o -> Comp op res a)

-- The fold over a computation. `call` gets each operation together with the
-- results of folding every way it could continue, and may use them any
-- number of times. A deep handler is a fold.
def Effect.foldComp [op: Type] [res: op -> Type] [a r: Type]
    (done: a -> r) (call: (o: op) -> (res o -> r) -> r): Comp op res a -> r
  | Done x => done x
  | Call o rest => call o (y => foldComp done call (rest y))

-- Sequencing: run `c`, then `next` with its result.
def Effect.bind: [op: Type] -> [res: op -> Type] -> [a b: Type] ->
    Comp op res a -> (a -> Comp op res b) -> Comp op res b
  | Done x, next => next x
  | Call o rest, next => Call o (y => bind (rest y) next)

-- Rows: signatures side by side, and mappings between signatures.

-- The operations of two signatures: the row `{l, r}`.
type Effect.Plus (l: Type) (r: Type): Type =
  | L (o: l)
  | R (o: r)

def Effect.PlusRes [l r: Type] (lres: l -> Type) (rres: r -> Type): Plus l r -> Type
  | L o => lres o
  | R o => rres o

-- A mapping from one signature into another. Because what an operation
-- returns depends on the operation, a mapping says both where each
-- operation goes and how its response comes back.
type Effect.SigMap (op1: Type) (res1: op1 -> Type) (op2: Type) (res2: op2 -> Type): Type =
  | MkSigMap (inject: op1 -> op2) (reply: (o: op1) -> res2 (inject o) -> res1 o)

def Effect.sigInject: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] ->
    SigMap op1 res1 op2 res2 -> op1 -> op2
  | MkSigMap inj rep, o => inj o

def Effect.sigReply: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] ->
    (m: SigMap op1 res1 op2 res2) -> (o: op1) -> res2 (sigInject m o) -> res1 o
  | MkSigMap inj rep, o, r => rep o r

-- Moves a computation along a mapping. Operations stay in the same order;
-- only their names in the signature change.
def Effect.translate [op1: Type] [res1: op1 -> Type] [op2: Type] [res2: op2 -> Type] [a: Type]
    (m: SigMap op1 res1 op2 res2): Comp op1 res1 a -> Comp op2 res2 a
  | Done x => Done x
  | Call o rest => Call (sigInject m o) (r => translate m (rest (sigReply m o r)))

def Effect.sigId: [op: Type] -> [res: op -> Type] -> SigMap op res op res := MkSigMap (o => o) (o r => r)

def Effect.sigCompose: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] ->
    [op3: Type] -> [res3: op3 -> Type] ->
    SigMap op1 res1 op2 res2 -> SigMap op2 res2 op3 res3 -> SigMap op1 res1 op3 res3
  | MkSigMap i1 r1, MkSigMap i2 r2 =>
    MkSigMap (o => i2 (i1 o)) (o r => r1 o (r2 (i1 o) r))

-- Weakening: a signature into a row with something else on the right or left.
def Effect.sigLeft: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
    SigMap l lres (Plus l r) (PlusRes lres rres) := MkSigMap (o => L o) (o x => x)

def Effect.sigRight: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
    SigMap r rres (Plus l r) (PlusRes lres rres) := MkSigMap (o => R o) (o x => x)

-- Reordering: `{l, r}` to `{r, l}`.
def Effect.swapOp: [l r: Type] -> Plus l r -> Plus r l
  | L o => R o
  | R o => L o

def Effect.swapReply: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
    (o: Plus l r) -> PlusRes rres lres (swapOp o) -> PlusRes lres rres o
  | L o, x => x
  | R o, x => x

def Effect.sigSwap: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
    SigMap (Plus l r) (PlusRes lres rres) (Plus r l) (PlusRes rres lres) := MkSigMap swapOp swapReply

-- Support for abilities (docs/proposals/abilities.md). The elaborator
-- translates `ability`, rows `{A | e}`, effectful code and `handle` into these.

-- `()`: the unit type and its only value.
type Builtin.UnitType: Type =
  | UnitValue

-- The signature with no operations: the end of a closed row.
type Effect.NoOp: Type

def Effect.NoRes: NoOp -> Type
  | ()

-- Combining two mappings into one from `{l, r}`.
def Effect.caseInject [l r t: Type] [lres: l -> Type] [rres: r -> Type] [tres: t -> Type]
    (ml: SigMap l lres t tres) (mr: SigMap r rres t tres): Plus l r -> t
  | L o => sigInject ml o
  | R o => sigInject mr o

def Effect.caseReply [l r t: Type] [lres: l -> Type] [rres: r -> Type] [tres: t -> Type]
    (ml: SigMap l lres t tres) (mr: SigMap r rres t tres):
    (o: Plus l r) -> tres (caseInject ml mr o) -> PlusRes lres rres o
  | L o, x => sigReply ml o x
  | R o, x => sigReply mr o x

def Effect.sigCase [l r t: Type] [lres: l -> Type] [rres: r -> Type] [tres: t -> Type]
    (ml: SigMap l lres t tres) (mr: SigMap r rres t tres): SigMap (Plus l r) (PlusRes lres rres) t tres := MkSigMap (caseInject ml mr) (caseReply ml mr)

-- The empty signature maps into anything.
def Effect.noInject: [t: Type] -> NoOp -> t
  | ()

def Effect.noReply: [t: Type] -> [tres: t -> Type] -> (o: NoOp) -> tres (noInject o) -> NoRes o
  | (), _

def Effect.sigFromNo: [t: Type] -> [tres: t -> Type] -> SigMap NoOp NoRes t tres := MkSigMap noInject noReply

-- A handler's step for the row `{l, r}`, from steps for each side.
def Effect.handlePlus [l r: Type] [lres: l -> Type] [rres: r -> Type] [res: Type]
    (fl: (o: l) -> (lres o -> res) -> res) (fr: (o: r) -> (rres o -> res) -> res):
    (o: Plus l r) -> (PlusRes lres rres o -> res) -> res
  | L o, k => fl o k
  | R o, k => fr o k

-- A computation that performs nothing is just its result.
def Effect.runPure: [a: Type] -> Comp NoOp NoRes a -> a
  | Done x => x
  | Call () rest

-- Rows as values (docs/proposals/effect-polymorphism.md, design C). A row
-- variable `e` in `{e}` or `{A | e}` is a `Row`: either the empty row, or the
-- operations and results of a row with at least one ability. Only the
-- library may name `Row`'s constructors and the definitions below that take
-- a row apart (D1122); programs get rows only through `{e}` in types.
-- The elaborator never builds `Ops NoOp NoRes`: a row with no abilities is
-- always `Empty` (the canonical form).
type Effect.Row: Type 1 =
  | Empty
  | Ops (op: Type) (res: op -> Type)

-- The operation type of a row: what `{A | e}` puts after `A`.
def Effect.rowOp: Row -> Type
  | Empty => NoOp
  | Ops op res => op

def Effect.rowRes: (row: Row) -> rowOp row -> Type
  | Empty, o => NoRes o
  | Ops op res, o => res o

-- `{e} a`: a computation in the row `e`. In the empty row it is the plain
-- type, so pure uses of an effect-polymorphic function compute as pure code.
def Effect.CompIn: Row -> Type -> Type
  | Empty, a => a
  | Ops op res, a => Comp op res a

-- `Done`, in any row.
def Effect.doneIn [a: Type]: (row: Row) -> a -> CompIn row a
  | Empty, value => value
  | Ops op res, value => Done value

-- `bind`, in any row. In the empty row it is application.
def Effect.bindIn [a b: Type]: (row: Row) -> CompIn row a -> (a -> CompIn row b) -> CompIn row b
  | Empty, computation, next => next computation
  | Ops op res, computation, next => bind computation next

-- A computation in `{e}` as a tree, to move into a row with abilities.
def Effect.liftIn [a: Type]: (row: Row) -> CompIn row a -> Comp (rowOp row) (rowRes row) a
  | Empty, value => Done value
  | Ops op res, computation => computation

-- The converse: what a handler whose remaining row is `{e}` ends with.
def Effect.lowerIn [a: Type]: (row: Row) -> Comp (rowOp row) (rowRes row) a -> CompIn row a
  | Empty, computation => runPure computation
  | Ops op res, computation => computation

-- Laws of computations (docs/proposals/effect-polymorphism.md, "Proof
-- tooling"). A computation passed where a `Comp` is expected is passed as it
-- is, so these apply to computations that don't compute yet. The laws whose
-- proofs need function extensionality (`bindDone`, `bindAssoc`,
-- `foldCompBind`) are in `Effect/Laws.sw`.

-- Folding a finished computation gives `done` of its result.
theorem Effect.foldCompDone [op: Type] [res: op -> Type] [a r: Type]
    (done: a -> r) (call: (o: op) -> (res o -> r) -> r) (x: a):
    foldComp done call (Done x: Comp op res a) = done x := rfl

-- Running a sequence that performs nothing runs its first part, then the rest.
theorem Effect.runPureBind [a b: Type]:
    (computation: Comp NoOp NoRes a) -> (next: a -> Comp NoOp NoRes b) ->
    runPure (bind computation next) = runPure (next (runPure computation))
  | Done x, next => rfl
  | Call () rest, next

-- Partial computations (docs/proposals/partial.md)

-- A recursion request: run the definition being defined again on `x`. A
-- partial definition's body makes these instead of calling itself.
type Effect.Rec (req: Type): Type =
  | Recur (x: req)

-- What a request is answered with.
def Effect.RecRes [req: Type] (ans: req -> Type): Rec req -> Type
  | Recur x => ans x

-- A computation that may not finish: what `{Partial | e} a` stands for.
-- These have no definitions, and nothing can look inside a `Delay`: only
-- the runtime runs one, a step at a time. The kernel admits them as
-- primitives, after checking their types are exactly these.
def Effect.Delay: (op: Type) -> (res: op -> Type) -> Type -> Type

-- Finished, with this result.
def Effect.now: [op: Type] -> [res: op -> Type] -> [a: Type] -> a -> Delay op res a

-- A computation that finishes, as one that might not.
def Effect.lift: [op: Type] -> [res: op -> Type] -> [a: Type] -> Comp op res a -> Delay op res a

-- Sequencing.
def Effect.bindD: [op: Type] -> [res: op -> Type] -> [a b: Type] ->
  Delay op res a -> (a -> Delay op res b) -> Delay op res b

-- Moves a computation along a mapping between signatures.
def Effect.mapSig: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] -> [a: Type] ->
  SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a

-- The recursive function a description defines: each `Recur y` its body
-- requests is answered by running the body on `y`.
def Effect.pfix: [op: Type] -> [res: op -> Type] -> [req: Type] -> [ans: req -> Type] ->
  ((x: req) -> Delay (Plus (Rec req) op) (PlusRes (RecRes ans) res) (ans x)) ->
  (x: req) -> Delay op res (ans x)
