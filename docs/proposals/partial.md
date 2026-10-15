# Proposal: `Partial`

**Status:** open, 15 October 2026. Nothing is decided or implemented. Split out of [`abilities.md`](abilities.md) after review found draft 1's design unsound. Until this is settled there is no `Partial`, and every definition must pass the termination checker.

## Goal

A function that might not terminate says so in its type (`Nat -> {Partial} Nat`), and so does everything that calls it. Only the runtime runs `Partial` code without a bound. The type checker never runs it.

## Why draft 1's design doesn't work

Draft 1 represented a partial computation as a `Comp` tree that may be infinite, built by guarded recursion:

```
spin n = Call later (\_ -> spin n)
```

But `Comp` is an *inductive* type: its fold (any structurally recursive function over it) assumes every tree is *well-founded*, meaning every path through it ends. (A tree may still have infinitely many paths, as when an operation returns a `Nat`.) With an infinite tree available, an ordinary function proves anything:

```
drain : Comp LaterOp LaterRes a -> a
drain (Done x)          = x
drain (Call Later rest) = drain (rest ())

forever : () -> Comp LaterOp LaterRes Void
forever () = Call Later (\_ -> forever ())

contradiction : Void
contradiction = drain (forever ())
```

Some things that don't help:
- **Not unfolding `forever` during type checking.** The problem is that the kernel would have admitted an inhabitant that its eliminator proves can't exist.
- **"Users may not handle `Partial`".** `drain` is an ordinary function over an ordinary type.

This is now a must-reject test (`examples/soundness/infinite-computation.sw`).

## Requirements for a design

1. **Keep well-founded computations and computations that may continue indefinitely distinct in the core.** Options:
   - A separate type for possibly-infinite computations, coinductive or productivity-checked (Capretta's delay monad, Interaction Trees), with its own rules for constructing, observing and eliminating it.
   - A resumable machine with a total step function.

   Either way, `Comp`'s inductive eliminator must never apply to it.
2. **Row-polymorphic handlers.** What does `runState` do when its residual row includes `Partial`? An inductive fold can't consume a possibly-infinite input. Options:
   - a productive interpretation of handlers for that case;
   - a distinction carried by the representation;
   - excluding `Partial` from handlers' residual rows at first.
3. **Bounded observation versus unbounded running.** Only the runtime may run `Partial` code without a bound. A checked, bounded observer (`withFuel`) may be allowed. Their policies must fit together.
4. **What type checking may do.** Opaque partial definitions block computing through bounded observations. Decide whether a bounded observer may expose delayed steps while checking. A runtime result doesn't automatically become a proof by computation.

## A first experiment: a machine with a total step function

This one needs no coinduction. A partial computation is a state together with a total step function:

```
type Step op res s a =
  | Finish (x : a)
  | Continue (next : s)
  | Request (o : op) (next : res o -> s)

runFuel : Nat -> (s -> Step op res s a) -> s -> Comp op res (Optional a)
runFuel 0        step st = Done None
runFuel (Succ n) step st =
  match step st with
  | Finish x       -> Done (Some x)
  | Continue st'   -> runFuel n step st'
  | Request o next -> Call o (\r -> runFuel n step (next r))
```

Every call to `step` costs one unit of fuel, including one that makes a request, so every recursive call decreases the fuel. This would show bounded observation working on the existing total core. It doesn't settle:
- compiling recursive source functions into machines;
- composing machines;
- how row-polymorphic handlers work on them.

## `withFuel` is not free

Draft 1 claimed `withFuel : Nat -> (() -> {Partial | e} a) -> {e} Optional a` "recurses on the fuel". For a forwarded operation, the natural equation doesn't decrease the fuel:

```
withFuel n (Call o rest) = Call o (\x -> withFuel n (rest x))
```

With an inductive input, recursion on the tree would justify this; with a coinductive one it doesn't. The invariant needed is roughly "between successive fuel-consuming steps, the computation is well-founded". One possible shape:
- each suspension is a well-founded `Comp` segment, ending in either a result or the next suspension;
- an observer recurses structurally through a segment, and uses up fuel moving on to the next.

That invariant is needed only if ordinary forwarded operations *don't* use up fuel. If they do, as in the machine experiment above, it isn't needed, which is the simpler choice to start with.

That's a direction, not a specification. It also needs a definition of what fuel counts:
- **What produces a step?** Counting steps isn't wall-clock time, and can't interrupt a blocking foreign call.
- **Do ordinary operations use up fuel?**
- **Must program transformations preserve the exact count?**
- **Is fuel per path or shared?** In the machine sketch, a multi-shot handler that resumes twice gives each resumption the remaining fuel, so `allResults` can explore more steps in total than the budget, though each path respects it. That's not a soundness problem, but it's an observable policy, and a shared budget would make handler order matter.
- **What a total step guarantees.** It bounds the number of steps, not how long each one takes, and a request to the host may block.

## Until then

Bounded algorithms take explicit fuel, as now (DESIGN.md §5). DESIGN.md's earlier decision to postpone a generic `withFuel` stands.
