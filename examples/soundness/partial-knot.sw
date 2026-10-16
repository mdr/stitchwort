-- expect-error: E-PARTIAL
-- The `pfixBad` attempt (docs/proposals/partial.md §8.3): a description
-- given its own tied function, rather than requests that only the runtime
-- answers. If total code could ever step a `Delay`, a description could step
-- its own recursive call, and one "total" step would never return. Here the
-- description calls `bad`, the function being defined: that's running a
-- partial computation in code the elaborator doesn't treat as partial, so
-- it's refused. The kernel refuses the same thing written as core terms by
-- termination (`crates/core/tests/partial.rs`).
bad : Nat -> Delay NoOp NoRes Nat
bad = pfix (\x -> mapSig sigRight (bad x))
