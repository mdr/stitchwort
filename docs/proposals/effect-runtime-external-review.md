# External review of the effect runtime report (D1162)

Received 24 Oct 2026, reviewing [effect-runtime-review.md](effect-runtime-review.md) (sent with a context preamble). Verbatim, except that the chat client's "Pasted text" citation markers are removed.

This is a strong proposal. I think the central recommendation is right: **adopt A + lazy resumption, keep the native `Done` fast path, fix IO routing, and treat CPS/evidence passing as future architectural options rather than prerequisites.** The document has also found a materially important hole in the original design: making `bind` stack-safe is insufficient if calling a handler resumption immediately re-enters the handler recursively.

I would approve it with a handful of changes, two of which I think are significant.

### 1. The lazy-resumption argument looks sound

I buy the core argument.

The semantic equation is:

`foldComp d c (Call o r) ≈ c o (y => foldComp d c (r y))`

and for a generated handler, the result of that fold is itself a computation in the enclosing row. If instead of evaluating that continuation immediately you return something equivalent to

```text
bind (Done y) (\z -> foldComp ... (r z) ...)
```

then `bind (Done y) k ≈ k y` gives you exactly the old tree semantics. Since the runtime representation of `Comp` is abstract to executing Stitchwort programs, that extra suspension is not observable through pattern matching or representation inspection.

I would strengthen §5.2 by actually presenting this as a tiny equational proof rather than mainly an argument from carrier type. Something like:

```text
k_eager y
  = foldComp d c (r y)

k_lazy y
  = Bind (Done y) (\z -> foldComp d c (r z))

run(k_lazy y)
  ≈ bind (Done y) (\z -> foldComp d c (r z))
  ≈ foldComp d c (r y)
  = k_eager y
```

Then explicitly cover the potentially worrying cases:

- **discarded continuation:** neither representation executes it;
- **single resumption:** equivalent by the bind law;
- **multiple resumptions:** each gets the same immutable captured `pending`;
- **stored continuation:** storing the suspended representation is fine;
- **deep handling:** `fold` is still present around `rest`;
- **effects before/after the resumption:** enclosing-row sequencing is represented by `bind`, so effect order is preserved.

That would make Q1 considerably easier to sign off.

The one qualification I'd add is that this is sound **because runtime `foldComp` has been effectively sealed**. Your R2 restriction is doing real semantic work here, rather than merely being an implementation detail.

### 2. I would soften the claim that the empty-row case is “inherent”

This is the largest conceptual point I'd change.

You convincingly establish that it **cannot be fixed merely by changing the `Comp` runtime representation**. At the empty row:

```text
Cons v (k ())
```

really has become ordinary pure non-tail computation, and `runPure(k ())` is demanded before `Cons` can be returned.

But:

> “No change confined to the runtime fixes that in JS.”

is narrower and more defensible than:

> “One case remains, and it is inherent.”

The limitation is really:

> **inherent under Stitchwort's current empty-row calling convention unless code consuming resumptions is itself transformed.**

There is a fourth family of solutions between “change `k`'s source type” and “Stopify all JavaScript”: **compile handler clause continuations specially**.

For a clause such as:

```text
emit v, k => Cons v (k ())
```

the compiler could in principle defunctionalise the pure context around the resumption into something like:

```text
Resume k () ; then Cons v □
```

and let the handler machine execute that context explicitly.

That preserves the *source* type of `k`; it is a backend/control transformation rather than necessarily a type-system change.

It doesn't solve everything cheaply. Your `Each.both (b => k b)` example is exactly the hard case: `k` escapes into arbitrary ordinary higher-order code. Handling that generally pulls you towards selective CPS/defunctionalisation of a larger region.

So I **still agree with your practical recommendation to accept the limitation for now**. I just wouldn't call it fundamentally inherent. I'd describe option 4 in Q2 as:

> selectively CPS/defunctionalise handler clauses (and, where required, pure code through which resumptions escape), preserving source-level `k : res -> r`.

That makes the design space complete and explains why you're not choosing it.

### 3. I wouldn't put A′ in the elaborator if you can avoid it

The proposed choice in Q5 feels unnecessarily binary:

> recognise parameterised handlers in the elaborator, or expose surface syntax.

There's an attractive third answer:

**recognise them in a post-elaboration optimisation / backend IR.**

You already have the crucial abstraction principle: runtime representation isn't part of the semantics. The state handler

```text
return x       => s => x
next (), k     => s => k s (s + 1)
```

has a recognisable elaborated shape. Turning that fold into a loop does not need to alter what the Stitchwort term means.

That has two advantages:

1. **No content hash changes.**
2. A′ becomes what it really is: a handler optimisation, rather than a special semantic elaboration rule.

I'd only add surface parameterised-handler syntax if you independently think it improves the language.

So my recommendation for Q5 would be:

> backend/core optimisation first; surface syntax only if parameterised handlers deserve first-class language ergonomics.

### 4. Keeping the native stacks separate is the right stage-4 design

Your discovery about the existing `IO` runner scan is important. If every pending `Comp` bind becomes one more frame traversed by every operation, you've removed one quadratic algorithm and created another.

For this stage I'd choose:

**`Comp` continuation stack separate from `Delay`/runner frames.**

An alternating segmented continuation à la Links/Effekt may ultimately be more elegant, particularly if Stitchwort later wants cheap capture relative to handler depth rather than ordinary control depth. But it increases the conceptual scope of D1162 enormously.

I'd make the invariant explicit:

> Running an operation must not inspect ordinary `Comp` continuation frames individually.

Then test that invariant directly, rather than relying solely on timing.

### 5. The immutable list is the correct baseline; chunking is the obvious next experiment

I wouldn't delay stage 4 looking for a cleverer structure.

An immutable cons stack gives you unusually clean multi-shot semantics:

- capture = pointer;
- resume = pointer;
- second resume = same pointer;
- push/pop = O(1) worst-case.

That is an excellent correctness baseline.

Your likely next optimisation is indeed some form of **persistent chunked stack**: e.g. blocks containing 16–64 continuation references plus a cursor/link, rather than one JS object for each continuation. That could substantially reduce headers, pointer chasing and GC object count while preserving sharing.

I'd be cautious about “mutable array, copy on second resumption”. The interesting event isn't really *second resumption*; it's **divergence after a captured stack becomes shared**. Getting ownership right in the presence of stored/multi-shot continuations can quickly become more complicated than the execution machinery itself.

So:

> ship cons cells → measure → try chunked immutable/persistent segments.

That is a much safer progression.

### 6. Your GC conclusion is plausible, but the measurement wording overstates it slightly

This sentence needs tightening:

> “About 80% of A's run time is garbage collection pauses.”

You say the GC statistics cover the **whole process, including construction of the input list**, whereas the “call time” appears to be the measured export invocation. Those aren't quite the same interval.

The huge difference in GC counts and heap footprint is compelling evidence that allocation is the dominant new problem, but I'd say:

> “GC pause time is of the same order as ~80% of the measured call time; because the GC trace also includes process/input setup, this is evidence that GC dominates the additional cost rather than an exact attribution.”

If possible, later use Node's GC performance events around the benchmark region or otherwise isolate the invocation.

The design conclusion doesn't change.

### 7. The acceptance criteria need deterministic complexity checks as well as timing

The expanded acceptance suite is much better than the original one, especially the addition of reader/writer/search shapes, wasm, memory and native regression.

But I wouldn't call

> each doubling ≤2.3×

a test for **linear growth**.

As you note earlier yourself, timing ratios won't reliably distinguish `O(n)` from `O(n log n)`, particularly under this much GC noise.

I'd use two layers:

1. **Structural/instrumented complexity tests**
   - number of `run` steps ≤ `C*n`;
   - continuation pushes/pops ≤ `C*n`;
   - operation routing examines ≤ `C*operations*handlerDepth`, not control-stack depth;
   - no rebuilding of a pending suffix proportional to its length.

2. **End-to-end performance tests**
   - median timings;
   - heap/allocation bounds;
   - stack safety at 1M;
   - native regression limits.

The first layer will catch accidental quadratic algorithms much more reliably than benchmarks.

I'd also add explicit cases for:

- handler nesting depth 10 or 100;
- repeated `translate`s around an operation;
- continuation captured and resumed after the original handler clause has returned;
- 0, 1, 2 and many resumptions of the same `k`;
- a stored resumption resumed in different branches;
- `IO` crossing many ordinary binds but few handler/translation frames;
- `Partial` mixed with another forwarded ability.

### 8. Keep the native `Done` fast path

This one looks clearly right.

The semantic equation literally gives you:

```text
bind (Done x) k ≈ k x
```

and native execution doesn't have JS's host-stack problem because the VM already owns its frames. Allocating an intermediate `Bind` node there would be paying for machinery solving a problem that doesn't exist on that backend.

I'd make this not merely an optimisation but an explicit backend invariant.

### 9. I agree with rejecting CPS and evidence passing *for this decision*

The §7 evidence is good enough to answer the engineering question:

> is there evidence that Stitchwort needs an architectural CPS conversion *before* trying the much smaller A design?

No.

Your models show that the loop implementation is competitive with CPS on exactly the workloads motivating the change, and lazy resumption removes much of the stack-safety argument for CPS.

I would slightly soften:

> “CPS stays rejected”

to:

> “There is no current justification for paying the architectural cost of CPS.”

The benchmarks are hand-written models rather than generated compiler output, something you correctly acknowledge. So they support *not choosing CPS now*, rather than a lasting conclusion that CPS can't win.

Likewise Koka-style evidence passing may become interesting later for fast handler lookup/forwarding. Nothing here requires adopting its continuation representation wholesale.

---

### What I would send back as the decision

I'd make D1162 approximately:

> **Adopt the `Done | Call | Bind` runtime representation with an explicit continuation loop. Handler resumptions produce suspended computations rather than recursively running the continuation. Continuation stacks are persistent, preserving unrestricted multi-shot semantics.**
>
> JS always uses the loop. Native retains `bind (Done x) k = k x` as a fast path.
>
> Parameterised empty-row handlers may be recognised and loop-fused as an optimisation, preferably after elaboration.
>
> `Comp` continuation frames must not cause operation routing to become proportional to ordinary control depth.
>
> Empty-row handlers which consume a resumption non-tail in pure code remain subject to ordinary JS stack limits in this stage. This is a consequence of the current pure calling convention, not of the `Comp` representation itself; selective transformation of such code remains a possible future solution.
>
> Correctness acceptance includes multi-shot, stored resumptions, nested handlers, forwarding, translation, `IO`, `Partial`, native and wasm. Complexity is checked with instrumented step/frame counts as well as wall-clock and memory benchmarks.

So overall: **yes, I'd proceed with A.** The new lazy-resumption result is the key insight in the review, and it makes the design substantially more convincing than the original note. My main requested changes would be to (1) weaken “inherent” to “inherent under the current pure calling convention”, (2) keep A′ out of elaboration/hashing if possible, and (3) add structural complexity assertions to the acceptance suite.