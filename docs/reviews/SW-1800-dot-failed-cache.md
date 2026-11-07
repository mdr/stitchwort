# SW-1800: the address-keyed dot-call caches

7 Nov 2026, Opus. From SW-1797's diagnosis.

## What the caches are for

`dot_heads` and `dot_failed` (`crates/elab/src/state/caches.rs`) came in
with SW-129 (5470ca67b, "Long dot chains: no exponential re-elaboration").
`call_or_block` tries a dot call as its prefix form first: it infers the
receiver to find the head, undoes that, then checks the receiver again as
an argument, and on a failure infers it a third time through
`dot_or_block`. Without the caches every level of `x.f.g.h…` would
re-elaborate everything below it two or three times. Both tables share one
key, `call_key`: the receiver's address, its span, the field's span and the
source epoch. `dot_failed` adds the metavariable state (count and trail
length), which a snapshot restore puts back, so the second visit of a
receiver after an undo finds the first visit's result.

The saving is not small. With `dot_failed` off, `long_dot_chains_are_cheap`
(60 levels) ran for more than 180 s before I stopped it; with it on it
takes 5 s. Removing the cache is not an option.

## What a hit may stand for

Two experiments, each over `hash_stability::{prelude, examples, projects,
a_namespace_checked_alone_has_the_same_hashes}`:

- **Both tables off (always a miss):** every hash is the same. A miss is
  always right. Only a hit can be wrong.
- **Structural key** (a hash of the receiver's `Debug` text in place of
  the address): the derived `ext` lemmas (`Board.Position.ext`,
  `Lib.Range.ext`, `Main.Point.ext`, …) stop checking (`<none>`). That
  stays so after adding the field's text, the local context (length and
  names), and emptying the tables before each declaration, with either
  table on alone. So a recorded result belongs to *one piece of syntax in
  one attempt*. Syntax that looks the same in a context that looks the same
  isn't enough: the elaborator state that matters (solutions, the expected
  type, the queue) isn't captured by any cheap fingerprint.

So the address isn't a poor stand-in for a structural key. Identity is
what's meant, and the address gives it only while the syntax stays
allocated. The hazard is a freed node whose address is reused.

## Where addresses get reused

1. **The queue's copies.** `queue_call` clones the receiver into a
   `DotCall`. The queue item is dropped on an undo, and the next copy may
   land at the freed address, with the same spans and, after the undo, the
   same metavariable state. That is the variation in
   `postponed-lambda-second-error` (a hit skips `prefix_form`: 20 steps).
2. **Across declarations.** The tables were only emptied on a rewind, or
   with `clear_caches_per_declaration`. Each declaration starts from a
   fresh metavariable state, and derived declarations from one `deriving`
   clause share their spans. A derived declaration freed, then the next one
   at the same addresses, could find the first one's entries. This is the
   likeliest *wrong* hit.
3. **Syntax the elaborator builds and frees within a declaration**: pipe
   desugaring (`pipe::as_call`), record arguments
   (`records::brace_arguments`), `effects::run_first`'s rewrites, and
   others. Not fixed (below).

## The change

- `glued` empties the two dot tables before every declaration
  (`Caches::forget_dot_calls`). The declaration's syntax is borrowed for
  the whole of `glued`, so it stays allocated while its entries live.
- `resume_item` hands each check it resumes to `Caches::keep_dot_owner`,
  which keeps the `Rc` until the tables are emptied. A queue copy's syntax
  then can't be freed while its entries live.

No hash moves (the four `hash_stability` tests pass). A copy that used to
hit by luck now misses, so `postponed-lambda-second-error` always takes
the larger count (8,888,188).

## Determinism

`dot_prefix::a_postponed_dot_call_takes_the_same_steps_every_time`
(`#[ignore]`, about 30 s) loads the file 102 times on three threads, each
load after freeing blocks of varied sizes. Before the change, 26 of 102
loads differed. After it, none do.

## Not fixed: syntax built and freed within a declaration

`reads-weaken-over-map-implicits` still varies (67,836,957 to 67,837,612
steps over 42 loads on three threads). Logging hits per load shows the
difference is in `dot_heads` hits on `read.all` in
`crates/elab/src/std/Parse/Reads.sw` (the lambdas under
`Parse.readsWeaken (Parse.readsBind …)`, offsets 33477 and 96932). That
is class 3: syntax the elaborator builds for itself. Covering it site by
site is fragile. Every place that builds an `Expr` and elaborates it would
have to keep it alive, and a missed site fails silently.

The robust fix is an identity that doesn't come from the allocator: node
ids from the parser, with each copy the elaborator makes getting fresh
ones or keeping its source's. That touches the syntax crate, so it is a
design question. Filed as a finding for the orchestrator. A cheaper
detector (in debug builds, assert that every keyed address belongs to
registered, kept-alive syntax) would find the sites, if the site-by-site
route is preferred.
