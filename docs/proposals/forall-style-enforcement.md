# Keeping the ∀ house style (SW-2595)

Status: options note, for Matt's decision. Costs are estimated, not measured.

## The problem

SW-2587 added `∀ (x: T) => P`, and SW-2588 swept std, aoc and rogue so every
quantified statement uses it (about 3,100 rewrites). Nothing stops the next
statement being written `(x: T) -> P` again, by a person or a lane agent
who reads the guide less closely than they copy a neighbour's old habit.
The tree then slowly drifts back, and the next sweep is another overnight
lane.

The hard part is that `->` is right for a function type (`(n: Nat) -> Vec n`)
and wrong for a statement. Only the type of the result tells them apart, so
any rule has to know whether the result is a proposition.

## The options

**(a) `stitchwort fmt` rewrites it.**
- User-visible: saving a file in VS Code quietly turns `->` into `∀`.
  Nothing to learn, nothing to fix by hand.
- Catches: the clear cases (an equation, `∧`, `∨`, `¬`, `∈`, a comparison
  after the arrow).
- Misses: anything where the answer depends on a type, such as `p n` with
  `p: Nat -> Prop`, or a call of a definition that ends in `Prop`. The
  formatter reads only syntax (`crates/fmt` depends on `stitchwort-syntax`
  alone), so it can't see those. It must also guess wrong never: turning a
  real function type into `∀` changes nothing in the term but reads as a
  false claim. The sweep script needed a hand-built list of `Prop` names to
  get this far.
- Cost, estimated: 2 to 3 days. The formatter promises to keep every token
  and checks that its output is "the same program", so rewriting tokens is a
  new kind of rule, and the self-check has to learn that `->` and `∀` are
  the same term. Then a name-guessing heuristic and its tests.
- Risk: a heuristic formatter is a surprise machine; a wrong rewrite
  happens silently on save.

**(b) `check` warns.**
- User-visible: a yellow squiggle on `->` that says "this is a statement;
  write `∀ (x: T) => P`", with a quick fix in the editor. You see it as you
  type, and only where it is right.
- Catches: everything the printer already recognises as a proposition,
  including variables with `Prop` types. The printer (SW-2592) already makes
  this exact decision when showing goals, so the rule exists.
- Misses: nothing it can type; skips files that fail to elaborate. Doesn't
  fix files by itself unless we add the quick fix.
- Cost, estimated: 1 to 2 days. `check` has a warning channel (`W-` codes),
  and the printer's "is this a proposition" test can be reused. It needs the
  source span of the original `->`, since elaboration keeps the term but
  may drop the token, plus a test per case. A new warning code, and a rule
  for unused-binder chains (keep as arrows, as the guide says).
- Risk: warnings in std and aoc must be zero first (the sweep leaves
  binder chains of unused names and the examples, so a short follow-up
  sweep comes first). Every future message is noise if the rule is wrong.

**(c) A test runs the sweep rule over std, aoc and rogue.**
- User-visible: nothing in the editor. A lane or CI fails with "std/Foo.sw:12
  should use ∀", after the fact.
- Catches: new drift in the three trees, at about the sweep script's
  accuracy (token-level, so it has the same blind spot as (a)).
- Misses: user code outside those trees; typed cases. The script is Python
  and read-only today; the project is Rust and Nix, so it would need
  porting or a new test dependency.
- Cost, estimated: half a day to a day if it wraps the script, 2 days to
  port it to Rust.
- Risk: another test in a budget that is already tight; a false positive
  blocks a merge rather than annoying one person.

**(d) Do nothing; rely on review and the guide.**
- User-visible: no change. Drift appears now and then in diffs.
- Catches: whatever a reviewer notices. Misses the rest.
- Cost: nothing now; a later sweep, about 30 minutes of a Sonnet lane
  (SW-2588 took 30 min), repeated whenever the drift is bad enough.
- Risk: the orchestrator already reviews every diff and has plenty to
  look at. Style review is a poor use of that.

## Recommendation

(b), a `check` warning, because it is the only option that is both exact
(it uses types) and visible to the author at the moment of writing. Estimated
1 to 2 days, after a short follow-up sweep so the trees start at zero
warnings. Do (d) in the meantime: SW-2588 showed a sweep is cheap (estimated
30 min), so there is no hurry. Skip (a): its blind spot is the very case
that needs types, and silently rewriting on save is the wrong kind of
surprise. Skip (c) unless (b) is deferred for long, as a cheap stopgap
(estimated half a day).

## Built (SW-2658)

Option (b): `W-ARROW-FORALL`, with the quick fix "Write ∀ instead of ->". The
elaborator proposes a candidate at each explicit named binder group whose
function type is a proposition over a type that isn't one and whose variable
occurs in the body (so an unused name stays an arrow); `->`, `∀` and a
header's parameters are one tree, so the driver (and the library loader) keep
only the candidates whose group is followed by an arrow in the file's text.
The library has none (`the_library_writes_its_statements_with_forall`).
