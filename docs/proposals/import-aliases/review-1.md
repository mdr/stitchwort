# External review 1 of the import-names design

Received 30 October 2026 on the reviewer brief (review-brief.md), pasted verbatim. "Import Names Review" and links are the reviewer's citations.

Overall, I think this is a **good proposal and I would approve Stage 1 (b′)**, with a few changes to the collision rules. I would **not implement Stage 2 yet**, and I agree with deferring arbitrary `as` aliases.

The strongest part of the proposal is that it has identified a much narrower problem than “Stitchwort needs module aliases.” The actual need is: *given `Shop.Spec`, let me deliberately bring the qualifier `Spec` into scope*. The corpus evidence is unusually useful here: project-qualified names occur only four times in real code, none of those four actually required qualification, and the stronger evidence is behavioral—both the agent and maintainer naturally tried to get to `Spec.f`. Import Names Review

The proposed:

```text
import Shop (Spec)

theorem emptyAgrees:
  total [] = Spec.total [] := rfl
```

is therefore a very nice fit. It repairs something the documentation already says should work, uses existing syntax, doesn't introduce another spelling for the namespace, and works with the existing pasteable-name printer. Import Names Review

## My main recommendation

I'd phrase the design principle as:

> **Namespaces are importable named entities for qualification purposes, but importing one does not open its contents.**

That feels simpler and more general than thinking of this as a special “subnamespace naming” feature.

In other words, if `P.S` is a namespace, then:

```text
import P (S)
```

puts the namespace `P.S` in scope under its canonical final component `S`, exactly as importing a type puts that type's name in scope.

That's a coherent module model. The distinction then becomes:

```text
import P (S)     -- bind the qualifier S
import P.S (x)   -- bind x
import P.S (..)  -- bind P.S's contents
```

Those are three pleasantly orthogonal operations.

### The biggest issue I see: R3 is a little inconsistent

R3 currently says that importing `S` is rejected immediately if `S` already denotes certain kinds of qualifiers, but two imported namespaces both called `S` are permitted and become `E-AMBIGUOUS` only upon use. Import Names Review

I'd reconsider that asymmetry.

Suppose you have:

```text
import Day12 (Spec)
import Day13 (Spec)
```

and never write `Spec.foo`. Under the proposal this is accepted.

But if there happens to be a root `Spec` namespace, apparently:

```text
import Day12 (Spec)
```

is immediately rejected.

That makes the user's mental model depend on *where the competing qualifier came from*, which isn't especially valuable.

I think Stitchwort already has a good principle:

> competing things at the same resolution level are tolerated until somebody actually asks for the ambiguous spelling.

I'd seriously consider extending that principle to qualifiers too.

Something like:

```text
Spec.foo
```

→

```text
[E-AMBIGUOUS] `Spec` could mean
  Day12.Spec
  Day13.Spec

write `Day12.Spec.foo` or `Day13.Spec.foo`
```

You could still make local declarations/current-namespace meanings outrank imports, exactly as ordinary names do.

There is precedent for this general philosophy. Haskell imports are cumulative and ambiguity is normally diagnosed when an ambiguous name is referenced rather than because the imports coexist. [haskell.org](https://www.haskell.org/onlinereport/haskell2010/haskellch5.html?utm_source=chatgpt.com) Lean similarly permits multiple opened namespaces and can retain multiple candidate identifiers until elaboration resolves them—or report ambiguity if it cannot. [Lean Language](https://lean-lang.org/doc/reference/latest/Terms/Identifiers/?utm_source=chatgpt.com)

I don't think you need Lean's *type-directed* ambiguity resolution, but its distinction between “there are multiple candidates” and “the program actually contains an ambiguous reference” is useful.

## Stage 2: I would defer it

This is the part I feel most strongly about.

Stage 2 says:

```text
import Aoc.Year2024.Day13 (..)
```

would implicitly make immediate subnamespace `Spec` available, so that:

```text
Spec.fewestTokens
```

works without:

```text
import Aoc.Year2024.Day13 (Spec)
```

Import Names Review

I don't think you've established a need for that yet.

It saves exactly one very descriptive import:

```text
import Aoc.Year2024.Day13 (Spec)
```

at the cost of making `( .. )` considerably more magical.

In particular, a namespace addition elsewhere can now alter name resolution in an importing file:

```text
-- yesterday
import Foo (..)

-- later somebody adds Foo.Spec
-- suddenly `Spec` is in this file
```

That's precisely the kind of implicit environmental change that tends to be unpleasant in large programs—and probably particularly unpleasant for coding agents.

The proposed “dependency edge only when the qualifier is actually used” is clever implementation-wise, but doesn't solve the cognitive issue. The source says `(..)`, not “import these values plus potentially some namespace qualifiers”.

And your own data actually argues against Stage 2: the requirement is tiny. Stage 1 gives agents exactly the spelling they were trying to achieve, explicitly.

So I'd do:

**b′ now → instrument/observe → only add b″ if repeated friction appears.**

Agda indeed has a much richer module/open system, including renaming, selective opening, and public re-export. [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/module-system.html?utm_source=chatgpt.com) But I wouldn't infer from Agda that Stitchwort should automatically make its namespace model similarly permeable.

## Answers to the six questions

**1. Is b′ enough, or should `as` exist because agents try it?**

**b′ is enough for now.**

The crucial distinction is between *discoverability* and *capability*. Agents try `as` because it is a common syntax from Python, Haskell, Agda, Scala, Rust-ish experience, etc. That doesn't mean they actually need arbitrary aliases.

Your proposed diagnostic is exactly the right solution:

```text
import Shop.Spec as Spec
                 ^^
Namespaces use their own name as the qualifier.
Write: import Shop (Spec)
```

I'd make this a specially recognized parse error rather than merely whatever generic parse failure happens to arise.

You've then converted a predictable agent prior into a one-step learning experience.

And your “adding it later only turns an error into a program” argument is excellent. Import Names Review

So I wouldn't spend language complexity now on a feature for which the corpus has essentially no semantic need.

---

**2. Should R3 refuse qualifier collisions rather than hiding?**

**Do not silently hide. But I would lean toward ambiguity-at-use rather than import-time rejection.**

Silent shadowing is particularly bad for qualifiers because:

```text
Spec.foo
```

looks deliberately qualified. A reader reasonably expects `Spec` to have a stable identity.

I'd therefore choose one of:

```text
E-IMPORT-CLASH
```

or ambiguity at use, never “most recent one wins”.

Of those two, I slightly prefer ambiguity at use because it matches Stitchwort's existing behavior for competing named imports and permits harmless imports to coexist.

Current-namespace/local-name precedence can still beat imports.

---

**3. Should `( .. )` bring subnamespaces?**

**Not yet.**

The benefit is one fewer import line.

The cost is:

- more implicit scope;
- new ambiguities caused by adding namespaces upstream;
- harder inspection of where `Spec` came from;
- a changed meaning for existing `( .. )`;
- hidden dependency relationships;
- names such as `Spec`, `Proofs`, `Test`, `Util`, `Internal` becoming ambient qualifiers.

For an AI-agent-oriented language, I'd actually weight **explicitly reconstructible scope** rather highly.

`import P (Spec)` is extremely cheap.

---

**4. Is inability to short-name two `Spec`s a serious limitation?**

**No, not enough to justify aliases today.**

The obvious bad case is something like:

```text
Day12.Spec.foo
Day13.Spec.foo
```

in a cross-day comparison.

But the fallback is perfectly serviceable:

```text
import Day12 (Spec)
Spec.foo

Day13.Spec.foo
```

or just use both full names.

This is exactly the kind of uncommon case where a slightly more verbose spelling is preferable to making the whole language more complicated.

If real Stitchwort evolves toward heavy use of similarly named sibling modules—`Client.Types`, `Server.Types`, etc.—you may eventually get evidence for aliasing. You don't have it now.

---

**5. If aliases eventually exist, what should the printer print?**

This one has a clear answer:

**the alias. More precisely: the shortest name that actually resolves to the intended declaration in the current file.**

Do not sacrifice the existing pasteability invariant.

The document says the printer currently tries suffixes shortest-first and prints the first one which resolves to the intended declaration. Import Names Review That's a very strong rule.

If someday:

```text
import Aoc.Year2024.Day13.Spec as Oracle
```

exists, and only:

```text
Oracle.f
```

resolves, print that.

A goal being slightly different between files is far less harmful than the compiler printing syntax that **cannot be pasted back into the file**.

I would actually elevate this to a language/tooling invariant:

> **Every source-level name emitted by diagnostics should resolve to the entity it denotes when pasted at the diagnostic location, whenever such a spelling exists.**

That will serve you far beyond this feature.

---

**6. Is there another module-system idea worth studying for program/spec pairs?**

I don't think `export`/`open public` solves this particular problem.

Lean's `export` introduces names from one namespace into another namespace, and `open` controls lexical visibility; its current documentation also makes explicit that opened namespaces participate in qualified-name resolution. [Lean Language](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/?utm_source=chatgpt.com) Agda's `open … public` is primarily a **re-export/composition** mechanism. [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/module-system.html?utm_source=chatgpt.com)

Those are useful if you want to construct APIs:

```text
MyPrelude
    re-exports A
    re-exports B
```

but that's not really your situation.

The “program vs spec” relationship looks semantic to humans, but the namespace system need not know about it. I think:

```text
import Day13 (Spec)
```

already captures exactly the relationship you need.

If this pattern becomes extraordinarily common, I'd sooner consider a **project convention**:

```text
Foo
Foo.Spec
Foo.Proofs
Foo.Tests
```

than add language semantics specifically for specs.

## A couple of smaller observations

The proposal resolves one of its own literature uncertainties. Current Lean documentation explicitly describes qualified identifiers as also being tried relative to opened namespaces: if `Q` is open, a qualified identifier can be resolved with `Q` prepended. So the uncertainty noted in §5 about something like `open A` followed by `B.x` can essentially be answered **yes, provided `A.B.x` is a valid resolution candidate**. [Lean Language](https://lean-lang.org/doc/reference/latest/Terms/Identifiers/?utm_source=chatgpt.com)

The Rust inference also looks sound: Rust's `use` imports *items*, and modules are importable items; `use path::m` gives you `m::...`, while `use ... as ...` can rename that imported item. [Rust Documentation](https://doc.rust-lang.org/stable/core/keyword.use.html?utm_source=chatgpt.com) So I'd tighten those two entries before publishing another draft. The proposal currently marks both as unsettled. Import Names Review

I would also be careful about R2's statement that imported namespace items simply “sit with names imported by name.” Qualifiers and term/type names clearly interact in resolution, but conceptually I would model **imported qualifier bindings** explicitly even if they happen to share a priority tier. That will make the implementation easier to reason about when you later get cases involving types-with-owned-namespaces, abilities, root namespaces, and perhaps aliases.

## Verdict

I'd ship the design approximately as:

```text
import P (S)
```

where `P.S` may be either a declaration or a namespace.

If it is a namespace, `S` becomes a canonical qualifier for `P.S`. It imports **none of `P.S`'s contents**. It is file-local and adds the required dependency. Full names always remain available.

I'd change/clarify **R3 so qualifier conflicts never silently hide one another**, and I'd strongly consider diagnosing conflicts at use rather than at import.

Then stop there.

**No `as` yet. No subnamespace propagation through `( .. )` yet.**

That gives Stitchwort the desirable `Spec.foo` spelling the evidence actually supports, fixes an existing documented inconsistency, preserves deterministic/pasteable diagnostics, and introduces essentially no new conceptual machinery. That's a very good complexity-to-benefit ratio. Import Names Review