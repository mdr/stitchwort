# Should a reference to a definition leave out its inline proofs? (SW-4782)

Paper note, 25 Nov 2026. Read from the code and the docs; nothing was built or run. Every
claim about current behaviour has a file and line; what I couldn't verify is marked.

## Summary

**The problem.** Re-proving a theorem moves no other declaration's hash (rule I of
sealed-theorems.md §3.8, SW-4701). A proof written *inside a definition* still does: an
inline invariant, `Quot.lift f (proof)`, `[decreasing := p]` or the proof `auto` finds for
it, a `match` lifted from a definition's proof. Edit one and the definition, every caller,
their tests' cache keys, any native pin above it and every namespace above it in the check
cache all move (trial-promises-after-rule-i.md, case 1).

**The question.** Hash a reference to a definition as its *proofless* hash
(`hash::proofless_hash`, which exists), so the edit moves only that definition's own hash?

**The answer: no, and do something else instead.** Proofless references would be right for
what a *run* computes, but a definition's body, unlike a theorem's proof, is unfolded: the
kernel and the elaborator read it, copy pieces of it into other declarations, and in three
places still tell two proofs apart (section 2). Making that safe means trusting that every
reader of a body ignores its proof positions, and it still wouldn't give the gain that
matters (the check cache re-checks callers anyway, section 3). The same end is reached with
no new trust by **moving each inline proof out of the definition into a sealed auxiliary
theorem** when the definition is elaborated, as Lean does. The body then holds a call of a
theorem, which rule I already covers everywhere: hashes, the digest, stage 3, the editor.

## 1. What each hash is used for

Two hashes exist per definition. The content hash (`def_hash`, `hash.rs:123`) refers to a
final theorem by its statement and to anything else by its full hash (`hash.rs:714-717`,
`has_interface` = `Def::proof_hidden`, `globals.rs:360`). The proofless hash
(`hash.rs:127-147`) replaces every proof position by one marker and refers to everything by
its proofless hash; its doc says "it decides nothing the kernel accepts, and nothing is
cached by it" (`hash.rs:142-145`).

| Consumer | Reads | Right with proofless references to definitions? |
|---|---|---|
| Test-result cache (`test_run.rs:326-352`, key = test's `def_hash` plus the goals it relies on) | what a run computes | **Yes.** A run erases exactly the positions the proofless hash blanks (`erase.rs:7-41` against `hash.rs:131-136`), and the goals a test relies on are found by walking bodies (`assume.rs:181`), not from the hash. One caveat, which holds today for theorems too: a false `?` can change a run (`erase.rs:56-64`); the key's goals cover it |
| Native pins (`pins.rs:215-223`; runtimes, `rt/natives.rs:223`) | "the declaration the native was written for" | **Yes for what it computes**, with fix 2.1. A callee's inline proof can make the kernel's unfolding *stuck* where a native answers, never give another answer. But a pin is also a statement that someone re-read the declaration; hiding callees' proofs from it is a (small) trust change, Matt's |
| Check-cache keys | text and dependencies' digests, not hashes (interface-digest-cache.md §1.2) | Not affected by the hash at all: see section 3 |
| Check-cache dependency records (`cache/mod.rs:2036-2050`, compared on decode at `4157-4170`) | "this outside declaration is what the entry was made with" | **No, for carried-over hits.** There the comparison is the correctness check (docs/core.md, "A carried-over hit"), and the claim it supports is "never a term this kernel wouldn't accept". Section 2 shows three ways that fails |
| Decode self-check (`cache/mod.rs:4547-4565`) and the digest's per-declaration hash (`3246-3253`) | the declaration's own hash | Unaffected: a declaration's own hash keeps its own proofs |
| `hash_stability` snapshots (`driver/tests/library/hash_stability.rs`) | regression net for the hash function | Fine either way; they would move once |
| Trial promises, `rename`, `oracle readings/builds` (`live/trial.rs:98-113`) | `SameMeaning`: full hash; `ProofsOnly`: proofless | `ProofsOnly` already is this comparison, as an advisory. Finding 2.1 applies to it today |
| `declhash` listings, `counterexample` (`type_hash`), `chars.rs` | reports | Unaffected |

So for running, the answer is yes. The trouble is everything that stands for a *checking*
verdict.

## 2. Where a proof inside a definition changes what the kernel or the elaborator does

Rules I, K, S and F say a proof never decides what computes or what is equal (docs/core.md
"Proof irrelevance", line 301 on). `decreasing` is safe by construction: the fuel is a
number and the proof only makes the `Zero` branch absurd (docs/core.md:241-247), and
`Quot.lift`'s fifth argument is never applied. But the rules are about *proofs as values*;
the proofless hash is about *positions in a term*, and they differ:

1. **A cast's ends are not in the proofless hash.** Rule K computes `J P d p` into data
   exactly when the two ends of `p`'s equation are convertible, and the kernel stores those
   ends *on the proof*, as `J(P, d, Ann(p, Eq(A, x, y)))` (`term.rs:276-282`, `j_ends` at
   `553-564`; read by `value.rs:2037-2042` and `2346-2352`). The proofless hasher blanks the
   whole third argument (`hash.rs:923-926`), ends included. With a motive that ignores its
   index, `J (y e => Nat) 5 (p: 2 = 2)` and `J (y e => Nat) 5 (q: 2 = g 7)` (`g` opaque,
   `q` a lemma) have one proofless hash; the kernel computes the first to `5` and leaves the
   second stuck, so `theorem t: f = 5 := byComputing` checks against one and not the other.
   **[Read from the code; no fixture written.]** Fixable (hash the annotation, blank only
   the proof under it), and worth fixing for `ProofsOnly` whatever is decided here: the
   sentence in trial-promises-after-rule-i.md that a held proofless hash "means the checker
   can't tell the two apart" is not true of this case.
2. **Rule I is deliberately incomplete.** Where a value's proof mark is *unknown* (the
   variable eta makes for a partial application, helper walks under a function type), "rule
   I doesn't fire" and the two proofs are compared as terms (docs/core.md:311, "costs only
   completeness"); the unifier pairs two proofs in a first-order call "only once their types
   have been unified, and otherwise only if they are the same value" (docs/core.md:310,
   condition D). So there are comparisons whose answer depends on *which* proof a callee's
   body holds. For theorems this can't arise, because the proof never leaves the theorem.
   **[From the spec; I did not construct a program that shows it.]**
3. **Bodies are copied out.** Unfolding `f` puts `f`'s inline proof into the caller's goal,
   and from there into the caller's elaborated terms: generated equations and `f.unfold`
   state the body's leaves (the elaborator reads computing bodies at 20-odd sites,
   interface-digest-cache.md §2.1's table), rewrite motives are read back from goals. A
   caller's *own* term can therefore contain the callee's proof, sometimes at a position
   that is not a proof position there (`g x p` unfolding to `id {P x} p`: only arguments of
   a definition's proof parameters are blanked, `hash.rs:541-551`). The caller's hash then
   moves honestly on a fresh check, and would be stale on any replay keyed without proofs.
4. **Step counts.** The checker doesn't erase (`erase.rs:69-71`), so a proof argument in an
   unfolded body is evaluated as far as a frozen call's arguments go; another proof costs
   other steps, and a caller near its budget could pass with one and report `E-RESOURCE`
   with the other. **[Not verified how much of a proof argument the kernel's evaluator
   forces.]** Marginal, but it is a verdict the hash would no longer cover.

None of these proves `False`: in the model the proofs are equal and the cast is the
identity. What breaks is the cache's contract, "a hit is what a check would produce", for
anything keyed on the weaker hash: an entry accepted on a hit that this kernel, checking
from source, would refuse (1, 2, 4) or would build differently (3).

## 3. The check cache, stage 3 and the editor

The hash change alone buys little. A namespace's key covers each dependency's *interface
digest*, which keeps every computing definition's body in full and leaves out only bodies
for which `has_interface` holds (interface-digest-cache.md §1.3, the "Its body" row). So an
inline-proof edit would still re-check every namespace above, with or without proofless
references. To cut that off, the digest would also have to drop proof positions inside
kept bodies, and its trust argument (P2, "elaborating `N` never reads the body of a
declaration for which `has_interface` holds", §2) would become "never reads a proof
position inside any body", which items 2 and 3 above contradict.

Stage 3 (parallel-checking-stage-3.md §1): the interface pass checks definitions and
theorems' statements and leaves proofs to proof jobs. A "type + proofless body" interface
would mean a definition admitted with holes where its proofs go, a new kind of kernel
object that unfolding then copies into dependants. A stated theorem is only a constant;
this would not be. The editor replays by namespace through the same keys (§4 of the digest
note), so it follows whatever the digest does.

## 4. Options

**A. No change.** Sound, simple. Inline-proof edits keep cascading. How often that hurts is
not measured: nobody has counted proof positions in computing definitions across std, AoC,
the roguelike and `tools/fmt`.

**B. Proofless references for definitions** (the question as asked). Needs fix 2.1, a
decision that pins may ignore callees' proofs, and either acceptance of 2.2-2.4 for
carried-over replay or keeping full hashes there (two reference hashes per definition).
Gains: test results and pins survive a callee's inline-proof edit. No check-cache gain
without the digest change of section 3, which I'd not make. The trusted claim grows from
"a theorem never unfolds" (one predicate, `value::frozen`) to "every reader of an unfolded
body ignores proof positions".

**C. Proofless only at chosen positions** (say `decreasing` and `Quot.lift` proofs, whose
type the surrounding term fixes). A subset of B with the same copying problem (2.3) and a
third hash to explain.

**D. Take the proofs out: abstract nested proofs into sealed theorems.** When a `def` is
elaborated, each proof at a proof position that isn't already trivial (a variable, a call
of a theorem on variables) becomes an auxiliary theorem over the local context,
`f.%proof1 (x…) (h…): P x…`, and the body holds the call. Lean 4 does this for every
definition (`Lean.Meta.abstractNestedProofs`, "Replace proofs nested in `e` with new
lemmas", skipping trivial proofs and ones containing `sorry`; checked today against
`src/Lean/Meta/AbstractNestedProofs.lean` on lean4 `master`). Then, with no new rule:

- the definition's hash covers the *statement* of each of its proofs (its interface hash),
  so editing an inline proof moves the auxiliary theorem's full hash and nothing else, not
  even the definition; callers, tests and pins stay;
- the digest already leaves the auxiliary theorem's body out, so namespaces above replay;
- stage 3's interface pass can leave it stated like any theorem, so inline proofs
  (including `auto`'s search for a `decreasing` proof) move to the proof jobs;
- copying is harmless: what unfolding copies is the call, the same before and after;
- a cast's ends are in the auxiliary theorem's statement, so 2.1 can't arise;
- goals show `f.%proof1 x h` where they showed a proof term;
- `ProofsOnly` has almost nothing left to accept that `SameStatement` doesn't, and the
  proofless hash could later be retired.

What D needs designing (not done here): closing a proof over a `match` branch's refined
context (the lifted-`match` machinery has the same captures problem and solves it); whether
an inline proof with a `?` is lifted (Lean doesn't; an assumption is already its own
declaration here); naming and numbering that stay stable under edits elsewhere in the
body; display and navigation into the lifted proof; and a measured count of how many
proofs it would lift and what it does to check time.

Two small extensions belong with it. A **`def` whose type is a proposition** is frozen by
rule F already but cited by its full hash (sealed-theorems.md:390-393); citing it by
statement needs `Def::computing_body` to hide it too. A **computing definition in a group
with a theorem** has the theorem's proof in the group hash (docs/core.md, "A theorem in a
group…"); the proofless hasher already splits such a group (`hash.rs:233-250`), and the
content hash could do the same with the theorem's statement kept.

## 5. Recommendation

Not B or C. Keep "a reference to a definition is its full hash": a definition is what it
unfolds to, and that includes the terms at its proof positions as long as they are in the
body. Reach the goal by D, as its own design note and decision, preceded by a count of
inline proofs in computing definitions (a cheap `declhash`-style report: declarations
whose proofless hash differs from their content hash for a reason other than a theorem
reference). If the count is small, A is the end state and nothing is built. Independently,
fix 2.1 in the proofless hasher, since `ProofsOnly` relies on it now.

## Decisions for Matt

1. **Identity of a definition.** *Problem:* editing a proof inside a definition moves the
   hash of everything that calls it. *Change asked about:* cite definitions without their
   proofs. *Effect:* tests and pins would hold, but a cache hit could stand for a check
   this kernel wouldn't repeat, and the check cache wouldn't re-check less. **Rec: no;
   a reference to a definition stays its full hash.**
2. **Lifting inline proofs (option D).** *Problem:* the same cascade. *Change:* the
   elaborator moves each proof inside a `def` into a hidden theorem beside it, as Lean
   does. *Effect:* an inline-proof edit re-checks one namespace and moves no caller, test
   or pin, with the trust unchanged; goals show a name where they showed a proof term.
   **Rec: count first, then a design note if the count justifies it.** It changes
   elaborated terms and what users see in goals, so the design is his.

## What I could not verify

- No fixture for 2.1, and no program exhibiting 2.2; both are read from code and spec.
- How much of a proof argument the kernel's evaluator forces (2.4).
- That generated equations copy proof terms out of leaves verbatim (2.3): inferred from
  the read sites listed in interface-digest-cache.md §2.1, not read line by line.
- How many inline proofs computing definitions hold today.
- The JS and runtime pins beyond `rt/natives.rs:223`.
