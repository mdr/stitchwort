# Review of SW-3719: derived `==` and `<` laws through nested pairs

SW-3763, Opus, 17 Nov 2026. Branch `lane/SW-3719` at `380ded510`
(code commits `211ab5eee`, `7830bbdb7`, `a8f81e55e`), against `main` at
`2aeca9976`. Required by D2364: the derivers now generate different proof
terms, and `T.%C%unpack` and `T.%C%pack` are built directly as kernel terms.

## Verdict

**Merge with follow-ups.** Nothing bypasses the kernel, the derived
statements are unchanged, and every shape I probed behaves as on `main`.
The speed-up holds at sizes beyond what the lane measured, and there is no
stack overflow at 128 fields. Wide records are still cubic above about 32
fields, though: 64 fields take 9 s and 128 take 99 s. A follow-up should
profile that (finding 5).

## How it was checked

- I read the whole diff of `derive.rs`, `derive_ord.rs`, `OrdDerived.sw` and
  the tests, plus `kernel::declare_def` / `define_def` in `crates/elab` and
  `crates/core/src/check.rs`.
- I compared the `hash_stability::prelude` snapshot's declaration names, old
  against new.
- I ran small probes with `nice -n 19`, using both main's release binary
  (built 09:21 from main's elaborator as of `95002ca61`) and the branch's
  (built 10:19, after the last commit that changed code). The probe files
  are in the review lane's scratchpad. No suites were run.

## Findings

### 1. Statements unchanged (no issue)

The derived names are not reachable from source (`P.%sameSound` is
`E-PARSE`, and `stitchwort doc` doesn't list them), so I couldn't print
their types. I checked the statements three other ways:

- **Code.** `sound_signature` and `complete_signature` are built as before.
  The diff only moves their equations into the new `laws` list, which is
  defined after `proofs`. `derive_ord.rs` changes bodies only: no
  signature-building line is touched.
- **Snapshot.** No name was removed from the prelude snapshot. The names
  added are 46 `%sameIff`s, 20 `%unpack`/`%pack` pairs,
  `Std.Ordering.thenPairEqual` and `Std.Ord.instanceFor`. The other changed
  lines are hash changes. Hashes cover bodies, so a changed hash says
  nothing about the type. `data Std.Disk`'s hash also changes; the commit
  message explains this, since what uses std's derived instances changes
  with them.
- **Typing constraint.** `T.%decide` is still the record `{ holds = T.%same
  r s, sound = T.%sameSound r s, complete = T.%sameComplete r s }`, checked
  against `Decidable (r = s)`. If either law's type had changed, that record
  would fail to check. The `.read` theorems in my probes (`c = d` from
  `(c == d) = True`, and `c ≠ d`) also check on the branch.

### 2. Soundness: nothing bypasses the kernel (no issue)

`derive_tuple_in` declares `%unpack` and `%pack` through `declare_member`,
which calls `kernel::declare_def`, which checks the type, and then
`kernel::define_def` → `k::define_group` → `admit_group`, which checks the
body. That is the same path the derivers already used on `main` for
kernel-built `%tag`, `%C%k`, `%C%k%at`, `%view`, `%eta` and `%etaAt`.
`admit_trusted_group` is used only for the check cache's hashed bodies,
which is unchanged. All the source-built laws go through `definition` /
`definitions` as before.

So a wrong term fails. It fails softly, though: an error inside deriving
becomes the note "`==` isn't derived for `T`: deriving it failed: …" on the
type's first use of `==`, not an error at the declaration. The probe of
`type Big: Type 1` shows this path, which is the same on `main`. A bug in
the new term builders would therefore show up as missing `==`, which any
example that uses `==` catches.

The core additions say what their names claim:

- `Ordering.thenPairEqual`: from `andThen c d = Equal`, `c = Equal → x1 =
  x2` and `d = Equal → y1 = y2`, it proves `MkPair x1 y1 = MkPair x2 y2`.
  That is true and fits the name. Its doc explains the argument order.
- `Ord.instanceFor [auto ord: Ord a] (x: a): Ord a := ord`: the instance
  found for `x`'s type. It is a `def`, not a theorem, and is correct.

I checked by hand that `%unpack`'s and `%pack`'s de Bruijn arithmetic is
right for n = 1 (`p => C p`, with no `case`) and n = 2. Larger n are covered
by the probes, since the kernel would refuse a wrong index.

### 3. Coverage: tests are thin on new shapes, but probes pass (low)

The lane added one test, `derived_instances_of_wide_constructors_stay_cheap`,
which guards step counts. Correctness rests on the existing
`examples/accept/derive-*`, `eqeq-*`, `mutual-data-derived`,
`nested-data-*` and `readings-derived-eq` files and on std itself.

I probed each of the following on both binaries. All agree.

| Shape | Probe | Result |
|---|---|---|
| Type parameters, constructors with 0, 1 and 3 fields | `Mixed a b = Nothing \| Single x \| Many x y z` | `==`, `<` and `.read` both ways pass |
| Single constructor with one field | `One = MkOne (n: Nat)` | pass |
| Value parameter | `Valued (k: Nat)` | pass |
| Data and proof fields together (old `andThen` path) | `Dial (highest)` record | `==` and `<` pass |
| Only a proof field (no tuple) | `OnlyProof n = Pf (ok: n = 3)` | pass |
| Nested types (`List`, `Option` of a pair) | `Packet` | pass |
| Mutual types | `Expr` / `Body` | pass |
| A parameter inside `List` | `Wrap a = W (xs: List a) (n: Nat)` | pass |
| Indexed types | `V: Nat -> Type`, `Fixed: Nat -> Type` | refused as on `main` ("has indices") |
| Function field | `MkFn (f: Nat -> Nat) (n: Nat)` | refused as on `main` |
| Field depending on an earlier one | `MkDep (n: Nat) (xs: Fin n)` | refused as on `main` |
| Type in `Type 1` | `Big: Type 1` | "deriving it failed: universe mismatch", as on `main` |

Gaps worth a test:

- **(a) Wide constructors.** No example has a constructor wider than the
  cost test's 16 fields, and that test checks steps, not that `==` and `<`
  give the right answers. A 32-field example would guard the deep nesting.
- **(b) No universe-polymorphic `Pair`.** `Std.Pair` takes `(a: Type)`, so
  the tuple path needs every field in `Type`. That holds today only because
  `DecEq` itself is restricted to `Type`; the `Big` probe shows that a type
  in `Type 1` gets no `==` on `main` either. If `DecEq` is ever generalised
  over universes, `derive_tuple_in` will build an ill-typed `Pair` for a
  large field. The kernel would refuse it, and the user would get only the
  soft "deriving it failed" note. One line in `derive_tuple_in`'s doc saying
  so would help.
- **(c) A constructor with an implicit field.** I didn't probe one
  (brace-declared constructors with implicit fields). `derive_tuple_in`
  ignores icity, which should be fine, since kernel constructors take every
  field.

### 4. Maintainability: clearer laws, one more path to keep in step (low)

The `T.%sameIff` shape is clearer than the old pair of `%sameSound` /
`%sameComplete` bodies. Each constructor's decision is now stated once, and
the module docs are updated to match.

The derivers do get murkier in two ways:

- **Two paths in each deriver.** Both `derive.rs` and `derive_ord.rs` now
  have a tupled path, used for constructors whose fields are all data, and
  the old `andThen` / `thenEqual` + `J` path, used for constructors with
  proof fields. The old path is the one that was cubic, and it is now
  exercised only by constructors with proof fields, so it will rot quietly.
  Extending the tuple to the data fields of a constructor with proof fields
  would leave one path. `pack` would give the data fields; the proof fields
  would come from `DecEq.uniqueEq` / proof irrelevance, as the second step
  already does. A follow-up should look at this.
- **The choice of path is found by name.** `derive.rs` and `derive_ord.rs`
  each pick the path with `has_member(owner, "{prefix}{C}%unpack")`, which
  couples the three places through a string. It's fine as it stands; a
  shared helper (`fn tupled(&self, member, ctor) -> bool`) would keep them
  from drifting.

**Kernel terms as an exception to "derivers generate source": reasonable.**
`%unpack` and `%pack` are not a new kind of exception. They join six
kernel-built helpers that already exist (`%tag`, the field projections,
`%view`, `%eta`, `%etaAt`), and like those they are small, non-recursive
`case` trees, checked by the kernel. Writing them as source would need
nested `MkPair` patterns that the elaborator's match compiler would turn
into much the same trees, at greater cost. The index arithmetic in
`derive_tuple_in` is dense, but its comments say which context each part is
built in.

`Std.Ord.instanceFor` is now a public name in std. It is documented, but it
exists only for the deriver. A `%`-free public helper is harmless; it could
be marked as internal if std gains such a convention.

### 5. Deeper nesting and remaining cubic cost (medium: follow-up)

There is no stack problem at the sizes probed. Times are wall clock on the
branch's release binary under `nice -n 19`, about 0.4 s of which is
start-up:

| Type | Branch | Main |
|---|---|---|
| record of 16 `Nat`s | 0.50 s | |
| record of 32 | 1.37 s | |
| record of 48 | 4.35 s | |
| record of 64 (`==` and `<` used) | 9.1–14.3 s, 320 MB | over 60 s (stopped by `timeout 60`) |
| record of 128 | 99.5 s, passes | not run |
| 40 constructors of 3 fields | 1.22 s | 2.07 s |

There was no stack overflow at 128 fields or 40 constructors. The CLI's
default stack copes with the deeper pending frames.

The cost from 32 to 64 to 128 fields grows about ×8 and then ×11 at each
doubling, so the proofs are still roughly cubic for wide records. They are
just much cheaper than before, and the cost test's 8 and 16 fields sit in
a range where this doesn't show.

A likely cause, which needs profiling before any change (memory: profile
before optimising): the `Pair.decMk` chain in `eq_source` passes the
explicit tuples `tuple(&a, i + 1)` and `tuple(b, i + 1)` at each of the n
levels. Each tuple has n − i elements, and each `MkPair` in it has
implicit type arguments of size up to n − i. Elaborating them all is
Σ (n − i)² = O(n³). If that is the cause, it can be fixed by leaving the
tuples to unification (`_`), or by binding each suffix once.

Records of 64 fields are rare, but 9 s for one declaration is a cliff a
user would notice.

## Follow-ups to file

1. **Profile the 64-field record** (Sonnet, about 30 min). Find what is
   still cubic in derived `==` and `<` for wide constructors, and fix that
   hotspot only. The suspect is the explicit suffix tuples given to
   `Pair.decMk` and `Ordering.thenPairEqual`. Extend
   `derived_instances_of_wide_constructors_stay_cheap` to 32 fields with a
   ratio bound. Finding 5.
2. **One path for constructors with proof fields** (Opus design, then
   Sonnet). Use the tuple path for the data fields of a constructor that
   also has proof fields, so that the old `andThen` / `J` path and
   `Ordering.thenEqual` can go. Finding 4.
3. **A wide-constructor correctness example** (DeepSeek, small). Add an
   `examples/accept/derive-wide.sw` with a 32-field record and a
   constructor with one field, checking `==`, `!=`, `<` and the `.read`
   readings. Finding 3a.
4. **Small cleanups** (DeepSeek, small). Share one `tupled` helper between
   `derive.rs` and `derive_ord.rs`. Note in `derive_tuple_in`'s doc that
   `Std.Pair` is monomorphic in `Type`, so the path relies on `DecEq` being
   restricted to `Type`. Findings 3b and 4.
