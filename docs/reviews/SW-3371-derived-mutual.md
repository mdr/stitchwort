# SW-3371 (derived equality stage 3): review of derived `==`, `<` and `${…}` for groups and any earlier container

**Reviewed:** branch `lane/SW-3371` at `23765100a` (`git diff main...lane/SW-3371`):
`crates/elab/src/derive.rs`, `derive_ord.rs`, `derive_show.rs`, `derive_ext.rs`, `lib.rs`, the
two new examples, the changed reject example, the hash snapshots, `docs/syntax.md`, the guide,
`docs/proposals/derived-equality.md` (§5.3, §5.4, "As built (stage 3)") and the toy formatter's
change. Opus, 15 November 2026. **[run]** means probed with the lane's release binary on scratch
files (`test` / `check`, under a second each); **[run, main]** means also run with the main
checkout's binary; **[argued]** means reasoned from the source. No suites, no builds. Probe
files: `/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3371rev/`
(`p1.sw` to `p16.sw`, `proj/`, `js/`).

## Verdict

**Merge.** Nothing here can make the kernel accept something false: every derived instance is
an ordinary definition whose type (`Std.DecEq (T …)`, `Std.Ord.fromCompare …`, the readings'
`↔`) fixes what its laws say, and the kernel checks it. Termination is unchanged, and the
generated recursion doesn't lean on SW-3376's wrapper rule. Single-type output is unchanged (the
hash snapshots only gain lines). Run-time results are right on the bytecode runner, native and
JS. The findings below are one medium usability gap (mostly pre-existing), and lows and nits for
follow-up tickets; none blocks the merge.

| # | Finding | Severity |
|---|---|---|
| F1 | A field default of a non-last group record is checked before the group's instances exist: a misleading `E-INSTANCE-NONE`, and the error makes the whole group unusable. A pre-existing `E-INTERNAL` comes from the same ordering | Medium (follow-up) |
| F2 | A container with a proof field refuses `==` and `<` through it, although the container has its own derived `==`; the note says its fields "can't compare" | Low |
| F3 | Its own `DecEq` on one type of a group stops `Ord` for the whole group, where deferring only that type's instance would be enough | Low (documented choice) |
| F4 | Duplicated scaffolding, and an unreachable refusal | Nit |
| F5 | Note wording in groups | Nit |

## What was checked, and how it came out

**Containers (`members`, `derive.rs:365`).** A container is any `Value::Data` that isn't a group
type, has no indices and isn't a proposition. Quotients aren't `Value::Data`, so they're refused
as "another type". For `Ord` and `Show` a container other than `List`, `Option` and `Pair` must
have `C.%instOrd` / `C.%instShow` (`has_member`). Source can't write a `%` name, so that member
exists only if the deriver made it. The deriver skips any type whose module declares its own
instance, so "derived exists" means "the type's instance is the derived one". I checked
that the member's order and display agree with the container's own derived instance. The
generator is the same function: constructors in order, then fields left to right, proof fields
left out, record and braced forms chosen from `matched`'s own `record()` and `braced`. Field
type `a` is compared or shown through the group's function, which the instance for `a` is.

- Through an earlier group's type (`Rose X`, which pulls in `Roses X`), a program record
  (`Spaced X`) and a sum: for every pair of six sample roses, `compare (Branch r) (Branch s) ==
  compare r s`, `(Branch r == Branch s) == (r == s)`, and `"${Branch r}" == "Branch (${r})"`
  **[run]** (`p3.sw`). `List.sort` of the wrapped values gives the order the roses' own instance
  gives.
- Std types outside the core: `NonEmptyList` gets only `==`, as documented. `Result`'s `Ord` and
  `Show` aren't derived, so through `Result` only `==` is, with the note naming it **[run]**
  (`p2.sw`).
- A container in another namespace of a project (`Lib.Spaced`, `Lib.Rose` used from `Day`):
  `==`, `<` and `${…}` work **[run]** (`proj/`). `member_shape` writes such a type's
  constructors by its full name, which resolves.
- `Vec` (indices): refused, with the note naming it (the reject snapshot). An indexed type in a
  group (`B: Nat → Type` with `A`): refused cleanly, "`B` has indices" **[run]** (`p1.sw`). A
  group of propositions: `field_plan_for` refuses it, and checking doesn't crash **[run]**
  (`p15.sw`). A group that mixes `Type` and `Prop` is `E-MUTUAL-PARAMETERS` before deriving
  starts.
- A container whose fields would grow its arguments without end (`Nest a` with a field `Nest
  (List a)`), which would make the `while next < members.len()` loop run for ever: the kernel
  refuses it first (`E-POSITIVITY`, "used with different parameters") **[run]** (`p5.sw`). Every
  new member's arguments are a field type of an earlier type instantiated at finite arguments, and
  types can't recurse non-uniformly, so the member list is finite **[argued]**.

**`declares_instance_for` (`derive_show.rs:592`).** For a group type it finds the module item
by `data_key(d)` in `item_keys`. `data_key` (path for `Std.*`, else name) is what `register`
stores through `declaration_key`, so the keys match. A single type keeps the old path through
the current item. `lib.rs:2358` now sets `unit.module.item` to each group type's own item during
its `after_data`, so `declares_ext` and the derivers ask about the right item. Before, every type
of a group was checked under the first type's item. An own `DecEq` on one type (`Bd`, even as a
`?`) leaves `E`'s derived `==` working through the derived `Bd.%same` **[run]** (`p6.sw`). That's
right for `==`, since any two decisions of `x = y` give the same `Bool`.

**Groups.** Parameterised groups with two type parameters, `Option` of a pair of a group type
and a `List` of another: `==`, `<`, `${…}` and `DecEq.sound` all work **[run]** (`p11.sw`).
Groups must share parameter names (`E-MUTUAL-PARAMETERS`), so `ord_params` and `with_params`
taking names from the first root is safe. Records in a group get `R.ext`, with the same statement
as a single record's **[run]** (`p12.sw`). Mixed records and sums: the example's `Expr`, `Item`,
`Statement`, `Body`. The members are discovered in the same order whether `instance` is `None`
or `Some`; the only difference is an earlier refusal. So `T.%m1%type` means one thing for all
three derivers, and "unless declared already" in `derive_member_helpers` is safe.

**Statements.** Nothing new is stated by hand: the decision, the readings and the `Ord` laws are
built by the stage 2 code for each member, and the instance types pin them. `T.%sameReads` and
`T.%sameReadsFalse` are still filed for a type that keeps its own `DecEq`. They're true theorems
about the derived `%same`, so that's harmless.

**Termination.** The generated tests and proofs call a member's function only on a field matched
out of the first argument (`%fields r s` reads `s` by projection; `%flip` and `%trans` recurse on
`r`'s fields after `etaAt`). No recursive call takes a constructor application, so rule 3
(SW-3376, the one-field wrapper) never fires, and F2 of that review (false `<` at proof
positions through `alias`) isn't relied on either **[argued]**. The termination checker is
untouched.

**Hash stability.** The six `hash_stability` snapshots only gain lines (`git diff` shows no
removed hash). `derived-std-instances` and the prelude snapshot are unchanged, so the hashes of
single types and of std are the same. `member_shape` still writes `Std.`-path constructor
prefixes for `List`, `Option` and `Pair`, and `Src::this` builds the same `auto` named arguments
the removed inline code did.

**Run time.** One group (Tree/Forest) on the bytecode runner and native: identical output
(`run`, `build`, `build --native`, the same md5). Extracted to JS, `sameTree`, `lessTree` and
`showTree` give `true false true false Node 5 (FCons (Node 5 FNil) FNil)` **[run]** (`js/`).

**Performance.** `check --no-cache Toy.Syntax`: 3.3 s wall at load about 6 (the lane measured
2.43 s of elaboration at load 5; same order). `examples/accept/mutual-data-derived.sw` (21 tests):
2.4 s. An eight-type group with four constructors each and 16 containers: 0.7 s **[run]**
(`p16.sw`). The size stays linear, as the plan says.

**Examples.** `accept/mutual-data-derived.sw` 21/21, `accept/nested-data-derived.sw` 34/34,
`accept/mutual-data.sw` 6/6, and `reject/derived-through-own-instance.sw` gives the snapshot's
three notes **[run]**.

## Findings

### F1 (medium, follow-up): field defaults of a non-last group record run before the group is derived

`lib.rs:2358` runs `after_data` type by type, and `after_data` ends with `self.field_defaults(decl,
d)` (`lib.rs:2696`). The group's instances are derived inside the last type's `after_data`. So a
default on an earlier record that uses `==`, `<` or `${…}` on a group type is checked while no
instance exists:

```
type A = { kids: List B, f: Bool := ([] : List B) == [] }
type B = { a: Option A }
```

gives `E-INSTANCE-NONE: no DecEq instance for B` with "an instance of `DecEq` for `B` can be
declared in `Main`", and then `B needs A`: the whole group is unusable **[run]** (`p9.sw`). Put the
same default on the last type and it works (`p8.sw`). The same ordering causes an existing bug, on
`main` too: a default on an earlier type that uses a later type's constructor is `E-INTERNAL:
`Lit` is used before it's checked` **[run, main]** (`p7.sw`, `type Item = { value: Ex, flag: Bool
:= Lit 1 == Lit 1 }` before `type Ex = | Lit …`). Not a regression: `main` derives nothing for
groups, so the `==` case never worked.

**Fix:** split `after_data` so the group loop runs every type's registrations and derivations
first, then every type's `field_defaults`. That fixes both cases. Small; file it as a ticket.

### F2 (low): a container's proof field stops `==` and `<` through it

In `field_plan_for`'s container loop (`derive.rs:703`), any erased field, a proof included,
refuses with "`{what}` has `T` inside `C`, whose fields `==` can't compare". For roots, an
equation in a type with `DecEq` is `Field::Proof` and left out, and `Show`'s container loop does
the same (`derive_show.rs`, "A container's proof field is left out"). So with `type Checked a = {
item: a, n: Nat, ok: n = n }`, `Checked Nat` has `==`, and `T` nested in `Checked T` gets
`${…}`, but not `==` or `<` **[run]** (`p14.sw`). The note is wrong too: `Checked`'s fields can be
compared.

**Fix:** classify a container's proof field as a root's is: an equation whose carrier has
`DecEq`, doesn't mention the group and doesn't depend on other fields. The member's `same` and
`compare` already skip `Field::Proof`. Until then, make the note say a proof field inside a
container isn't supported yet.

### F3 (low, documented choice): its own `DecEq` on one type stops the group's `Ord`

`derive_ord.rs:108` refuses `Ord` for every type of a group when one has its module's own
`DecEq`. Only that type's `T.%instOrd` needs the hand-written `DecEq` (its `eq`). The others'
instances, and all the `%compare` functions and laws, don't. A single type already defers its
instance until the own `DecEq` is checked (`ord_after_dec_eq`). The group could defer just that
type's instance the same way. syntax.md documents the current rule, so this can wait for someone
to need it.

### F4 (nits): code

- The `own` / `refuse` scaffolding is written three times (`derive.rs:283`, `derive_ord.rs:87`,
  `derive_show.rs:86`). A helper returning `(group, own)` and a `refuse_for(table, …)` would make
  the three derivers read alike.
- `mentions_group` exists (`derive.rs:261`), but `show_plan`, the proof-carrier check in
  `field_plan_for` and the `inner` lookups repeat the same `subterms().any(...)` scan inline.
- `members`' refusal of a group type "with other arguments" (`derive.rs:444`) can't be reached
  today: the kernel refuses `List (T Nat)` in `T a` first (`E-POSITIVITY`, `p13.sw`). Keep it as a
  guard, with a comment saying so.

### F5 (nits): notes

- In a group the note names the constructor, not its type: "`==` isn't derived for `Rule`: the
  field `holds` of `When` is a function", where `When` is `Guard`'s. "of `When` (in `Guard`)"
  would help a reader looking at `Rule`.
- `e < f` on a type without `Ord` is `E-TYPE-MISMATCH` with "there's no `Ord` instance for `E`
  here", without the derivation's reason that `Ord.compare` shows (`p6.sw`). This is probably the
  same for single types (not checked on `main`). Worth a small ticket to attach the `no_ord` note
  there too.

## Tickets to file

1. F1: check a group's field defaults after the whole group is derived (also fixes the
   `E-INTERNAL` for a later type's constructor in a default). Sonnet, about 30 min.
2. F2: proof fields in containers for derived `==` and `<`, as for roots. Sonnet, about 45 min.
3. F5b: the `no_ord` note on `<`'s `E-TYPE-MISMATCH`. DeepSeek, small.
4. F3 and F4 can go with any later derive work.
