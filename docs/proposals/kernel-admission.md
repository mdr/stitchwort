# Kernel admission for single declarations (as built)

The part of [mutual-recursion.md](mutual-recursion.md) §5 (draft 2) that
today's one-declaration-at-a-time kernel needs. It closes the gap in
`TODO.md` ("The kernel doesn't track whether a declaration is finished"):
called directly, the kernel accepted a cycle split across two definitions
and an empty match on a data type whose constructors hadn't arrived yet.
Groups and forward references are left to the mutual-recursion work, which
extends this (size-change termination and the saturation rule for single
definitions are built: mutual-recursion.md §10.1).

## States

Each definition and data type records a `State` (`crates/core/src/globals.rs`),
replacing the meaning that was carried by `body: Option<…>` and
`ctors_defined: bool`:

- **Pending:** declared (signature, or parameters and universe, checked);
  its body or constructors haven't been admitted.
- **Final:** admitted, together with everything it refers to.
- **Failed:** its admission was refused, or it refers to a failed
  declaration. It never becomes final.

Transitions are one-way: pending → final, pending → failed. Only the
kernel's own functions change a state. A definition has a body exactly when
it's final, so only final definitions unfold (the evaluator still reads
`body`).

The "opaque assumption" state of §5.1 isn't added: nothing creates
assumptions yet, so the rule below describes today's assumption-free
fragment. Adding assumptions means admitting them as dependencies and
propagating them to whatever uses them.

## The rule

> Everything a submission refers to must be final, apart from the
> declaration being admitted, where the table below allows it.

"Refers to" means a `Def`, `Data`, `Ctor` or `Case` anywhere in the
submitted terms. The pending references each part may make:

| Part being checked | Pending references allowed |
|---|---|
| A definition's signature; a data type's parameters | None |
| A definition's body | The members of its group, including itself (opaque while they're checked) |
| A data type's constructor fields | The data type itself, as a type: not its constructors, and no `case` on it |
| An export's validator | None (and the export must be final) |

Because every final declaration was admitted under the same rule, everything
it reaches is final too (by induction over admissions; final declarations
never change), so the walk needn't follow references.

- A reference to a **pending** declaration is refused at once with
  `E-MALFORMED`: no correct elaborator submits one. The declaration being
  admitted becomes failed.
- A reference to a declaration that **doesn't exist** is refused the same
  way. Declaration ids are plain indices that a buggy elaborator could make
  up, so the walk checks each one before anything is checked or added.
- A reference to a **failed** declaration doesn't stop checking, so the
  user still sees the dependent's own errors. If checking succeeds, the
  result is failed anyway and the call returns `E-FAILED-DEPENDENCY`. A
  signature or data parameters that refer to a failed declaration are
  still declared (so the elaborator can keep going); the reference is found
  again when the body or constructors are submitted, so they fail.
- **Re-defining** anything that isn't pending is refused (`E-MALFORMED`).
- Any refusal of a body or constructors, including running out of
  resources, leaves the declaration failed.

## Where it's enforced

In `crates/core/src/check.rs`, by `admissible`:

| Function | Walks | Requires |
|---|---|---|
| `declare_def` | the signature | |
| `define_group` (and `define_def`, a group of one) | each signature again, and each body | every member is pending, and listed once |
| `declare_data` | the parameters | |
| `define_ctors` | the parameters again, and the fields | the data type is pending |
| `add_validator` | the decision | the export and `Decidable` are final |

These are the only ways into the kernel: there are no imported
declarations, and the test cache stores results by hash, never
declarations. The `register_*` functions in `native.rs`, which install the
trusted natives, refuse anything not final, including the `Void` they look
up. Second lines of defence: `check_case` refuses a data type that isn't
final, so a type without its constructors is never treated as empty; the
hasher (`def_hash`, `data_hash`) gives no hash for anything not final, so a
failed or pending declaration has no cache entry; and JavaScript is
generated only from bodies, which only final definitions have.

The elaborator declares and defines each item back to back, so it satisfies
the rule unchanged, with two additions in `elaborate_module`: when a
declaration fails, it calls `check::abandon_pending`, so one left pending
(because its body or constructors never reached the kernel) becomes failed
rather than something later declarations trip over as `E-MALFORMED`; and it
drops `E-FAILED-DEPENDENCY` diagnostics when the module reports some other
error, which already explains them.

## Tests

Raw-kernel tests in `crates/core/tests/admission.rs`, each must-reject one
paired with an accepted neighbour where there is one. From §5.5, those that
apply to single declarations:

1. The split cycle: `f n = g n` with `g` pending is refused, so `f` fails
   and `g n = f n` is then refused as a failed dependency (§5.5 test 1;
   the group neighbour belongs to the mutual-recursion work).
2. The pending data type (§5.5 test 2): `impossible : D -> Void` is
   refused at its signature, which mentions pending `D`. The `case` rule is
   tested separately, by an empty match on pending `D` checked directly.
   Neighbours: an empty match on `Void` (final, with no constructors) is
   accepted; `impossible`, once `D` is final, is `E-NONEXHAUSTIVE`.
3. Using a failed declaration: checked, failed, no hash, and not usable by
   a later definition or data type (§5.5 test 3).
4. Re-defining a final definition, and redefining a failed one (§5.5 tests
   4 and 5).
5. A signature referring to a pending declaration (§5.5 test 6), and data
   parameters referring to one.
6. A constructor field referring to a pending definition or data type, or
   to its own constructor (§5.5 test 7).
7. A proof (a theorem's body) referring to a pending definition.
8. A validator whose decision refers to a pending definition.
9. `Decidable` whose `No` mentions a pending `Void` can't be defined or
   registered as the builtin.
10. Running out of resources while checking a body leaves it failed, with
    no hash (§5.5 test 10).
11. References to declarations that don't exist, and defining one that was
    never declared: refused, and nothing is added.
12. A pending data type has no hash (in `crates/core/tests/hash.rs`).

§5.5 test 9 (incorrect partitions of a group), §5.3's group admission and
the mixed-group rule are built with function groups (mutual-recursion.md
§10.2, tests in `crates/core/tests/groups.rs`). §5.5 test 8 (adding a member
to an existing data group) and §5.4 are built with data groups
(mutual-recursion.md §10.3, tests in `crates/core/tests/data_groups.rs`).
A data type's fields may now mention the members of its group as types:
row 3 of the table above, for a group of one, is the data type itself.
