# SW-4728: eta read a sealed body (notes for the Fable review)

## The finding

`value::next_parameter` (the parameters eta for a partial application
reads off a definition's leading lambdas) read `def.body` directly, not
through `body_seen`, so it saw a theorem's proof (rule F) and a hidden
opaque definition's body. The reference evaluator's `eta` had the same
read. Users: the kernel's `push_eta` (three call sites in `conv_step` and
`recurse`), the unifier's `push_eta`, and `underapplied` (kernel and
unifier), which is reached only after the `sealed` test, so it never saw
a sealed definition.

## Probe: no visible effect found

- Instrumented `next_parameter` to log whenever it read a frozen or
  hidden body, and checked a probe file twice, once with `theorem t: ∀ (n:
  Nat) => P n := n => pAll n` and once with `:= pAll`. The file covered `t`
  against `x => t x`; `t` in a record with a data field (`{ size = 3, all
  = t }` against `all = x => t x` and `all = pAll`); an implicit
  `[f: ∀ (n: Nat) => P n]` solved from `f = g` with `g := t`; `t` against
  a variable; `holder t = holder (x => pAll x)`; a proof `pick b` defined
  by `match`; and a projection of `t` from a record. Both versions checked
  with no difference, and the log never fired: rule I, the `sealed` arm
  and lambda eta answer first every time.
- Argument for why that holds in general: when one side is a sealed call
  `t s` (under-applied), eta pushes `t s v` against `o v`. If `o` is marked
  a proof, rule I answers before eta. If `o` is a lambda, lambda eta runs
  and `next_parameter` isn't consulted. If `o` is an unknown, the unknown's
  arms come first. What's left is `o` neutral and not marked a proof (an
  unknown mark). Then `o v` is a neutral with the same head and spine plus
  `v`, and it can equal `t s v` only by having the same head `t` (the
  sealed arm, by arguments) or by rule I (needs a mark that `o v` doesn't
  have, since marks follow heads). So the result is the same as without
  eta. When `o` is itself an under-applied visible definition, it offers
  the same parameter: same icit, and the mark matches because both come
  from the shared type's binder, which the kernel derived.
- So there was no staleness in the interface-digest cache from this read.
  The only body-dependent bit was whether eta was tried at all (arity =
  the count of leading lambdas, from the proof's shape).

## The fix

- `next_parameter` reads `body_seen(g, id)?`; reference `eta` reads
  `seen(g, *id)?`. A frozen or hidden definition offers no parameters; eta
  is tried from the other side only. While a program runs, or inside the
  transparency set, nothing changes.
- Test: `crates/core/tests/it/opaque.rs`
  `eta_doesnt_read_a_sealed_body` pins it (fails before the fix with
  `Some(Explicit)` for the theorem).
- docs/core.md: the conversion paragraph ("A definition applied to fewer
  arguments …") and the opaque-definitions intro now say eta reads only a
  body that may be seen.

## What to check

1. The argument above that nothing is lost, especially in the unifier,
   where marks can be *unknown*: is there a value `o`, not a lambda, not an
   unknown-headed value and not proof-marked, for which `o v` can still
   compute to, or be postponed into, something equal to `t s v`? (I found
   none. `Value::Call` is forced before the fallback, and blocked calls
   are put aside before `push_eta`.)
2. `first_order` pairs values of possibly different types. The unifier's
   `push_eta` has `can_apply` for that. Does the change of which side
   supplies `(icit, mark)` matter there?
3. Remaining raw `Def::body` and `arity` reads in the elaborator (about 40
   `.body()` calls in `crates/elab`, for example `walk/mod.rs` `case_tree`,
   `matching.rs` `literal`, `equations.rs`, `decreasing.rs`). Not audited
   here. Any of them that can be reached with a theorem *other than the
   one being elaborated* is a rule 6 hole of the same kind, and a possible
   staleness in the digest cache. I suggest it as its own audit ticket.
4. `Def::arity` of a theorem is still derived from its proof's lambdas and
   read in kernel paths behind `body_seen` (eval of arity 0, `case_tree`,
   `unfold_now`). I checked those are all guarded by `frozen`, `hidden` or
   `body_seen` first.
