# SW-4665: sealed theorems, stage 1, notes for the kernel review

Stage 1 of docs/proposals/full-proof-irrelevance.md §9 (D3721, D3722): every
`theorem` is sealed, with no escape hatch. These notes give the kernel part's
reasoning for the Fable review; the lane's report has the rest.

## What the kernel does now

1. **Every theorem is opaque.** `push_def` sets `Def::opaque` to `theorem`, so
   `declare_def` and `admit_trusted_def` (the check cache's replay) both
   submit a theorem opaque. `assume` clears it again: an assumption has no
   body, and docs/core.md says it isn't opaque. The flag is the existing one
   (`mark_opaque`, docs/core.md "Opaque definitions"), so the existing
   machinery does the rest: `value::hidden` hides the body while checking any
   declaration whose transparency set lacks it, and running ignores it.
2. **No transparency set holds a theorem.** `transparency` refuses a theorem
   in an `unfolding` list (`E-UNFOLDING-THEOREM`, checked before
   `E-NOT-OPAQUE`), and the closure over an unfolded definition's opaque
   group-mates leaves out theorems. The closure's other source, an unfolded
   definition's own set, is closed and theorem-free by induction (every set
   is built here). So `hidden(g, t)` holds for every theorem `t` whenever a
   declaration other than `t`'s own group is checked, outside a running
   program.
3. **Hashes.** `opacity` skips a theorem with an empty list: the flag is
   implied by the `theorem` tag, so it carries no information. A theorem
   with a list hashes as before (tag and list). Consequence: no hash moves
   because of the flag itself. Hashes did move (the prelude snapshot: 1,407
   of its lines) because elaborated proof terms changed: the elaborator no
   longer unfolds a theorem's call, so read-backs keep the call where they
   used to write out its unfolding. Every such change is inside a proof (a
   theorem call's type is a proposition), and proofs are erased when a
   program runs, so no computation changed; that is the argument for the
   three native pins that moved (below).
4. **Check cache.** `cache::FORMAT` 38 to 39: an entry written when theorems
   were transparent could replay a declaration that unfolded one. The
   compiler fingerprint (which covers `crates/core`) already makes those
   misses; the bump makes it explicit.

## Why it's sound

Sealing only *removes* equalities: a theorem's call that used to unfold now
stays neutral, compared with another call of it by its arguments (shortcut
mode, as any hidden call). Hiding a body is the opaque-definition mechanism
already reviewed (SW-3948 and its predecessors); a theorem is one more opaque
definition with an empty list. The extra refusal in `transparency` and the
filter in the closure only shrink transparency sets. Neither can make a
term accepted that wasn't.

Rule 3 of "Opaque definitions" (a definition with a list must be opaque)
keeps holding: a theorem with a list is opaque, and the elaborator's lifted
helpers of such a theorem are marked opaque as before. A *local* theorem
lifted from a body with a list is opaque (as a theorem) and is no longer
added to its owner's list (`opaque_helper_admitted`), which `transparency`
would now refuse.

What still comes from a theorem's body: its inert proof parameters (the same
residue every opaque definition has, docs/core.md). Removing that is rule I
(stage 5), not this stage.

## Native pins

`Float.neg`, `Float.abs` and `Float.sub` moved (`crates/core/src/pins.rs`).
Their own terms are unchanged (`STITCHWORT_DUMP_KERNEL` on each, and on
`Float.negFrom`, `Float.make`, `Float.clearValid`, `Float.clearSignBits`, is
identical before and after); what moved is the hash of theorems they reach
through proof arguments (`Float.flipValid`, `Float.clearValid` and the
`arithmetic` proofs below them), for the reason in 3. The natives compute
on `bits` only, so they are unchanged. No text native moved
(`crates/rt/src/natives.rs`).

## Elaborator changes that read a proof's body

- `.eqK` / `f.induct` generation (`equations.rs` `uniqueness`): a `then`
  branch whose value depends on its guard's proof, for a condition that isn't
  a `Bool` or `DecEq` equation, used to get no equation (D2180). It now gets
  one, proved along `Prop.irrel` (std's core, SW-4663), which uses the
  proof's statement alone. This is what `and-guard-proof-in-induct.sw`
  needed: its `decreasing` proof is a call of the sealed `stepDown`, which
  conversion can no longer see through. It also accepts more:
  `equation-uses-relevant-proof.sw` moved from reject to accept.
- `rewrite`'s syntactic search (`matching::same_shifted`, SW-4661): not
  changed. The one proof that met it (`PrefixSums.atOf`) is edited instead.
