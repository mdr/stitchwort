# SW-4734: the stated theorem, notes for the Fable review

Parallel checking, stage 2 step 1 (docs/proposals/parallel-checking.md §10.6,
D3732). Built by Opus. This lane makes nothing stated in a real run: the
only callers of the new constructor are tests. Step 2 (SW-4735) adds the
cache's caller.

## Where a stated theorem can be made

One function, `check::admit_trusted_stated(g, name, path, ty, span)`
(`crates/core/src/check.rs`, beside `admit_trusted_def`, on the cache's trust
boundary). Callers in the tree after this lane:

- `crates/core/tests/it/stated.rs` (kernel tests);
- `crates/driver/src/axioms.rs`, the fail-closed unit test.

No `leave_stated`, and nothing makes one from an unchecked proof (D3732:
stage 3's use isn't approved).

What it checks: `case` only in a case tree; the type refers only to final
declarations (`admissible`); the type is a proposition by the kernel's own
mark (`def_mark`, worked out from `ty` there, before anything is pushed),
else `E-MALFORMED` and nothing is added. It then pushes a theorem with
`stated`, `Final`, `recursive = false`, no body, no group, no label, arity 0
(`push_def`'s defaults). `push_def` was split so the mark is worked out
before the push (`push_marked_def`); the checked path is unchanged.

## What refuses one, and what treats it as proved

| Site | Behaviour |
|---|---|
| `define_group`, `retype_def` | refuse: it isn't pending (tested) |
| `set_run_body`, `admit_trusted_run_body` (`run_body_shape`) | refuse, `E-MALFORMED` (tested) |
| `add_validator` | refuses, `E-MALFORMED` (not tested: needs a `Decidable`-shaped data type) |
| `native::register_shaped`, `float::register_def` | refuse, as for an assumption (not tested) |
| `registry::bind_def`, `nat_add`'s `Nat.addZero`/`addSucc` fit check | accept it: they ask for a final theorem, which it is. Only the prelude reaches them, and the prelude always loads with proofs |
| an `unfolding` list | refused, as for every theorem (tested through `define_def`) |
| `hash::has_interface` | true (`Def::defined()`), so users hash by the interface hash, the same as against the proved theorem (tested: three variants, lambdas, a lemma, stated, give identical interface, proofless and user hashes) |
| `hash::def_hash` (content) | `None`: the full hash is the recorded one, which the replay puts in the cache (tested) |
| `hash::proofless_hash` | `proof-def`, theorem, type, as a proved theorem's (`Hasher::declaration` now takes the proof path before reading a body) |
| `assumption::relied_on`, `mentions` | a leaf; doc names invariant W as the reason |
| `driver::axioms` walk, `audit`'s `witness_of` | fail closed: `axioms::walked_body` panics with "internal error: … is a stated theorem …" (tested for `axioms`) |
| the cache's encoder (`cache/mod.rs`, "isn't admitted with a body") | refuses one among the namespace's own declarations: it writes bodies. Kept as a body test on purpose, with a comment |
| `crates/rt` (`lower.rs`), `crates/js` (`lib.rs`, `run.rs`) | skip every result-erased definition (every theorem) before reading a body, and refuse a bodiless one they would run (`E-RUNTIME` / `E-EXPORT`). They see none in this step: only the check path will make them, and `run`/`build`/`test` load proofs |
| `cache/dump.rs` (F2) | a theorem's arity prints as `-`; a new `stated` field is printed |

## Erasure (F1)

`value::erases_proof`: while erasing, a call of any definition with
`Def::proof` is erased at any number of arguments, body or not. Used first
in `quick`, `eval_step` (`Term::Def`) and `unfold_now`. Before, a proof call
was erased only at `spine.len() == arity` with a body (or an assumption), so
a stated theorem (no body, arity 0) applied to arguments stayed a neutral.
`erases_result` now accepts `defined()` as well. Tested: a stated and a
proved `refl`, unapplied and applied, both erased while running.

This changes when a *proved* theorem's partial application is erased while
running (now at once, before: at full arity). Program results can't differ
(an erased value applied stays erased), but step counts of runs that pass
partially applied theorems around could; the erasure and natives tests
were run for that.

## The seven elaborator tests

All seven moved to `Def::defined()` (reading.rs `@[reading]` scan,
auto.rs hint scan, opaque.rs, interfaces.rs ×2, module.rs `auto_eligible`,
rewrite/repeatedly.rs). The brief also named `audit.rs:467` and
`cache/mod.rs:2483`: both read the body itself, so neither moved to
`defined()`; audit's fails closed and the encoder refuses (above).

## What I couldn't verify

- No real session holds a stated theorem yet, so the elaborator's other
  40-odd body readers (SW-4732's audit, not on main when I finished) are
  untested against one. Step 2's byte-compare is the test.
- `add_validator` and the native registrations' refusals are read, not
  tested.
- The group rule (a theorem in a group with a computing definition is
  never stated) is the writer's rule; there is no writer yet, so it is
  documented (docs/core.md) and left to step 2. The kernel doesn't enforce
  it: a stated theorem has no group by construction.
