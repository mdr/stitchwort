-- expect-error: E-TERMINATION
-- A false `<` at a proof position (termination.rs's header, "Two orders";
-- docs/reviews/SW-3376-wrapper-rule-soundness.md F2, p10). `x`'s type pins
-- `p`, so the checker takes the rebuilt `Mk (More (More p)) x` for the
-- matched `Mk p x` (`PBox`'s parameter is a proof, which comparison skips),
-- and the inner match's `w` counts as a part of the 1st argument, though
-- it's bigger than `p`. `viaAlias` loops (it gets `Mk` every time); size
-- change still refuses it, because the 1st argument only stays the same,
-- but the error's "the 2nd argument is smaller" is the false arc. Accepted
-- programs can't use such arcs to loop because of the positivity rules
-- that soundness/termination-relies-on-positivity-*.sw pin.
type Big: Prop = | Stop | More (b: Big)
type PBox (p: Big): Type = | MkPBox
type T: Type = | Mk (p: Big) (x: PBox p) | In (t: T)

theorem viaAlias: T → Big → Big
  | Mk p x, b =>
    (match Mk (More (More p)) x with
      | Mk w y => viaAlias (Mk w y) w
      | In t => Stop)
  | In t, b => viaAlias t b
