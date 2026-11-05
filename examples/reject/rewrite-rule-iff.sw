-- expect-error: E-REWRITE-RULE
-- `Iff` is a proof of `p ↔ q`, not of an equation: say how to rewrite with
-- one direction instead.
import Std (Iff)

theorem bad (p: Prop) (q: Prop) (h: p ↔ q): q := rewrite h
