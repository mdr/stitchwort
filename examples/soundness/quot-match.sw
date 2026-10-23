-- expect-error: E-NOT-A-CONSTRUCTOR
-- R2 (docs/proposals/map-equality.md §7.5, §7.6): a quotient can't be
-- matched on. `Quot.mk` isn't a constructor; a match that gave back `b`
-- would tell apart `Quot.mk False` and `Quot.mk True`, which are equal.
-- The kernel refuses a `case` on a quotient too (E-MALFORMED,
-- crates/core/tests/quot.rs). Pairs with `constFalse` in
-- accept/quot-forms.sw, which uses `Quot.lift`.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def rep (q: Q): Bool :=
  match q with
    | Quot.mk b => b
