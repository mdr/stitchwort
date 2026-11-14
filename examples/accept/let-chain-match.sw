-- Forty `let`s, each using the last twice, then a `match`: the body is
-- small, but with its `let`s substituted, as an equation states its right
-- side, it would be a tree of about 2^40 nodes. The equation generator
-- counts that size before building it and turns the arm down; building it
-- ran out of memory from about 20 `let`s, and at 40 gave up with a
-- resource error (SW-2512).
def chain (f: Nat → Nat → Nat) (x: Nat) (b: Bool): Nat :=
  let t1 := f x x
  let t2 := f t1 t1
  let t3 := f t2 t2
  let t4 := f t3 t3
  let t5 := f t4 t4
  let t6 := f t5 t5
  let t7 := f t6 t6
  let t8 := f t7 t7
  let t9 := f t8 t8
  let t10 := f t9 t9
  let t11 := f t10 t10
  let t12 := f t11 t11
  let t13 := f t12 t12
  let t14 := f t13 t13
  let t15 := f t14 t14
  let t16 := f t15 t15
  let t17 := f t16 t16
  let t18 := f t17 t17
  let t19 := f t18 t18
  let t20 := f t19 t19
  let t21 := f t20 t20
  let t22 := f t21 t21
  let t23 := f t22 t22
  let t24 := f t23 t23
  let t25 := f t24 t24
  let t26 := f t25 t25
  let t27 := f t26 t26
  let t28 := f t27 t27
  let t29 := f t28 t28
  let t30 := f t29 t29
  let t31 := f t30 t30
  let t32 := f t31 t31
  let t33 := f t32 t32
  let t34 := f t33 t33
  let t35 := f t34 t34
  let t36 := f t35 t35
  let t37 := f t36 t36
  let t38 := f t37 t37
  let t39 := f t38 t38
  let t40 := f t39 t39
  match b with
    | True => t40
    | False => 0

theorem chainFalse ∀ (f: Nat → Nat → Nat) (x: Nat): chain f x False = 0 := rfl
