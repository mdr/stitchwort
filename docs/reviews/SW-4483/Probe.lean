-- 1: part of a conjunction hypothesis
example (A B : Prop) (h : A ∧ B) : A := by solve_by_elim
-- 2: with And.left named
example (A B : Prop) (h : A ∧ B) : A := by solve_by_elim [And.left]
-- 3: implication applied to a fact
example (A B : Prop) (imp : A → B) (a : A) : B := by solve_by_elim
-- 4: conjunction goal, parts from scope
example (A B : Prop) (a : A) (b : B) : A ∧ B := by solve_by_elim
-- 5: implication whose premise is a part of a conjunction
example (A B C : Prop) (imp : A → C) (h : A ∧ B) : C := by solve_by_elim
-- 6: named lemma, premises in scope
theorem lem (n : Nat) (h : n > 3) : n > 1 := by omega
example (n : Nat) (h : n > 3) : n > 1 := by solve_by_elim [lem]
-- 7: local forall
example (P Q : Nat → Prop) (all : ∀ x, P x → Q x) (p : P 5) : Q 5 := by solve_by_elim
-- 8: Bool && fact
example (a b : Bool) (h : (a && b) = true) : a = true := by solve_by_elim
-- 9: show_term records the term
example (A B C : Prop) (imp : A → B → C) (a : A) (b : B) : C ∧ A := by show_term solve_by_elim
-- 10: needs an equation in scope
example (f : Nat → Nat) (a b : Nat) (e : a = b) (h : f b = 0) : f a = 0 := by solve_by_elim
-- 11: same with simp_all / grind
example (f : Nat → Nat) (a b : Nat) (e : a = b) (h : f b = 0) : f a = 0 := by simp_all
example (A B C : Prop) (imp : A → C) (h : A ∧ B) : C := by simp_all
example (A B C : Prop) (imp : A → C) (h : A ∧ B) : C := by grind
example (a b : Bool) (h : (a && b) = true) : a = true := by simp_all
-- 12: exact? on 5
example (A B C : Prop) (imp : A → C) (h : A ∧ B) : C := by exact?
-- 13: three chained implications
example (a b c d : Prop) (f : a → b) (g : b → c) (k : c → d) (x : a) : d := by solve_by_elim
-- 14: a local forall with two premises
example (P Q R : Nat → Prop) (step : ∀ x, P x → Q x → R x) (p : P 3) (q : Q 3) : R 3 := by solve_by_elim
-- 15: an unknown the conclusion doesn't fix
example (P Q R : Nat → Prop) (step : ∀ x y, P x → Q y → R y) (p : P 5) (q : Q 3) : R 3 := by solve_by_elim
-- 16: a part of a conjunction, by simp_all
example (A B : Prop) (h : A ∧ B) : A := by simp_all
-- 17: an existential from an existential
example (p q : Nat → Prop) (h : ∃ n, p n ∧ q n) : ∃ n, q n := by solve_by_elim
example (p q : Nat → Prop) (h : ∃ n, p n ∧ q n) : ∃ n, q n := by grind
