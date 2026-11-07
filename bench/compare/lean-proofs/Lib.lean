/-! The few list lemmas Stitchwort's standard library already has, so the
day files prove what the Stitchwort days prove and no more. -/

def List.chain (ok : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | x :: next :: rest => ok x next && List.chain ok (next :: rest)

theorem List.chain_cong (xs : List α) (h1 h2 : α → α → Bool)
    (eh : ∀ x y, h1 x y = h2 x y) : xs.chain h1 = xs.chain h2 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest => simp only [List.chain, eh x next, ih]

theorem List.chain_and (xs : List α) (h1 h2 : α → α → Bool) :
    xs.chain (fun x y => h1 x y && h2 x y) = (xs.chain h1 && xs.chain h2) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simp only [List.chain, ih]
      cases h1 x next <;> cases h2 x next <;> cases List.chain h1 (next :: rest) <;>
        cases List.chain h2 (next :: rest) <;> rfl

theorem List.chain_tail (xs : List α) (h : α → α → Bool) (c : xs.chain h = true) :
    xs.tail.chain h = true := by
  match xs, c with
  | [], _ => rfl
  | [_], _ => rfl
  | x :: next :: rest, c => exact (Bool.and_eq_true_iff.mp c).2

theorem List.chain_init_cons (x : α) (rest : List α) (h : α → α → Bool)
    (c : (x :: rest).chain h = true) : (x :: rest).dropLast.chain h = true := by
  induction rest generalizing x with
  | nil => rfl
  | cons next more ih =>
    cases more with
    | nil => rfl
    | cons after more =>
      obtain ⟨first, kept⟩ := Bool.and_eq_true_iff.mp c
      have := ih next kept
      simp only [List.dropLast, List.chain] at this ⊢
      simp [first, this]

theorem List.chain_dropLast (xs : List α) (h : α → α → Bool) (c : xs.chain h = true) :
    xs.dropLast.chain h = true := by
  cases xs with
  | nil => rfl
  | cons x rest => exact List.chain_init_cons x rest h c

theorem List.count_cong_mem (xs : List α) (p q : α → Bool)
    (ep : ∀ x, x ∈ xs → p x = q x) : xs.countP p = xs.countP q := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.countP_cons, ep x (List.mem_cons_self ..),
      ih (fun y hy => ep y (List.mem_cons_of_mem _ hy))]

theorem List.count_le_mem (xs : List α) (p q : α → Bool)
    (h : ∀ x, x ∈ xs → p x = true → q x = true) : xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    simp only [List.countP_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem List.any_or (p q : α → Bool) (xs : List α) :
    xs.any (fun x => p x || q x) = (xs.any p || xs.any q) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.any_cons, ih]
    cases p x <;> cases q x <;> cases rest.any p <;> cases rest.any q <;> rfl
