/-
Advent of Code 2025, day 2 part 2, in Lean 4 (core only: no Mathlib, no
Batteries), proved for every input. A prototype for the Stitchwort proof
(aoc/src/day02/), which today covers only ids of at most 10 digits.

  lean Day02General.lean     -- check, and print the example and cross-checks

The theorem is `part2Correct`: `solvePart2 ranges = part2Spec ranges` for every
list of ranges. See README.md for the outline and the porting note.
-/

-- Lean 4.34 marks `if_pos`/`if_neg` deprecated; they still work.
set_option linter.deprecated false

-- ===========================================================================
-- 1. The puzzle's definitions (the specification)
-- ===========================================================================

-- Decimal digits, most significant first; `digits 0 = [0]`.
def digits (x : Nat) : List Nat :=
  if x < 10 then [x] else digits (x / 10) ++ [x % 10]
termination_by x
decreasing_by omega

-- The digits `ds` are some block of k digits written n times.
def writtenAs (ds : List Nat) (k n : Nat) : Bool :=
  (List.replicate n (ds.take k)).flatten == ds

-- The puzzle: an id is invalid when its digits are some block written two or
-- more times. (Mirrors Stitchwort's `repeats`: k in 1..L, n in 2..L+1.)
def repeats (x : Nat) : Bool :=
  let ds := digits x
  (List.range' 1 ds.length).any fun k => (List.range' 2 ds.length).any fun n => writtenAs ds k n

structure Range where
  lo : Nat
  hi : Nat

def Range.ids (r : Range) : List Nat := List.range' r.lo (r.hi + 1 - r.lo)

-- Walk the ids of every range, add up those that repeat.
def part2Spec (ranges : List Range) : Nat :=
  (ranges.map fun r => (r.ids.filter repeats).sum).sum

-- ===========================================================================
-- 2. The program
-- ===========================================================================

-- Integer sums (Stitchwort's `List.sumBy`).
def sumBy {α : Type} (f : α → Int) : List α → Int
  | [] => 0
  | x :: xs => f x + sumBy f xs

-- 1 + 10^k + 10^2k + ... (n terms): a k-digit block b written n times is b * m.
def multiplier (k n : Nat) : Nat := ((List.range n).map fun i => 10 ^ (k * i)).sum

-- The sum of the ids in the range that are a k-digit block written n times:
-- m times an arithmetic series of blocks.
def repeated (r : Range) (k n : Nat) : Nat :=
  let m := multiplier k n
  if m ≠ 0 then
    let lo := max (10 ^ (k - 1)) ((r.lo + m - 1) / m)
    let hi := min (10 ^ k - 1) (r.hi / m)
    if lo ≤ hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
  else 0

-- The weights, computed rather than tabled: `weight K` is chosen so that, for
-- every K ≥ 2, the weights of the divisors of K from 2 on add up to 1.
-- (This is minus the Moebius function.) The first argument is fuel, so the
-- recursion is structural; `weight n` gives it enough.
def wf : Nat → Nat → Int
  | 0, _ => 0
  | f + 1, n => 1 - sumBy (fun d => if n % d = 0 then wf f d else 0) (List.range' 2 (n - 2))

def weight (n : Nat) : Int := wf (n + 1) n

-- One range: every block length k and repeat count n whose ids fit in the
-- digits of `hi`, weighted.
def invalid (r : Range) : Int :=
  let size := (digits r.hi).length
  sumBy (fun k => sumBy (fun n => if k * n ≤ size then weight n * repeated r k n else 0)
    (List.range' 2 (size - 1))) (List.range' 1 size)

def solvePart2 (ranges : List Range) : Nat := (sumBy invalid ranges).toNat

-- ===========================================================================
-- 3. Sums
-- ===========================================================================

theorem sumBy_append {α} (f : α → Int) (l₁ l₂ : List α) :
    sumBy f (l₁ ++ l₂) = sumBy f l₁ + sumBy f l₂ := by
  induction l₁ with
  | nil => simp [sumBy]
  | cons x xs ih => simp [sumBy, ih]; omega

theorem sumBy_congr {α} (f g : α → Int) (l : List α) (h : ∀ x ∈ l, f x = g x) :
    sumBy f l = sumBy g l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumBy]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem sumBy_zero {α} (f : α → Int) (l : List α) (h : ∀ x ∈ l, f x = 0) : sumBy f l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumBy]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]; rfl

theorem sumBy_add {α} (f g : α → Int) (l : List α) :
    sumBy (fun x => f x + g x) l = sumBy f l + sumBy g l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [sumBy, ih]; omega

theorem sumBy_mul {α} (c : Int) (f : α → Int) (l : List α) :
    sumBy (fun x => c * f x) l = c * sumBy f l := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih => simp only [sumBy, ih, Int.mul_add]

theorem sumBy_swap {α β} (f : α → β → Int) (la : List α) (lb : List β) :
    sumBy (fun a => sumBy (fun b => f a b) lb) la = sumBy (fun b => sumBy (fun a => f a b) la) lb := by
  induction la with
  | nil => simp [sumBy]; exact (sumBy_zero _ _ (fun _ _ => rfl)).symm
  | cons a as ih =>
    simp only [sumBy]; rw [ih, ← sumBy_add]

-- A sum over a run of numbers where only `x₀` can count.
theorem sumBy_single (f : Nat → Int) (x₀ : Nat) (h : ∀ x, x ≠ x₀ → f x = 0) :
    ∀ n s, sumBy f (List.range' s n) = if s ≤ x₀ ∧ x₀ < s + n then f x₀ else 0 := by
  intro n
  induction n with
  | zero => intro s; simp [sumBy]; omega
  | succ n ih =>
    intro s
    rw [List.range'_succ]; simp only [sumBy]; rw [ih (s + 1)]
    by_cases hs : s = x₀
    · subst hs
      rw [if_neg (by omega : ¬ (s + 1 ≤ s ∧ s < s + 1 + n)), if_pos (by omega : s ≤ s ∧ s < s + (n + 1))]
      simp
    · rw [h s hs]
      by_cases hin : s + 1 ≤ x₀ ∧ x₀ < s + 1 + n
      · rw [if_pos hin, if_pos (by omega)]; simp
      · rw [if_neg hin, if_neg (by omega)]; simp

-- The spec's Nat sum as an Int sum.
theorem filter_sum_eq (p : Nat → Bool) (l : List Nat) :
    ((l.filter p).sum : Int) = sumBy (fun x => if p x then (x : Int) else 0) l := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih =>
    simp only [List.filter, sumBy]
    cases hp : p x <;> simp [List.sum_cons, ih]

-- ===========================================================================
-- 4. The weights: over the divisors of K from 2 on, they add up to 1
-- ===========================================================================

-- More fuel doesn't change `wf`.
theorem wf_fuel : ∀ f g n, n < f → n < g → wf f n = wf g n := by
  intro f
  induction f with
  | zero => intro g n h; omega
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero => omega
    | succ g =>
      simp only [wf]
      congr 1
      apply sumBy_congr
      intro d hd
      simp [List.mem_range'] at hd
      split
      · exact ih g d (by omega) (by omega)
      · rfl

-- The divisors of K from 2 to K, weighted.
def divisorSum (K : Nat) : Int :=
  sumBy (fun n => if K % n = 0 then weight n else 0) (List.range' 2 (K - 1))

theorem divisorSum_eq (K : Nat) (hK : 2 ≤ K) : divisorSum K = 1 := by
  unfold divisorSum
  have hsplit : List.range' 2 (K - 1) = List.range' 2 (K - 2) ++ [K] := by
    have := List.range'_append (s := 2) (m := K - 2) (n := 1) (step := 1)
    simp only [Nat.one_mul] at this
    rw [show K - 1 = K - 2 + 1 by omega, ← this]
    simp [List.range'_succ, show 2 + (K - 2) = K by omega]
  rw [hsplit, sumBy_append]
  simp only [sumBy, Nat.mod_self, if_true, Int.add_zero]
  have hw : weight K = 1 - sumBy (fun d => if K % d = 0 then wf K d else 0) (List.range' 2 (K - 2)) := rfl
  have : sumBy (fun n => if K % n = 0 then weight n else 0) (List.range' 2 (K - 2))
      = sumBy (fun d => if K % d = 0 then wf K d else 0) (List.range' 2 (K - 2)) := by
    apply sumBy_congr
    intro d hd
    simp [List.mem_range'] at hd
    split
    · exact wf_fuel _ _ _ (by omega) (by omega)
    · rfl
  rw [this, hw]; omega

-- So, for K ≥ 1, the weights of the divisors of K from 2 on add up to
-- 1 if K ≥ 2 and 0 if K = 1.
theorem divisorSum_ind (K : Nat) (hK : 1 ≤ K) : divisorSum K = if 2 ≤ K then 1 else 0 := by
  by_cases h : 2 ≤ K
  · rw [if_pos h, divisorSum_eq K h]
  · rw [if_neg h, show K = 1 by omega]; rfl

-- ===========================================================================
-- 5. Periods: rotations that leave a sequence unchanged
-- ===========================================================================

-- Rotating the first L values of g by p leaves them unchanged.
def Cyc (g : Nat → Nat) (L p : Nat) : Prop := ∀ i, i < L → g ((i + p) % L) = g i

theorem cyc_zero (g : Nat → Nat) (L : Nat) : Cyc g L 0 := by
  intro i hi; simp [Nat.mod_eq_of_lt hi]

theorem cyc_add (g : Nat → Nat) (L p q : Nat) (hp : Cyc g L p) (hq : Cyc g L q) : Cyc g L (p + q) := by
  intro i hi
  have hL : 0 < L := by omega
  have h1 := hq ((i + p) % L) (Nat.mod_lt _ hL)
  rw [Nat.mod_add_mod] at h1
  rw [← Nat.add_assoc, h1, hp i hi]

theorem cyc_sub (g : Nat → Nat) (L p q : Nat) (hp : Cyc g L p) (hq : Cyc g L q) (hle : q ≤ p) :
    Cyc g L (p - q) := by
  intro i hi
  have hL : 0 < L := by omega
  have h1 := hq ((i + (p - q)) % L) (Nat.mod_lt _ hL)
  rw [Nat.mod_add_mod, Nat.add_assoc, Nat.sub_add_cancel hle] at h1
  rw [← h1, hp i hi]

theorem cyc_mul (g : Nat → Nat) (L p : Nat) (hp : Cyc g L p) : ∀ t, Cyc g L (p * t) := by
  intro t
  induction t with
  | zero => simpa using cyc_zero g L
  | succ t ih => rw [Nat.mul_succ]; exact cyc_add g L _ _ ih hp

-- The heart: if p₀ is the smallest positive period, every period is a
-- multiple of it (the remainder of division by p₀ is a smaller period).
theorem cyc_dvd (g : Nat → Nat) (L p₀ p : Nat) (h0 : 0 < p₀) (hp₀ : Cyc g L p₀)
    (hmin : ∀ q, 0 < q → q < p₀ → ¬ Cyc g L q) (hp : Cyc g L p) : p₀ ∣ p := by
  have hsub := cyc_sub g L p (p₀ * (p / p₀)) hp (cyc_mul g L p₀ hp₀ _) (Nat.mul_div_le p p₀)
  have hmod : p - p₀ * (p / p₀) = p % p₀ := by
    have := Nat.mod_add_div p p₀; omega
  rw [hmod] at hsub
  apply Nat.dvd_of_mod_eq_zero
  by_cases hz : p % p₀ = 0
  · exact hz
  · exact absurd hsub (hmin _ (by omega) (Nat.mod_lt _ h0))

-- Some property has a least witness (Stitchwort: a search over 1..L).
theorem exists_min (P : Nat → Prop) : ∀ n, P n → ∃ m, P m ∧ ∀ j, j < m → ¬ P j := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∃ j, j < n ∧ P j
    · obtain ⟨j, hj, pj⟩ := h; exact ih j hj pj
    · exact ⟨n, hn, fun j hj pj => h ⟨j, hj, pj⟩⟩

-- Every sequence of length L ≥ 1 has a smallest positive period p₀; p₀
-- divides L, and the periods are exactly the multiples of p₀.
theorem smallest_period (g : Nat → Nat) (L : Nat) (hL : 0 < L) :
    ∃ p₀, 0 < p₀ ∧ p₀ ∣ L ∧ Cyc g L p₀ ∧ ∀ p, Cyc g L p ↔ p₀ ∣ p := by
  have hLc : Cyc g L L := by
    intro i hi; simp [Nat.mod_eq_of_lt hi]
  obtain ⟨p₀, ⟨hpos, hp₀⟩, hmin⟩ := exists_min (fun p => 0 < p ∧ Cyc g L p) L ⟨hL, hLc⟩
  have hmin' : ∀ q, 0 < q → q < p₀ → ¬ Cyc g L q := fun q hq hlt hc => hmin q hlt ⟨hq, hc⟩
  refine ⟨p₀, hpos, cyc_dvd g L p₀ L hpos hp₀ hmin' hLc, hp₀, fun p => ⟨cyc_dvd g L p₀ p hpos hp₀ hmin', ?_⟩⟩
  intro ⟨t, ht⟩; subst ht; exact cyc_mul g L p₀ hp₀ t

-- ===========================================================================
-- 6. A block written n times is a period
-- ===========================================================================

-- Every value equals the one at its position within the first k.
def Block (g : Nat → Nat) (L k : Nat) : Prop := ∀ i, i < L → g i = g (i % k)

theorem block_iff_cyc (g : Nat → Nat) (L k : Nat) (hk : 0 < k) (hkL : k ∣ L) :
    Block g L k ↔ Cyc g L k := by
  constructor
  · intro hb i hi
    have hL : 0 < L := by omega
    rw [hb _ (Nat.mod_lt _ hL), Nat.mod_mod_of_dvd _ hkL, Nat.add_mod_right, ← hb i hi]
  · intro hc i hi
    have hm := cyc_mul g L k hc (i / k) (i % k) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hk) (Nat.le_of_dvd (by omega) hkL))
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt hi] at hm
    exact hm

theorem getD_append_left' (l₁ l₂ : List Nat) (i : Nat) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l₁ l₂ : List Nat) (i : Nat) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_take' (l : List Nat) (k i : Nat) (h : i < k) : (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

-- Position i of a block written n times.
theorem getD_flatten_replicate (b : List Nat) (k : Nat) (hb : b.length = k) :
    ∀ n i, i < n * k → ((List.replicate n b).flatten).getD i 0 = b.getD (i % k) 0 := by
  intro n
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih =>
    intro i hi
    rw [List.replicate_succ, List.flatten_cons]
    by_cases h : i < k
    · rw [getD_append_left' _ _ _ (by omega), Nat.mod_eq_of_lt h]
    · rw [getD_append_right' _ _ _ (by omega), hb, ih (i - k) (by rw [Nat.succ_mul] at hi; omega)]
      congr 1
      rw [← Nat.mod_eq_sub_mod (by omega)]

theorem length_flatten_replicate (b : List Nat) (n : Nat) :
    ((List.replicate n b).flatten).length = n * b.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]; omega

theorem ext_getD (l₁ l₂ : List Nat) (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

-- With n ≥ 2 copies, the block has L / n digits.
theorem writtenAs_length (ds : List Nat) (k n : Nat) (hL : 0 < ds.length) (hn : 2 ≤ n)
    (h : writtenAs ds k n = true) : k * n = ds.length ∧ 0 < k := by
  unfold writtenAs at h
  have e := congrArg List.length (of_decide_eq_true (by simpa using h) : (List.replicate n (ds.take k)).flatten = ds)
  rw [length_flatten_replicate, List.length_take] at e
  by_cases hk : k ≤ ds.length
  · rw [Nat.min_eq_left hk] at e
    refine ⟨by rw [Nat.mul_comm]; exact e, ?_⟩
    cases k with
    | zero => simp at e; omega
    | succ k => omega
  · rw [Nat.min_eq_right (by omega)] at e
    have : 2 * ds.length ≤ n * ds.length := Nat.mul_le_mul_right _ hn
    omega

-- Digits as a function of the position.
def at_ (ds : List Nat) (i : Nat) : Nat := ds.getD i 0

-- For k * n = L: written n times as its first k digits iff k is a period.
theorem writtenAs_iff (ds : List Nat) (k n : Nat) (hk : 0 < k) (hL : 0 < ds.length) (hkn : k * n = ds.length) :
    writtenAs ds k n = true ↔ Cyc (at_ ds) ds.length k := by
  have hdvd : k ∣ ds.length := ⟨n, hkn.symm⟩
  rw [← block_iff_cyc _ _ _ hk hdvd]
  have hkL : k ≤ ds.length := Nat.le_of_dvd hL hdvd
  have htake : (ds.take k).length = k := by simp [List.length_take]; omega
  unfold writtenAs
  simp only [beq_iff_eq]
  constructor
  · intro e i hi
    unfold at_
    have := getD_flatten_replicate (ds.take k) k htake n i (by rw [Nat.mul_comm]; omega)
    rw [e] at this
    rw [this, getD_take' _ _ _ (Nat.mod_lt _ hk)]
  · intro hb
    apply ext_getD
    · rw [length_flatten_replicate, htake, Nat.mul_comm]; exact hkn
    · intro i hi
      rw [length_flatten_replicate, htake, Nat.mul_comm] at hi
      rw [getD_flatten_replicate _ k htake n i (by rw [Nat.mul_comm]; omega)]
      rw [getD_take' _ _ _ (Nat.mod_lt _ hk)]
      exact (hb i (by omega)).symm

-- ===========================================================================
-- 7. One id: the weighted count is 1 exactly when the id repeats
-- ===========================================================================

-- Let p₀ be the smallest period of x's L digits, and K = L / p₀ (how many
-- times the smallest block is written). x's digits are a block written n
-- times (n ≥ 2) exactly when n divides K.
theorem written_iff_dvd (ds : List Nat) (p₀ K n : Nat) (hp₀ : 0 < p₀) (hL : ds.length = p₀ * K)
    (hK : 0 < K) (hper : ∀ p, Cyc (at_ ds) ds.length p ↔ p₀ ∣ p) (hn : 2 ≤ n) :
    writtenAs ds (ds.length / n) n = true ↔ n ∣ K := by
  have hLpos : 0 < ds.length := by rw [hL]; exact Nat.mul_pos hp₀ hK
  constructor
  · intro h
    obtain ⟨hkn, hk⟩ := writtenAs_length ds _ n hLpos hn h
    obtain ⟨t, ht⟩ := (hper _).mp ((writtenAs_iff ds _ n hk hLpos hkn).mp h)
    rw [ht, hL, Nat.mul_assoc] at hkn
    exact ⟨t, by rw [Nat.mul_comm]; exact (Nat.eq_of_mul_eq_mul_left hp₀ hkn).symm⟩
  · intro ⟨t, ht⟩
    have hq : ds.length / n = p₀ * t := by
      rw [hL, ht, Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by omega)]
    rw [hq]
    have ht0 : 0 < t := by
      cases t with
      | zero => simp at ht; omega
      | succ t => omega
    apply (writtenAs_iff ds _ n (Nat.mul_pos hp₀ ht0) hLpos (by rw [hL, ht]; simp [Nat.mul_comm, Nat.mul_left_comm])).mpr
    exact (hper _).mpr ⟨t, rfl⟩

theorem repeats_iff (x : Nat) (p₀ K : Nat) (hp₀ : 0 < p₀) (hL : (digits x).length = p₀ * K)
    (hK : 0 < K) (hper : ∀ p, Cyc (at_ (digits x)) (digits x).length p ↔ p₀ ∣ p) :
    repeats x = true ↔ 2 ≤ K := by
  have hLpos : 0 < (digits x).length := by rw [hL]; exact Nat.mul_pos hp₀ hK
  unfold repeats
  simp only [List.any_eq_true, List.mem_range']
  constructor
  · intro ⟨k, _, n, ⟨i, hi, hni⟩, h⟩
    have hn : 2 ≤ n := by omega
    obtain ⟨hkn, hk⟩ := writtenAs_length _ k n hLpos hn h
    obtain ⟨t, ht⟩ := (hper k).mp ((writtenAs_iff _ k n hk hLpos hkn).mp h)
    rw [ht, hL, Nat.mul_assoc] at hkn
    have hKe := (Nat.eq_of_mul_eq_mul_left hp₀ hkn)
    have ht0 : 0 < t := by
      cases t with
      | zero => simp at ht; omega
      | succ t => omega
    have : 2 * 1 ≤ n * t := Nat.mul_le_mul hn ht0
    rw [← hKe, Nat.mul_comm]; omega
  · intro hK2
    have hKL : K ≤ (digits x).length := by rw [hL]; exact Nat.le_mul_of_pos_left K hp₀
    have hpL : p₀ ≤ (digits x).length := by rw [hL]; exact Nat.le_mul_of_pos_right p₀ hK
    refine ⟨p₀, ⟨p₀ - 1, by omega, by omega⟩, K, ⟨K - 2, by omega, by omega⟩, ?_⟩
    exact (writtenAs_iff _ p₀ K hp₀ hLpos hL.symm).mpr ((hper p₀).mpr (Nat.dvd_refl _))

-- The program's terms for one id x, before the weights.
def term (size : Nat) (x k n : Nat) : Int :=
  if k * n ≤ size then weight n * (if writtenAs (digits x) k n then (x : Int) else 0) else 0

-- For one repeat count n, only the block length L / n can count.
theorem count_k (x size n : Nat) (hn : 2 ≤ n) (hLs : (digits x).length ≤ size) (hLpos : 0 < (digits x).length) :
    sumBy (fun k => term size x k n) (List.range' 1 size)
      = if writtenAs (digits x) ((digits x).length / n) n then weight n * x else 0 := by
  rw [sumBy_single _ ((digits x).length / n) ?off size 1]
  · by_cases h : writtenAs (digits x) ((digits x).length / n) n = true
    · obtain ⟨hkn, hk⟩ := writtenAs_length _ _ n hLpos hn h
      have hle : (digits x).length / n ≤ (digits x).length := Nat.div_le_self _ _
      rw [if_pos (by omega), if_pos h]
      unfold term; rw [if_pos (by omega), if_pos h]
    · simp only [Bool.not_eq_true] at h
      unfold term; simp [h]
  case off =>
    intro k hk
    unfold term
    by_cases h : writtenAs (digits x) k n = true
    · obtain ⟨hkn, _⟩ := writtenAs_length _ _ n hLpos hn h
      exact absurd (by rw [← hkn, Nat.mul_div_cancel _ (by omega)]) hk
    · simp only [Bool.not_eq_true] at h; simp [h]

theorem range'_split (a b : Nat) (hab : 1 ≤ a) (h : a ≤ b) :
    List.range' 2 (b - 1) = List.range' 2 (a - 1) ++ List.range' (a + 1) (b - a) := by
  have := List.range'_append (s := 2) (m := a - 1) (n := b - a) (step := 1)
  simp only [Nat.one_mul] at this
  rw [show 2 + (a - 1) = a + 1 by omega, show a - 1 + (b - a) = b - 1 by omega] at this
  exact this.symm

-- One id: the program's terms add up to x if x repeats, else 0.
theorem count_id (x size : Nat) (hLs : (digits x).length ≤ size) (hLpos : 0 < (digits x).length) :
    sumBy (fun k => sumBy (fun n => term size x k n) (List.range' 2 (size - 1))) (List.range' 1 size)
      = if repeats x then (x : Int) else 0 := by
  obtain ⟨p₀, hp₀, ⟨K, hK⟩, _, hper⟩ := smallest_period (at_ (digits x)) _ hLpos
  have hK0 : 0 < K := by
    cases K with
    | zero => rw [Nat.mul_zero] at hK; omega
    | succ K => omega
  have hKs : K ≤ size := by
    have : K ≤ (digits x).length := by rw [hK]; exact Nat.le_mul_of_pos_left K hp₀
    omega
  rw [sumBy_swap]
  rw [sumBy_congr _ (fun n => if K % n = 0 then weight n * x else 0)]
  · rw [range'_split K size hK0 hKs, sumBy_append]
    rw [sumBy_zero _ (List.range' (K + 1) (size - K))]
    · have hd := divisorSum_ind K hK0
      unfold divisorSum at hd
      rw [sumBy_congr _ (fun n => x * (if K % n = 0 then weight n else 0))]
      · rw [sumBy_mul, hd]
        by_cases h2 : 2 ≤ K
        · rw [if_pos h2, if_pos ((repeats_iff x p₀ K hp₀ hK hK0 hper).mpr h2)]; simp
        · rw [if_neg h2, if_neg (by rw [repeats_iff x p₀ K hp₀ hK hK0 hper]; exact h2)]; simp
      · intro n _; split <;> simp [Int.mul_comm]
    · intro n hn
      simp [List.mem_range'] at hn
      have : K % n ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [this]
  · intro n hn
    simp [List.mem_range'] at hn
    rw [count_k x size n (by omega) hLs hLpos]
    have hiff := written_iff_dvd (digits x) p₀ K n hp₀ hK hK0 hper (by omega)
    by_cases h : K % n = 0
    · rw [if_pos (hiff.mpr (Nat.dvd_of_mod_eq_zero h)), if_pos h]
    · rw [if_neg (fun hw => h (Nat.mod_eq_zero_of_dvd (hiff.mp hw))), if_neg h]

-- ===========================================================================
-- 8. The digit bridge: `repeated` adds the ids that are a block written n times
-- ===========================================================================

-- Stitchwort already proves all of this section for any n ≥ 2 (`repeatedIds`
-- in aoc/src/day02/part2proof.sw); it is here so the Lean file is complete.

-- 8a. Digits -----------------------------------------------------------------

theorem digits_lt (x : Nat) (h : x < 10) : digits x = [x] := by
  rw [digits]; simp [h]

theorem digits_ge (x : Nat) (h : 10 ≤ x) : digits x = digits (x / 10) ++ [x % 10] := by
  rw [digits]; simp [show ¬ x < 10 by omega]

theorem digits_length_pos (x : Nat) : 0 < (digits x).length := by
  by_cases h : x < 10
  · rw [digits_lt x h]; simp
  · rw [digits_ge x (by omega)]; simp

theorem digits_length_mono : ∀ y x, x ≤ y → (digits x).length ≤ (digits y).length := by
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro x hxy
    by_cases hx : x < 10
    · rw [digits_lt x hx]; exact digits_length_pos y
    · rw [digits_ge x (by omega), digits_ge y (by omega)]
      simp only [List.length_append, List.length_singleton]
      have := ih (y / 10) (by omega) (x / 10) (by omega)
      omega

theorem digits_lt_ten : ∀ x, ∀ d ∈ digits x, d < 10 := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro d hd
    by_cases hx : x < 10
    · rw [digits_lt x hx] at hd; simp at hd; omega
    · rw [digits_ge x (by omega)] at hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact ih (x / 10) (by omega) d hd
      · omega

def fromDigits (ds : List Nat) : Nat := ds.foldl (fun a d => 10 * a + d) 0

theorem foldl_digits (l : List Nat) :
    ∀ acc, l.foldl (fun a d => 10 * a + d) acc = acc * 10 ^ l.length + fromDigits l := by
  induction l with
  | nil => intro acc; simp [fromDigits]
  | cons d t ih =>
    intro acc
    simp only [fromDigits, List.foldl_cons, List.length_cons, Nat.mul_zero, Nat.zero_add]
    rw [ih (10 * acc + d), ih d, Nat.pow_succ]
    grind

theorem fromDigits_append (l₁ l₂ : List Nat) :
    fromDigits (l₁ ++ l₂) = fromDigits l₁ * 10 ^ l₂.length + fromDigits l₂ := by
  show List.foldl _ 0 (l₁ ++ l₂) = _
  rw [List.foldl_append, foldl_digits]; rfl

theorem fromDigits_single (d : Nat) : fromDigits [d] = d := by simp [fromDigits]

theorem fromDigits_digits : ∀ x, fromDigits (digits x) = x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    by_cases hx : x < 10
    · rw [digits_lt x hx, fromDigits_single]
    · rw [digits_ge x (by omega), fromDigits_append, ih (x / 10) (by omega), fromDigits_single]
      simp; omega

theorem fromDigits_cons (d : Nat) (t : List Nat) : fromDigits (d :: t) = d * 10 ^ t.length + fromDigits t := by
  rw [show d :: t = [d] ++ t from rfl, fromDigits_append, fromDigits_single]

theorem fromDigits_lt (l : List Nat) (h : ∀ d ∈ l, d < 10) : fromDigits l < 10 ^ l.length := by
  induction l with
  | nil => simp [fromDigits]
  | cons d t ih =>
    rw [fromDigits_cons, List.length_cons, Nat.pow_succ]
    have h1 := ih (fun e he => h e (by simp [he]))
    have h2 : d + 1 ≤ 10 := h d (by simp)
    have := Nat.mul_le_mul_right (10 ^ t.length) h2
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm (10 ^ t.length) 10]
    omega

-- Induction adding one element at the end.
theorem snoc_induction (P : List Nat → Prop) (h0 : P []) (hs : ∀ l d, P l → P (l ++ [d])) :
    ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons d t ih => rw [List.reverse_cons]; exact hs _ _ ih

theorem pow_pred_mul (L : Nat) (h : 1 ≤ L) : 10 ^ L = 10 ^ (L - 1) * 10 := by
  rw [← Nat.pow_succ]; congr 1; omega

-- Digits with no leading 0 are the digits of their value.
theorem digits_fromDigits (l : List Nat) (hne : l ≠ []) (hd : ∀ d ∈ l, d < 10)
    (hb : 10 ^ (l.length - 1) ≤ fromDigits l) : digits (fromDigits l) = l := by
  revert hne hd hb
  refine snoc_induction (fun l => l ≠ [] → (∀ d ∈ l, d < 10) → 10 ^ (l.length - 1) ≤ fromDigits l →
    digits (fromDigits l) = l) (fun hne => absurd rfl hne) ?_ l
  intro l d ih hne hd hb
  · have hd10 := hd d (by simp)
    rw [fromDigits_append, fromDigits_single, List.length_singleton, Nat.pow_one] at hb ⊢
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hb
    by_cases hl : l = []
    · subst hl
      simp only [fromDigits, List.foldl_nil, Nat.zero_mul, Nat.zero_add, List.nil_append]
      exact digits_lt d hd10
    · have hlpos : 1 ≤ l.length := List.length_pos_iff.mpr hl
      rw [pow_pred_mul _ hlpos] at hb
      have hfl : 10 ^ (l.length - 1) ≤ fromDigits l := by omega
      have hp : 1 ≤ 10 ^ (l.length - 1) := Nat.pow_pos (by decide)
      rw [digits_ge _ (by omega), show (fromDigits l * 10 + d) / 10 = fromDigits l by omega,
        show (fromDigits l * 10 + d) % 10 = d by omega, ih hl (fun e he => hd e (by simp [he])) hfl]

theorem digits_bounds : ∀ b, 1 ≤ b → 10 ^ ((digits b).length - 1) ≤ b ∧ b < 10 ^ (digits b).length := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro hb
    by_cases h : b < 10
    · rw [digits_lt b h]; simp; omega
    · rw [digits_ge b (by omega)]
      obtain ⟨h1, h2⟩ := ih (b / 10) (by omega) (by omega)
      have e := pow_pred_mul _ (digits_length_pos (b / 10))
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, Nat.pow_succ]
      constructor <;> omega

theorem digits_length_of_bounds (k b : Nat) (hk : 1 ≤ k) (h1 : 10 ^ (k - 1) ≤ b) (h2 : b < 10 ^ k) :
    (digits b).length = k := by
  have hb : 1 ≤ b := Nat.le_trans (Nat.pow_pos (by decide)) h1
  obtain ⟨h3, h4⟩ := digits_bounds b hb
  have hL := digits_length_pos b
  have a := (Nat.pow_lt_pow_iff_right (a := 10) (by decide)).mp (Nat.lt_of_le_of_lt h3 h2)
  have c := (Nat.pow_lt_pow_iff_right (a := 10) (by decide)).mp (Nat.lt_of_le_of_lt h1 h4)
  omega

-- The digits of a written after the digits of c.
theorem digits_append : ∀ c a, 1 ≤ a → digits (a * 10 ^ (digits c).length + c) = digits a ++ digits c := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro a ha
    by_cases hc : c < 10
    · rw [digits_lt c hc]; simp only [List.length_singleton, Nat.pow_one]
      rw [digits_ge _ (by omega), show (a * 10 + c) / 10 = a by omega, show (a * 10 + c) % 10 = c by omega]
    · rw [digits_ge c (by omega)]
      simp only [List.length_append, List.length_singleton, Nat.pow_succ, ← Nat.mul_assoc]
      have hp : 1 ≤ a * 10 ^ (digits (c / 10)).length := Nat.mul_pos ha (Nat.pow_pos (by decide))
      rw [digits_ge _ (by omega),
        show (a * 10 ^ (digits (c / 10)).length * 10 + c) / 10 = a * 10 ^ (digits (c / 10)).length + c / 10 by omega,
        show (a * 10 ^ (digits (c / 10)).length * 10 + c) % 10 = c % 10 by omega,
        ih (c / 10) (by omega) a ha, List.append_assoc]

-- 8b. A block written n times --------------------------------------------------

theorem multiplier_snoc (k n : Nat) : multiplier k (n + 1) = multiplier k n + 10 ^ (k * n) := by
  simp [multiplier, List.range_succ, List.sum_append]

theorem multiplier_succ (k : Nat) : ∀ n, multiplier k (n + 1) = multiplier k n * 10 ^ k + 1 := by
  intro n
  induction n with
  | zero => simp [multiplier]
  | succ n ih =>
    rw [multiplier_snoc k (n + 1), multiplier_snoc k n, Nat.add_mul, Nat.mul_succ, Nat.pow_add]
    rw [multiplier_snoc k n] at ih
    omega

theorem multiplier_pos (k n : Nat) (hn : 1 ≤ n) : 1 ≤ multiplier k n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [multiplier_succ]; omega

theorem digits_rep (b : Nat) (hb : 1 ≤ b) :
    ∀ n, digits (b * multiplier (digits b).length (n + 1)) = (List.replicate (n + 1) (digits b)).flatten := by
  intro n
  induction n with
  | zero => simp [multiplier]
  | succ n ih =>
    have hpos : 1 ≤ b * multiplier (digits b).length (n + 1) := Nat.mul_pos hb (multiplier_pos _ _ (by omega))
    rw [multiplier_succ, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, digits_append b _ hpos, ih,
      List.replicate_succ' (n := n + 1), List.flatten_append]
    simp

-- A k-digit block written n times has digits that are that block n times.
theorem written_of_block (k n b : Nat) (hk : 1 ≤ k) (hn : 1 ≤ n) (h1 : 10 ^ (k - 1) ≤ b) (h2 : b < 10 ^ k) :
    writtenAs (digits (b * multiplier k n)) k n = true := by
  have hL := digits_length_of_bounds k b hk h1 h2
  have hb : 1 ≤ b := Nat.le_trans (Nat.pow_pos (by decide)) h1
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [← hL, digits_rep b hb n']
  have htake : ((List.replicate (n' + 1) (digits b)).flatten).take (digits b).length = digits b := by
    rw [List.replicate_succ, List.flatten_cons, List.take_left' rfl]
  unfold writtenAs
  rw [htake]
  simp

-- And an id whose digits are a k-digit block written n ≥ 2 times is that
-- block times the multiplier.
theorem block_of_written (x k n : Nat) (hn : 2 ≤ n) (h : writtenAs (digits x) k n = true) :
    ∃ b, 10 ^ (k - 1) ≤ b ∧ b < 10 ^ k ∧ b * multiplier k n = x := by
  have hLpos := digits_length_pos x
  obtain ⟨hkn, hk⟩ := writtenAs_length _ k n hLpos hn h
  have hkL : k ≤ (digits x).length := by rw [← hkn]; exact Nat.le_mul_of_pos_right k (by omega)
  have e : (List.replicate n ((digits x).take k)).flatten = digits x := by
    unfold writtenAs at h; simpa using h
  obtain ⟨blk, hblk⟩ : ∃ blk, blk = (digits x).take k := ⟨_, rfl⟩
  rw [← hblk] at e
  have hblen : blk.length = k := by rw [hblk, List.length_take]; omega
  have hlt10 := digits_lt_ten x
  have hsplit : digits x = blk ++ (digits x).drop k := by rw [hblk]; exact (List.take_append_drop k _).symm
  have hdroplen : ((digits x).drop k).length = (digits x).length - k := List.length_drop
  have hx : x = fromDigits blk * 10 ^ ((digits x).length - k) + fromDigits ((digits x).drop k) := by
    have := fromDigits_digits x
    rw [hsplit, fromDigits_append, hdroplen] at this
    exact this.symm
  have hrest := fromDigits_lt ((digits x).drop k) (fun d hd => hlt10 d (List.mem_of_mem_drop hd))
  rw [hdroplen] at hrest
  have hblk_lt := fromDigits_lt blk (fun d hd => hlt10 d (by rw [hblk] at hd; exact List.mem_of_mem_take hd))
  rw [hblen] at hblk_lt
  have hx1 : 1 ≤ x := by
    by_cases hx : x < 10
    · rw [digits_lt x hx] at hkn; simp at hkn
      have : k * 2 ≤ k * n := Nat.mul_le_mul_left k hn
      omega
    · omega
  obtain ⟨hxb, _⟩ := digits_bounds x hx1
  have hlow : 10 ^ (k - 1) ≤ fromDigits blk := by
    have e2 : 10 ^ ((digits x).length - 1) = 10 ^ (k - 1) * 10 ^ ((digits x).length - k) := by
      rw [← Nat.pow_add]; congr 1; omega
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_mul_lt_mul_right (a := 10 ^ ((digits x).length - k))
    rw [Nat.succ_mul]
    omega
  refine ⟨fromDigits blk, hlow, hblk_lt, ?_⟩
  have hcanon : digits (fromDigits blk) = blk :=
    digits_fromDigits blk (by intro hn; rw [hn] at hblen; simp at hblen; omega)
      (fun d hd => hlt10 d (by rw [hblk] at hd; exact List.mem_of_mem_take hd)) (by rw [hblen]; exact hlow)
  have hb1 : 1 ≤ fromDigits blk := Nat.le_trans (Nat.pow_pos (by decide)) hlow
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hd := digits_rep (fromDigits blk) hb1 n'
  rw [hcanon, hblen, e] at hd
  rw [← fromDigits_digits (fromDigits blk * multiplier k (n' + 1)), hd, fromDigits_digits]

-- 8c. Counting blocks as ids ---------------------------------------------------

-- The k-digit numbers.
def blocks (k : Nat) : List Nat := List.range' (10 ^ (k - 1)) (10 ^ k - 10 ^ (k - 1))

theorem pow_pred_le (k : Nat) : 10 ^ (k - 1) ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) (by omega)

-- For one id x: the blocks that make x add up to x when x's digits are a
-- k-digit block written n times, else to 0.
theorem block_count (x k n : Nat) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    sumBy (fun b => if b * multiplier k n = x then (x : Int) else 0) (blocks k)
      = if writtenAs (digits x) k n then (x : Int) else 0 := by
  have hm := multiplier_pos k n (by omega)
  have hp := pow_pred_le k
  by_cases h : writtenAs (digits x) k n = true
  · obtain ⟨b, h1, h2, hbx⟩ := block_of_written x k n hn h
    rw [if_pos h, blocks, sumBy_single _ b ?off, if_pos (by omega), if_pos hbx]
    case off =>
      intro b' hb'
      rw [if_neg]
      intro e
      exact hb' (Nat.eq_of_mul_eq_mul_right hm (e.trans hbx.symm))
  · rw [if_neg h]
    apply sumBy_zero
    intro b hb
    simp only [blocks, List.mem_range'] at hb
    obtain ⟨i, hi, hbi⟩ := hb
    rw [if_neg]
    intro e
    apply h
    rw [← e]
    exact written_of_block k n b hk (by omega) (by omega) (by omega)

-- Walking the blocks is walking the ids.
theorem blocks_as_ids (r : Range) (k n : Nat) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    sumBy (fun b => if r.lo ≤ b * multiplier k n ∧ b * multiplier k n ≤ r.hi
        then ((b * multiplier k n : Nat) : Int) else 0) (blocks k)
      = sumBy (fun x => if writtenAs (digits x) k n then (x : Int) else 0) r.ids := by
  rw [sumBy_congr _ (fun b => sumBy (fun x => if b * multiplier k n = x then (x : Int) else 0) r.ids)]
  · rw [sumBy_swap]
    exact sumBy_congr _ _ _ (fun x _ => block_count x k n hk hn)
  · intro b _
    unfold Range.ids
    rw [sumBy_single _ (b * multiplier k n) (fun x hx => by rw [if_neg (Ne.symm hx)])]
    by_cases hin : r.lo ≤ b * multiplier k n ∧ b * multiplier k n ≤ r.hi
    · rw [if_pos hin, if_pos (by omega), if_pos rfl]
    · rw [if_neg hin, if_neg (by omega)]

-- 8d. The arithmetic series --------------------------------------------------

-- Keeping the terms between p and q of a run of numbers.
theorem sumBy_window (f : Nat → Int) (p q : Nat) : ∀ c s,
    sumBy (fun b => if p ≤ b ∧ b ≤ q then f b else 0) (List.range' s c)
      = sumBy f (List.range' (max p s) (min (q + 1) (s + c) - max p s)) := by
  intro c
  induction c with
  | zero => intro s; rw [show min (q + 1) (s + 0) - max p s = 0 by omega]; rfl
  | succ c ih =>
    intro s
    rw [List.range'_succ]; simp only [sumBy]; rw [ih (s + 1)]
    by_cases h1 : p ≤ s ∧ s ≤ q
    · rw [if_pos h1, show max p s = s by omega, show max p (s + 1) = s + 1 by omega,
        show min (q + 1) (s + (c + 1)) - s = (min (q + 1) (s + 1 + c) - (s + 1)) + 1 by omega,
        List.range'_succ]
      rfl
    · rw [if_neg h1, Int.zero_add]
      by_cases h2 : s < p
      · rw [show max p (s + 1) = max p s by omega, show s + 1 + c = s + (c + 1) by omega]
      · rw [show min (q + 1) (s + 1 + c) - max p (s + 1) = 0 by omega,
          show min (q + 1) (s + (c + 1)) - max p s = 0 by omega]
        rfl

theorem sumBy_natCast_mul (m : Nat) (l : List Nat) :
    sumBy (fun b => ((b * m : Nat) : Int)) l = ((m * l.sum : Nat) : Int) := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih => simp only [sumBy, ih, List.sum_cons]; push_cast; grind

-- Gauss: lo + ... + hi.
theorem gauss (lo hi : Nat) (h : lo ≤ hi) :
    (List.range' lo (hi + 1 - lo)).sum = (lo + hi) * (hi - lo + 1) / 2 := by
  rw [List.sum_range']
  obtain ⟨c, rfl⟩ : ∃ c, hi = lo + c := ⟨hi - lo, by omega⟩
  rw [show lo + c + 1 - lo = c + 1 by omega, show lo + c - lo + 1 = c + 1 by omega, Nat.add_sub_cancel,
    Nat.mul_one, show (lo + (lo + c)) * (c + 1) = 2 * (lo * (c + 1)) + (c + 1) * c by grind,
    Nat.mul_add_div (by decide), Nat.mul_comm (c + 1) lo]

-- (a) The arithmetic sum is the brute-force sum over blocks.
theorem repeated_blocks (r : Range) (k n : Nat) (hn : 1 ≤ n) :
    (repeated r k n : Int) = sumBy (fun b => if r.lo ≤ b * multiplier k n ∧ b * multiplier k n ≤ r.hi
        then ((b * multiplier k n : Nat) : Int) else 0) (blocks k) := by
  have hm := multiplier_pos k n hn
  have hp := pow_pred_le k
  have hp1 : 1 ≤ 10 ^ k := Nat.pow_pos (by decide)
  -- lo ≤ b·m iff b ≥ lo/m rounded up; b·m ≤ hi iff b ≤ hi/m rounded down.
  rw [sumBy_congr _ (fun b => if (r.lo + multiplier k n - 1) / multiplier k n ≤ b ∧ b ≤ r.hi / multiplier k n
      then ((b * multiplier k n : Nat) : Int) else 0)]
  · unfold blocks
    rw [sumBy_window, show 10 ^ (k - 1) + (10 ^ k - 10 ^ (k - 1)) = 10 ^ k by omega]
    unfold repeated
    simp only [show multiplier k n ≠ 0 by omega, if_true, ne_eq, not_false_eq_true]
    rw [sumBy_natCast_mul]
    generalize (r.lo + multiplier k n - 1) / multiplier k n = c
    generalize r.hi / multiplier k n = d
    by_cases hle : max (10 ^ (k - 1)) c ≤ min (10 ^ k - 1) d
    · rw [if_pos hle, ← gauss _ _ hle, Nat.max_comm c,
        show min (d + 1) (10 ^ k) - max (10 ^ (k - 1)) c = min (10 ^ k - 1) d + 1 - max (10 ^ (k - 1)) c by omega]
    · rw [if_neg hle, show min (d + 1) (10 ^ k) - max c (10 ^ (k - 1)) = 0 by omega]
      simp
  · intro b _
    have e1 : r.lo ≤ b * multiplier k n ↔ (r.lo + multiplier k n - 1) / multiplier k n ≤ b := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega), Nat.mul_comm]; omega
    have e2 : b * multiplier k n ≤ r.hi ↔ b ≤ r.hi / multiplier k n := (Nat.le_div_iff_mul_le (by omega)).symm
    simp only [e1, e2]

-- (1) `repeated r k n` adds the ids of the range whose digits are a k-digit
-- block written n times.
theorem repeatedIds (r : Range) (k n : Nat) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (repeated r k n : Int) = sumBy (fun x => if writtenAs (digits x) k n then (x : Int) else 0) r.ids := by
  rw [repeated_blocks r k n (by omega), blocks_as_ids r k n hk hn]

-- ===========================================================================
-- 9. Part 2 is right, for every input
-- ===========================================================================

theorem sumBy_ite {α} (c : Prop) [Decidable c] (f : α → Int) (l : List α) :
    (if c then sumBy f l else 0) = sumBy (fun x => if c then f x else 0) l := by
  by_cases h : c
  · simp [h]
  · simp [h]; exact (sumBy_zero _ _ (fun _ _ => rfl)).symm

theorem invalid_eq (r : Range) :
    invalid r = sumBy (fun x => if repeats x then (x : Int) else 0) r.ids := by
  unfold invalid
  -- Each (k, n) term as a sum over the ids.
  rw [sumBy_congr _ (fun k => sumBy (fun n => sumBy (fun x => term (digits r.hi).length x k n) r.ids)
      (List.range' 2 ((digits r.hi).length - 1))) _ ?step]
  · rw [sumBy_congr _ (fun k => sumBy (fun x => sumBy (fun n => term (digits r.hi).length x k n)
        (List.range' 2 ((digits r.hi).length - 1))) r.ids) _ (fun k _ => sumBy_swap _ _ _)]
    rw [sumBy_swap]
    apply sumBy_congr
    intro x hx
    simp [Range.ids, List.mem_range'] at hx
    exact count_id x _ (digits_length_mono r.hi x (by omega)) (digits_length_pos x)
  case step =>
    intro k hk
    simp [List.mem_range'] at hk
    apply sumBy_congr
    intro n hn
    simp [List.mem_range'] at hn
    rw [repeatedIds r k n (by omega) (by omega), ← sumBy_mul, sumBy_ite]
    rfl

theorem sumBy_cast (ranges : List Range) :
    sumBy invalid ranges = ((part2Spec ranges : Nat) : Int) := by
  unfold part2Spec
  induction ranges with
  | nil => rfl
  | cons r rs ih =>
    simp only [sumBy, List.map_cons, List.sum_cons, Int.natCast_add, ih, invalid_eq, filter_sum_eq]

-- Part 2 is the sum of the ids, in all the ranges, whose digits are some
-- block written two or more times. For every input.
theorem part2Correct (ranges : List Range) : solvePart2 ranges = part2Spec ranges := by
  unfold solvePart2; rw [sumBy_cast]; rfl

-- ===========================================================================
-- 10. The example, and a cross-check on ids of more than 10 digits
-- ===========================================================================

def example_ : List Range :=
  [⟨11, 22⟩, ⟨95, 115⟩, ⟨998, 1012⟩, ⟨1188511880, 1188511890⟩, ⟨222220, 222224⟩,
   ⟨1698522, 1698528⟩, ⟨446443, 446449⟩, ⟨38593856, 38593862⟩, ⟨565653, 565659⟩,
   ⟨824824821, 824824827⟩, ⟨2121212118, 2121212124⟩]

#eval (solvePart2 example_, part2Spec example_)  -- (4174379265, 4174379265)

-- Ranges of 11 to 20 digits around ids with 11, 13 and 17 copies (no weight
-- in the old table), 12 = 2·2·3 copies, 3 copies of a 4-digit block, and so
-- on: the program against walking the ids.
def bigRanges : List Range :=
  [⟨11111111100, 11111111200⟩,                               -- 1 written 11 times
   ⟨1111111111100, 1111111111200⟩,                           -- 1 written 13 times
   ⟨111111111111 - 50, 111111111111 + 50⟩,                   -- 1 written 12 times
   ⟨121212121212 - 50, 121212121212 + 50⟩,                   -- 12 written 6 times
   ⟨123412341234 - 50, 123412341234 + 50⟩,                   -- 1234 written 3 times
   ⟨99999999999 - 30, 99999999999 + 30⟩,                     -- crosses into 12 digits
   ⟨11111111111111111 - 20, 11111111111111111 + 20⟩,         -- 17 digits
   ⟨1212121212121212121 - 20, 1212121212121212121 + 20⟩,     -- 19 digits, no repeat
   ⟨10101010101010101010 - 20, 10101010101010101010 + 20⟩]   -- 10 written 10 times

#eval bigRanges.map fun r => (solvePart2 [r], part2Spec [r])
#eval solvePart2 bigRanges == part2Spec bigRanges  -- true

-- Every id up to 200,000 one range at a time, and 4,001-id windows around
-- some 11- and 12-digit repeats.
def manyRanges : List Range :=
  (List.range 4000).map (fun i => ⟨50 * i, 50 * i + 49⟩) ++
  [⟨11111111111 - 2000, 11111111111 + 2000⟩, ⟨999999999999 - 2000, 999999999999 + 2000⟩,
   ⟨100000000000 - 2000, 100000000000 + 2000⟩, ⟨123123123123 - 2000, 123123123123 + 2000⟩]

#eval manyRanges.all fun r => solvePart2 [r] == part2Spec [r]  -- true

-- No `sorry`: only Lean's standard axioms.
#print axioms part2Correct
