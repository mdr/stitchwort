------------------------------------------------------------------------
-- Advent of Code 2025, day 1, in Agda with the standard library,
-- mirroring Stitchwort's aoc/src/day01/day01.sw: a dial numbered 0 to `highest` is
-- turned left or right. Part 1 counts the turns that end on 0; part 2
-- counts every click that lands on 0. The theorem `zerosPassedCorrect`
-- says part 2's arithmetic count equals turning the dial one click at a
-- time, for any dial, start and turns.
------------------------------------------------------------------------

module Day01 where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; s≤s⁻¹; _≡ᵇ_; _%_; _/_; NonZero)
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.Show using (readMaybe)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _⊖_; _%ℕ_)
import Data.Integer.Properties as ℤP
open import Data.Integer.DivMod using (n%ℕd<d)
open import Data.List.Base
  using (List; []; _∷_; _++_; drop; zipWith; concatMap; replicate; foldl; length; filterᵇ; mapMaybe)
open import Data.List.Scans.Base using (scanl)
open import Data.Nat.ListAction using (sum)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String; uncons)
open import Data.Char.Base using (Char)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Definitions ---------------------------------------------------------

data Turn : Set where
  left right : (distance : ℕ) → Turn

-- "L68" is `left 68`.
parseTurn : String → Maybe Turn
parseTurn t with uncons t
... | just ('L' , rest) = map left (readMaybe 10 rest)
... | just ('R' , rest) = map right (readMaybe 10 rest)
... | _ = nothing

-- A turn, one click at a time: `left 3` is three `left 1`s.
clicks : Turn → List Turn
clicks (left n)  = replicate n (left 1)
clicks (right n) = replicate n (right 1)

-- A dial numbered 0 to `highest`, at `position`.
record Dial (highest : ℕ) : Set where
  constructor mkDial
  field
    position : ℕ
    inRange  : position ≤ highest
open Dial

variable highest : ℕ

-- Any integer, wrapped onto the dial.
fromInt : (highest : ℕ) → ℤ → Dial highest
fromInt highest x = mkDial (x %ℕ suc highest) (s≤s⁻¹ (n%ℕd<d x (suc highest)))

-- Where a turn leaves the dial.
move : Dial highest → Turn → Dial highest
move {highest} d (left n)  = fromInt highest (+ position d ℤ.- + n)
move {highest} d (right n) = fromInt highest (+ position d ℤ.+ + n)

isZero : Dial highest → Bool
isZero d = position d ≡ᵇ 0

-- How many clicks of a turn land on 0.
zerosDuring : Dial highest → Turn → ℕ
zerosDuring {highest} d (right n) = (position d + n) / suc highest
zerosDuring {highest} d (left n)  = ((suc highest ∸ position d) % suc highest + n) / suc highest

-- Part 1: the positions after each turn that are 0.
zerosLandedOn : Dial highest → List Turn → ℕ
zerosLandedOn start turns = length (filterᵇ isZero (drop 1 (scanl move start turns)))

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
zerosPassed : Dial highest → List Turn → ℕ
zerosPassed start turns = sum (zipWith zerosDuring (scanl move start turns) turns)

-- The specification of part 2: count the zeros click by click.
zerosPassedSpec : Dial highest → List Turn → ℕ
zerosPassedSpec start turns = zerosLandedOn start (concatMap clicks turns)

dial : Dial 99
dial = mkDial 50 (m≤m+n 50 49)

solvePart1 solvePart2 : List Turn → ℕ
solvePart1 = zerosLandedOn dial
solvePart2 = zerosPassed dial

example : List Turn
example = mapMaybe parseTurn ("L68" ∷ "L30" ∷ "R48" ∷ "L5" ∷ "R60" ∷ "L55" ∷ "L1" ∷ "L99" ∷ "R14" ∷ "L82" ∷ [])

_ : _≡_ {A = ℕ × ℕ} (solvePart1 example , solvePart2 example) (3 , 6)
_ = refl

_ : zerosPassedSpec dial example ≡ 6
_ = refl

-- Proofs --------------------------------------------------------------

-- Two dials at the same position are the same (`≤` proofs are unique).
dialExt : {d e : Dial highest} → position d ≡ position e → d ≡ e
dialExt {d = mkDial a p} {mkDial .a q} refl = cong (mkDial a) (≤-irrelevant p q)

modSelf : ∀ h → suc h % suc h ≡ 0
modSelf h = n%n≡0 (suc h)

[n+m]/n≡1+m/n : ∀ n m .{{_ : NonZero n}} → (n + m) / n ≡ 1 + m / n
[n+m]/n≡1+m/n n m = trans (m/n≡1+[m∸n]/n (m≤m+n n m)) (cong (λ x → 1 + x / n) (m+n∸m≡n n m))

-- Integers: what `%ℕ` does to a negative number, and going back from `h`.
negR : ℕ → ℕ → ℕ
negR d zero    = 0
negR d (suc r) = d ∸ suc r

negMod : ∀ n h → -[1+ n ] %ℕ suc h ≡ negR (suc h) (suc n % suc h)
negMod n h with suc n % suc h
... | zero  = refl
... | suc _ = refl

backNear : ∀ {h n} → n < h ⊎ n ≡ h → h ∸ n ≡ negR (suc h) (suc n % suc h)
backNear (inj₁ n<h)       = cong (negR _) (sym (m≤n⇒m%n≡m n<h))
backNear {n = n} (inj₂ refl) = trans (n∸n≡0 n) (cong (negR (suc n)) (sym (n%n≡0 (suc n))))

back : ∀ h n → (h ⊖ n) %ℕ suc h ≡ -[1+ n ] %ℕ suc h
back h n with n ≤? h
... | yes n≤h = begin
    (h ⊖ n) %ℕ suc h             ≡⟨ cong (_%ℕ suc h) (ℤP.⊖-≥ n≤h) ⟩
    (h ∸ n) % suc h              ≡⟨ m≤n⇒m%n≡m (m∸n≤m h n) ⟩
    h ∸ n                        ≡⟨ backNear (m≤n⇒m<n∨m≡n n≤h) ⟩
    negR (suc h) (suc n % suc h) ≡⟨ sym (negMod n h) ⟩
    -[1+ n ] %ℕ suc h ∎
back h n | no n≰h = begin
    (h ⊖ n) %ℕ suc h             ≡⟨ cong (_%ℕ suc h) (ℤP.⊖-< (≰⇒> n≰h)) ⟩
    (ℤ.- + (n ∸ h)) %ℕ suc h     ≡⟨ cong (λ x → (ℤ.- + x) %ℕ suc h) n∸h≡1+r ⟩
    -[1+ r ] %ℕ suc h            ≡⟨ negMod r h ⟩
    negR (suc h) (suc r % suc h) ≡⟨ cong (negR (suc h)) (sym 1+n%s≡1+r%s) ⟩
    negR (suc h) (suc n % suc h) ≡⟨ sym (negMod n h) ⟩
    -[1+ n ] %ℕ suc h ∎
  where
  r = n ∸ suc h
  h<n = ≰⇒> n≰h
  n∸h≡1+r : n ∸ h ≡ suc r
  n∸h≡1+r = +-∸-assoc 1 h<n
  1+n%s≡1+r%s : suc n % suc h ≡ suc r % suc h
  1+n%s≡1+r%s = begin
    suc n % suc h               ≡⟨ cong (λ x → suc x % suc h) (sym (m∸n+n≡m h<n)) ⟩
    (suc r + suc h) % suc h     ≡⟨ [m+n]%n≡m%n (suc r) (suc h) ⟩
    suc r % suc h ∎

place : (highest : ℕ) → ℤ → ℕ
place highest x = x %ℕ suc highest

-- One click left: from 0 to `highest`, otherwise down by one.
leftZero : ∀ h → place h (+ 0 ℤ.- + 1) ≡ h
leftZero zero    = refl
leftZero (suc h) = refl

leftOne : ∀ h m → suc m ≤ h → place h (+ suc m ℤ.- + 1) ≡ m
leftOne h m sm≤h = m≤n⇒m%n≡m (<⇒≤ sm≤h)

-- Positions after a run of single clicks.
stepLeftAt : ∀ h a → a ≤ h → ∀ n → place h (+ place h (+ a ℤ.- + 1) ℤ.- + n) ≡ place h (+ a ℤ.- + suc n)
stepLeftAt h zero    _ n rewrite leftZero h | ℤP.[+m]-[+n]≡m⊖n h n = back h n
stepLeftAt h (suc m) a≤h n rewrite leftOne h m a≤h | ℤP.[+m]-[+n]≡m⊖n m n =
  cong (_%ℕ suc h) (sym (ℤP.[1+m]⊖[1+n]≡m⊖n m n))

rightAt : (d : Dial highest) (n : ℕ) → position (foldl move d (replicate n (right 1))) ≡ (position d + n) % suc highest
rightAt d zero    rewrite +-identityʳ (position d) = sym (m≤n⇒m%n≡m (inRange d))
rightAt {highest} d (suc n) = begin
  position (foldl move (move d (right 1)) (replicate n (right 1)))  ≡⟨ rightAt (move d (right 1)) n ⟩
  ((position d + 1) % s + n) % s                                    ≡⟨ %-distribˡ-+ ((position d + 1) % s) n s ⟩
  ((position d + 1) % s % s + n % s) % s                            ≡⟨ cong (λ x → (x + n % s) % s) (m%n%n≡m%n (position d + 1) s) ⟩
  ((position d + 1) % s + n % s) % s                                ≡⟨ sym (%-distribˡ-+ (position d + 1) n s) ⟩
  (position d + 1 + n) % s                                          ≡⟨ cong (_% s) (trans (+-assoc (position d) 1 n) refl) ⟩
  (position d + suc n) % s ∎
  where s = suc highest

leftAt : (d : Dial highest) (n : ℕ) → position (foldl move d (replicate n (left 1))) ≡ position (move d (left n))
leftAt {highest} d zero =
  sym (trans (cong (_% suc highest) (+-identityʳ (position d))) (m≤n⇒m%n≡m (inRange d)))
leftAt {highest} d (suc n) = trans (leftAt (move d (left 1)) n) (stepLeftAt highest (position d) (inRange d) n)

-- `zerosAfter d ts`: the zeros after each of `ts`, from `d`.
zerosAfter : Dial highest → List Turn → ℕ
zerosAfter d ts = length (filterᵇ isZero (drop 1 (scanl move d ts)))

b2n : Bool → ℕ
b2n b = if b then 1 else 0

zerosAfterCons : (d : Dial highest) (t : Turn) (ts : List Turn) →
  zerosAfter d (t ∷ ts) ≡ b2n (isZero (move d t)) + zerosAfter (move d t) ts
zerosAfterCons d t []       with isZero (move d t)
... | true  = refl
... | false = refl
zerosAfterCons d t (u ∷ us) with isZero (move d t)
... | true  = refl
... | false = refl

zerosAfterAppend : (d : Dial highest) (l₁ l₂ : List Turn) →
  zerosAfter d (l₁ ++ l₂) ≡ zerosAfter d l₁ + zerosAfter (foldl move d l₁) l₂
zerosAfterAppend d []       l₂ = refl
zerosAfterAppend d (t ∷ l₁) l₂ = begin
  zerosAfter d (t ∷ l₁ ++ l₂)                          ≡⟨ zerosAfterCons d t (l₁ ++ l₂) ⟩
  b + zerosAfter (move d t) (l₁ ++ l₂)                 ≡⟨ cong (λ x → b + x) (zerosAfterAppend (move d t) l₁ l₂) ⟩
  b + (zerosAfter (move d t) l₁ + zerosAfter e l₂)     ≡⟨ sym (+-assoc b _ _) ⟩
  b + zerosAfter (move d t) l₁ + zerosAfter e l₂       ≡⟨ cong (_+ zerosAfter e l₂) (sym (zerosAfterCons d t l₁)) ⟩
  zerosAfter d (t ∷ l₁) + zerosAfter e l₂ ∎
  where b = b2n (isZero (move d t)); e = foldl move (move d t) l₁

-- Arithmetic for one click.
stepRight : ∀ h a n → a ≤ h →
  b2n ((a + 1) % suc h ≡ᵇ 0) + ((a + 1) % suc h + n) / suc h ≡ (a + suc n) / suc h
stepRight h a n a≤h rewrite +-comm a 1 with m≤n⇒m<n∨m≡n a≤h
... | inj₁ a<h rewrite m≤n⇒m%n≡m a<h = cong (_/ suc h) (sym (+-suc a n))
... | inj₂ a≡h rewrite a≡h | modSelf h | +-suc h n = sym ([n+m]/n≡1+m/n (suc h) n)

stepLeft : ∀ h a → a ≤ h → ∀ n →
  b2n (place h (+ a ℤ.- + 1) ≡ᵇ 0) + ((suc h ∸ place h (+ a ℤ.- + 1)) % suc h + n) / suc h
    ≡ ((suc h ∸ a) % suc h + suc n) / suc h
stepLeft h zero _ n rewrite leftZero h with h
... | zero  = trans (cong suc (n/1≡n n)) (sym (n/1≡n (suc n)))
... | suc k rewrite m+n∸n≡m 1 k | modSelf (suc k) = refl
stepLeft h (suc m) a≤h n rewrite leftOne h m a≤h with m
... | zero rewrite modSelf h | m≤n⇒m%n≡m (≤-refl {h}) | +-suc h n =
  sym ([n+m]/n≡1+m/n (suc h) n)
... | suc j rewrite m≤n⇒m%n≡m (m∸n≤m h j) | m≤n⇒m%n≡m (m∸n≤m h (suc j)) =
  cong (λ x → (x + n) / suc h) (+-∸-assoc 1 (<⇒≤ a≤h)) ⨾ cong (_/ suc h) (sym (+-suc (h ∸ suc j) n))
  where _⨾_ = trans

-- One whole turn, click by click.
rightCount : (d : Dial highest) (n : ℕ) → zerosAfter d (replicate n (right 1)) ≡ zerosDuring d (right n)
rightCount d zero rewrite +-identityʳ (position d) = sym (m<n⇒m/n≡0 (s≤s (inRange d)))
rightCount {highest} d (suc n) = begin
  zerosAfter d (right 1 ∷ replicate n (right 1))                         ≡⟨ zerosAfterCons d (right 1) _ ⟩
  b2n (isZero d′) + zerosAfter d′ (replicate n (right 1))                ≡⟨ cong (λ x → b2n (isZero d′) + x) (rightCount d′ n) ⟩
  b2n (isZero d′) + (position d′ + n) / suc highest                      ≡⟨ stepRight highest (position d) n (inRange d) ⟩
  (position d + suc n) / suc highest ∎
  where d′ = move d (right 1)

leftCount : (d : Dial highest) (n : ℕ) → zerosAfter d (replicate n (left 1)) ≡ zerosDuring d (left n)
leftCount {highest} d zero = sym (trans (cong (_/ suc highest) (+-identityʳ r)) (m<n⇒m/n≡0 (m%n<n (suc highest ∸ position d) (suc highest))))
  where r = (suc highest ∸ position d) % suc highest
leftCount {highest} d (suc n) = begin
  zerosAfter d (left 1 ∷ replicate n (left 1))                            ≡⟨ zerosAfterCons d (left 1) _ ⟩
  b2n (isZero d′) + zerosAfter d′ (replicate n (left 1))                  ≡⟨ cong (λ x → b2n (isZero d′) + x) (leftCount d′ n) ⟩
  b2n (isZero d′) + zerosDuring d′ (left n)                               ≡⟨ stepLeft highest (position d) (inRange d) n ⟩
  zerosDuring d (left (suc n)) ∎
  where d′ = move d (left 1)

turnAt : (d : Dial highest) (t : Turn) → foldl move d (clicks t) ≡ move d t
turnAt d (left n)  = dialExt (leftAt d n)
turnAt d (right n) = dialExt (rightAt d n)

turnCount : (d : Dial highest) (t : Turn) → zerosAfter d (clicks t) ≡ zerosDuring d t
turnCount d (left n)  = leftCount d n
turnCount d (right n) = rightCount d n

zerosPassedFrom : (d : Dial highest) (ts : List Turn) → zerosPassed d ts ≡ zerosAfter d (concatMap clicks ts)
zerosPassedFrom d []       = refl
zerosPassedFrom d (t ∷ ts) = begin
  zerosDuring d t + zerosPassed (move d t) ts                         ≡⟨ cong (λ x → zerosDuring d t + x) (zerosPassedFrom (move d t) ts) ⟩
  zerosDuring d t + zerosAfter (move d t) rest                        ≡⟨ cong (_+ zerosAfter (move d t) rest) (sym (turnCount d t)) ⟩
  zerosAfter d (clicks t) + zerosAfter (move d t) rest                ≡⟨ cong (λ e → zerosAfter d (clicks t) + zerosAfter e rest) (sym (turnAt d t)) ⟩
  zerosAfter d (clicks t) + zerosAfter (foldl move d (clicks t)) rest ≡⟨ sym (zerosAfterAppend d (clicks t) rest) ⟩
  zerosAfter d (clicks t ++ rest) ∎
  where rest = concatMap clicks ts

-- The arithmetic count is the click-by-click count, for any dial, start and turns.
zerosPassedCorrect : (start : Dial highest) (turns : List Turn) → zerosPassed start turns ≡ zerosPassedSpec start turns
zerosPassedCorrect = zerosPassedFrom

part2Puzzle : (turns : List Turn) → solvePart2 turns ≡ zerosPassedSpec dial turns
part2Puzzle = zerosPassedCorrect dial
