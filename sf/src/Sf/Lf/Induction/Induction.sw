-- Software Foundations, Volume 1: Logical Foundations, Induction.v
-- ("Induction: Proof by Induction"), ported to Stitchwort. Copyright and
-- licence: sf/LICENSE-SF. Names and exercises follow the conventions
-- described at the top of Basics.sw: an exercise is a theorem or function
-- with `?` for the reader to fill in. The numbers are the book's own, from
-- Nat.sw, not the library's (see README.md).

namespace Sf.Lf.Induction
import Sf.Lf.Basics (..)
import Sf.Lf.Nat (Nat, ofNat, plus, mult, minus)
import Std (Eq)

-- # Separate Compilation
--
-- The chapter starts from the definitions of the previous one. The book
-- explains how to compile `Basics.v` to `Basics.vo` (with `_CoqProject`,
-- `rocq makefile` and `make`) so that `From LF Require Export Basics`
-- can find it. In Stitchwort the chapters are namespaces of one project
-- (sf/stitchwort.yaml), and `import Sf.Lf.Basics (..)` above brings in
-- the previous chapter's names. `stitchwort check` in sf/ checks every
-- chapter, in the order their imports need, and keeps what it checked in
-- a cache (`.stitchwort/cache`), so a chapter that didn't change isn't
-- checked again. There is nothing to compile by hand, and no stale
-- compiled file to cause "inconsistent assumptions" errors.

-- # Proof by Induction
--
-- We proved that `O` is a neutral element for `plus` on the *left* by
-- computing. In the book, the proof that it is also neutral on the
-- *right*,
--
--     Theorem add_0_r_firsttry : forall n:nat, n + 0 = n.
--
-- can't be done the same way: `n` is unknown, so the `match` in the
-- definition of `plus` can't compute.
--
-- (This is why the port uses the book's own numbers, Nat.sw, here.
-- Stitchwort's library `+` computes on its second argument when its first
-- is unknown, so `n + 0 = n` is `rfl` for it, and the chapter's first
-- example would have nothing to show.)
--
-- With the book's `plus`, `rfl` fails, and says why:
--
--     theorem plusN0FirstTry (n: Nat): plus n O = n := rfl
--
--     [E-REFL] Error: `rfl` can't prove this
--       ╰─── `plus n 0` and `n` aren't equal
--       Note 1: the left side is stuck on `n`: it can't compute further
--               until `n` is known; a `match` on `n` (or `cases n`) splits it
--
-- Splitting `n` into cases, as the note suggests, doesn't get us much
-- further. The case `n = O` goes through, but in the case `n = S n'` we
-- are stuck in the same way. Writing `?` for that case shows its goal:
--
--     theorem plusN0SecondTry (n: Nat): plus n O = n := match n with
--       | O => rfl
--       | S n' => ?
--
--     [GOAL] Goal: in `plusN0SecondTry`
--       ╰── n': Nat
--           ⊢ S (plus n' O) = S n'
--
-- We could split `n'` too, but since `n` can be arbitrarily large, we'd
-- never get all the way there.
--
-- To prove interesting facts about numbers, lists and other inductively
-- defined sets, we need a more powerful principle: *induction*. Recall
-- the principle of induction over the natural numbers: if `P(n)` is some
-- proposition involving a natural number `n`, and we want to show that
-- `P` holds for every `n`, we can reason like this:
--
-- - show that `P(O)` holds;
-- - show that, for any `n'`, if `P(n')` holds, then so does `P(S n')`;
-- - conclude that `P(n)` holds for all `n`.
--
-- In Rocq, the `induction` tactic turns the goal `P(n)` into those two
-- subgoals, the second with the hypothesis `P(n')` named (`IHn'`). In
-- Stitchwort, induction is recursion: the proof is a `match` on `n`, as
-- for case analysis, and in the `S n'` case the theorem may call
-- itself on `n'`. That call is the induction hypothesis: it proves
-- `P(n')`. The checker accepts it because `n'` is smaller than `n`, as
-- it would for a recursive function, so the recursion always ends.

theorem plusN0 ∀ (n: Nat): plus n O = n := match n with
  | O => rfl
  | S n' => Eq.cong S (plusN0 n')

-- In the case `O`, `plus O O = O` computes. In the case `S n'`, the goal
-- `plus (S n') O = S n'` computes to `S (plus n' O) = S n'`. The
-- induction hypothesis, `plusN0 n'`, proves `plus n' O = n'`, and
-- `Eq.cong S` puts an `S` on both sides. The book's proof of
-- that case is `simpl. rewrite -> IHn'. reflexivity.`; the Stitchwort
-- term `rewrite plusN0 n' in rfl` is the same steps and proves it too.
--
-- (The book calls this `add_0_r`, with Rocq's `+`; it is the same theorem.)
--
-- Another one by induction:

theorem minusNN ∀ (n: Nat): minus n n = O := match n with
  | O => rfl
  | S n' => minusNN n'

-- In the case `S n'`, `minus (S n') (S n')` computes to `minus n' n'`, so
-- the induction hypothesis is the whole proof.
--
-- Stitchwort can also do induction that follows a function's own
-- recursion rather than its argument's type: `match induct (f args)`
-- (docs/guide/10-proofs.md, "Induction that follows a function").

-- Exercise: 2 stars, standard, especially useful (basic_induction)
--
-- Prove these by induction. You might need results proved before.

theorem mul0R ∀ (n: Nat): mult n O = O := ?

theorem plusNSm ∀ (n m: Nat): S (plus n m) = plus n (S m) := ?

theorem addComm ∀ (n m: Nat): plus n m = plus m n := ?

theorem addAssoc ∀ (n m p: Nat): plus n (plus m p) = plus (plus n m) p := ?

-- Exercise: 2 stars, standard (double_plus)
--
-- This function doubles its argument:

def double (n: Nat): Nat := match n with
  | O => O
  | S n' => S (S (double n'))

-- Use induction to prove this simple fact about `double`:

theorem doublePlus ∀ (n: Nat): double n = plus n n := ?

-- Exercise: 2 stars, standard (eqb_refl)
--
-- This relates the computed equality `eqb` on numbers to the logical
-- equality `=` on booleans.

theorem eqbRefl ∀ (n: Nat): eqb n n = True := ?

-- Exercise: 2 stars, standard, optional (even_S)
--
-- One awkward aspect of `even n` is its recursive call on `n - 2`, which
-- makes proofs about it by induction on `n` harder: we may need an
-- induction hypothesis about `n - 2`. This lemma characterises
-- `even (S n)` in a way that works better with induction:

theorem evenS ∀ (n: Nat): even (S n) = negb (even n) := ?

-- # Proofs Within Proofs
--
-- Large proofs are often broken into a sequence of theorems, later proofs
-- using earlier ones. Sometimes a proof needs a fact too trivial to be
-- worth a name of its own. Rocq's `replace e1 with e2` replaces `e1` by
-- `e2` in the goal, and leaves a second subgoal, `e1 = e2`, to prove.
-- Stitchwort's `rewrite` takes the equation as a proof, written in
-- place:

theorem mult0Plus' ∀ (n m: Nat): mult (plus (plus n O) O) m = mult n m := rewrite plusN0 n, plusN0 n in rfl

-- Here `plusN0 n` proves `plus n O = n`, which rewrites `plus (plus n O)
-- O` to `plus n O` and then to `n`. A fact with no lemma to cite can be
-- stated in place with its proof, `rewrite (proof: a = b) in rfl`, which
-- is the closest thing to `replace`.
--
-- As another example, suppose we want to prove `(n + m) + (p + q) =
-- (m + n) + (p + q)`. The two sides differ only in the order of `m` and
-- `n` in the first inner `+`, so commutativity of addition should turn
-- one into the other. But `rewrite` isn't very smart about *where* it
-- applies a rule. There are three uses of `plus`, and rewriting with
-- `addComm` (the exercise above, as the book uses `add_comm`) with no
-- arguments affects only the *outer* one:
--
--     theorem plusRearrangeFirstTry (n m p q: Nat): plus (plus n m) (plus p q) = plus (plus m n) (plus p q) :=
--       rewrite addComm in rfl
--
--     [E-REFL] Error: `rfl` can't prove this
--       ╰─── `plus (plus p q) (plus n m)` and `plus (plus m n) (plus p q)` aren't equal
--
-- The book uses `replace` to point at the right `+`. In Stitchwort, give
-- the rule its arguments, and it rewrites `plus n m` and nothing else:

theorem plusRearrange ∀ (n m p q: Nat): plus (plus n m) (plus p q) = plus (plus m n) (plus p q) :=
  rewrite addComm n m in rfl

-- # Formal vs. Informal Proof
--
-- "Informal proofs are algorithms; formal proofs are code."
--
-- What makes a successful proof of a mathematical claim? A rough and
-- ready answer: a proof of `P` is a written (or spoken) text that
-- instills in the reader the certainty that `P` is true. A proof is an
-- act of communication.
--
-- The reader can be a program, such as Stitchwort's checker, in which
-- case the "belief" is that `P` can be derived mechanically from a set
-- of formal rules, and the proof is a recipe that guides the program in
-- checking it: a *formal* proof. Or the reader can be a human, and the
-- proof is written in a natural language, and is *informal*. Then the
-- criteria are less clear: a valid proof is one that makes the reader
-- believe `P`, but different readers are convinced by different
-- phrasings, and need different amounts of detail. In practice,
-- mathematicians have developed conventions and idioms that make this
-- communication fairly reliable, at least within a community.
--
-- This book works mostly with formal proofs, but informal ones still
-- matter: formal proofs are not very efficient ways of communicating
-- ideas between human beings. Here is a proof that addition is
-- associative, as the book writes it in Rocq:
--
--     Theorem add_assoc' : forall n m p : nat,
--       n + (m + p) = (n + m) + p.
--     Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
--       simpl. rewrite IHn'. reflexivity.  Qed.
--
-- Rocq is perfectly happy with this, but for a human it is hard to make
-- sense of: the state of the proof (the context and the goal) at each
-- point is implicit, and has to be imagined by stepping through the
-- tactics.
--
-- In Stitchwort, the proof is a term, and its shape is the shape of the
-- argument. The cases are visible as the arms of the `match`, and each
-- arm says what proves its case:

theorem addAssoc' ∀ (n m p: Nat): plus n (plus m p) = plus (plus n m) p := match n with
  | O => rfl
  | S n' => Eq.cong S (addAssoc' n' m p)

-- A (pedantic) mathematician might write the proof like this:
--
-- - *Theorem*: for any `n`, `m` and `p`,
--
--       n + (m + p) = (n + m) + p.
--
--   *Proof*: by induction on `n`.
--
--   - First, suppose `n = O`. We must show that
--
--         O + (m + p) = (O + m) + p.
--
--     This follows directly from the definition of `+`.
--
--   - Next, suppose `n = S n'`, where
--
--         n' + (m + p) = (n' + m) + p.
--
--     We must now show that
--
--         (S n') + (m + p) = ((S n') + m) + p.
--
--     By the definition of `+`, this follows from
--
--         S (n' + (m + p)) = S ((n' + m) + p),
--
--     which is immediate from the induction hypothesis. *Qed*.
--
-- The overall form is the same as the Stitchwort term's: an arm for each
-- case, in the same order. The term is more explicit than the informal
-- proof in some ways (`Eq.cong S` says how the hypothesis gives the
-- goal) and less in others: it doesn't restate the goal of each case.
-- Writing `?` in an arm, or hovering over it in the editor, shows that
-- goal.

-- Exercise: 2 stars, advanced, optional (add_comm_informal)
--
-- Translate your solution for `addComm` into an informal proof.
--
-- Theorem: addition is commutative.
--
-- Proof: (fill in here)

-- Exercise: 2 stars, standard, optional (eqb_refl_informal)
--
-- Write an informal proof of the following theorem, using the informal
-- proof of `addAssoc'` as a model. Don't just paraphrase the proof term
-- into English!
--
-- Theorem: `eqb n n = True` for any `n`.
--
-- Proof: (fill in here)

-- # More Exercises

-- Exercise: 3 stars, standard, especially useful (mul_comm)
--
-- Use `rewrite` with stated facts, as `replace` would be used, to prove
-- `addShuffle3`. You don't need induction yet.

theorem addShuffle3 ∀ (n m p: Nat): plus n (plus m p) = plus m (plus n p) := ?

-- Now prove commutativity of multiplication. You will probably want to
-- find (or define and prove) a helper theorem to use in this one. Hint:
-- what is `mult n (plus (S O) k)`?

theorem mulComm ∀ (m n: Nat): mult m n = mult n m := ?

-- Exercise: 3 stars, standard, optional (more_exercises)
--
-- Take a piece of paper. For each of the following, first think about
-- whether (a) it can be proved by computing and rewriting alone, (b) it
-- also needs case analysis (`match`), or (c) it also needs induction.
-- Write down your prediction, then fill in the proof. (This is just to
-- encourage you to reflect before you hack.)
-- which computes on its second argument when the first is unknown,
-- moves some of these from (b) or (c) to (a).

theorem lebRefl ∀ (n: Nat): leb n n = True := ?

theorem zeroNeqbS ∀ (n: Nat): eqb O (S n) = False := ?

theorem andbFalseR ∀ (b: Bool): andb b False = False := ?

theorem sNeqb0 ∀ (n: Nat): eqb (S n) O = False := ?

theorem mult1L ∀ (n: Nat): mult (S O) n = n := ?

theorem all3Spec ∀ (b c: Bool): orb (andb b c) (orb (negb b) (negb c)) = True := ?

theorem multPlusDistrR ∀ (n m p: Nat): mult (plus n m) p = plus (mult n p) (mult m p) := ?

theorem multAssoc ∀ (n m p: Nat): mult n (mult m p) = mult (mult n m) p := ?

-- # Nat to Bin and Back to Nat
--
-- Recall the type `Bin` from Basics. The book repeats `bin`, and stubs of
-- `incr` and `bin_to_nat`, here, so that this chapter can be graded on
-- its own; here they are imported from Basics, where your definitions
-- from that exercise are.
--
-- In Basics we unit-tested `binToNat`, but didn't prove it correct. Now
-- we do.

-- Exercise: 3 stars, standard, especially useful (binary_commute)
--
-- Prove that this diagram commutes:
--
--                             incr
--               Bin ----------------------> Bin
--                |                           |
--       binToNat |                           | binToNat
--                |                           |
--                v                           v
--               Nat ----------------------> Nat
--                              S
--
-- That is, incrementing a binary number and then converting it to unary
-- gives the same result as converting it first and then incrementing.
-- If changing your definitions of `incr` or `binToNat` makes this easier
-- to prove, feel free to.

theorem binToNatPresIncr ∀ (b: Bin): binToNat (incr b) = plus (S O) (binToNat b) := ?

-- Exercise: 3 stars, standard (nat_bin_nat)
--
-- Write a function that converts natural numbers to binary numbers.

--| Exercise (nat_bin_nat): replace the `?` with the definition.
def natToBin (n: Nat): Bin := ?

-- Prove that converting any `Nat` to `Bin` and back gives the number we
-- started with. Hint: the proof should go through smoothly with the
-- previous exercise as a lemma. If not, revisit your definitions and see
-- whether they are more complicated than they need to be: the shape of a
-- proof by induction follows the recursion of the program it is about, so
-- make the recursions as simple as possible.

theorem natBinNat ∀ (n: Nat): binToNat (natToBin n) = n := ?

-- # Bin to Nat and Back to Bin (Advanced)
--
-- The opposite direction, from a `Bin` to a `Nat` and back, turns out to
-- be a problem: this doesn't hold.
--
--     theorem binNatBinFails (b: Bin): natToBin (binToNat b) = b

-- We'll explore why, and prove a modified version. First some lemmas that
-- might seem unrelated, but turn out to be relevant.

-- Exercise: 2 stars, advanced (double_bin)
--
-- Prove this lemma about `double`, defined earlier in the chapter.

theorem doubleIncr ∀ (n: Nat): double (S n) = S (S (double n)) := ?

-- Now define a similar doubling function for `Bin`.

--| Exercise (double_bin): replace the `?` with the definition.
def doubleBin (b: Bin): Bin := ?

-- Check that it doubles zero correctly.

theorem doubleBinZero: doubleBin Z = Z := ?

-- Prove this lemma, which corresponds to `doubleIncr`.

theorem doubleIncrBin ∀ (b: Bin): doubleBin (incr b) = incr (incr (doubleBin b)) := ?

-- Back to the theorem we wanted, `binNatBinFails`. It fails because for
-- some `Bin`s we don't get back the *original* `Bin`, but an
-- "equivalent" one. (The book leaves that notion undefined, for you to
-- think about.)
--
-- Explain in a comment here why the failure happens. If you are stuck,
-- think of other ways to write `doubleBin` that might not satisfy
-- `doubleBinZero` but otherwise seem right.
--
-- (Stitchwort's counterexample search finds such a `Bin` for you, once
-- `natToBin` and `binToNat` are defined: state `binNatBinFails` as a
-- theorem with `?` as its proof and run `stitchwort check`.)
--
-- To solve the problem, we can introduce a *normalisation* function that
-- picks the simplest `Bin` of all the equivalent ones. Then we can prove
-- that converting from `Bin` to `Nat` and back gives that simplest `Bin`.

-- Exercise: 4 stars, advanced (bin_nat_bin)
--
-- Define `normalize`. Keep its definition as simple as possible, for the
-- later proofs to go smoothly. Don't use `binToNat` or `natToBin`, but do
-- use `doubleBin`. Hint: make the recursion *always* reach the end of the
-- `Bin`, and process each bit only once. Don't try to "look ahead" at
-- later bits.

--| Exercise (bin_nat_bin): replace the `?` with the definition.
def normalize (b: Bin): Bin := ?

-- It is wise to check with some examples that `normalize` works as you
-- intend before going on. (Write them here.)
--
-- Finally, prove the main theorem. The inductive cases can be a bit
-- tricky. Hint: start by trying to prove the main statement, see where
-- you get stuck, and see whether a lemma (perhaps with its own inductive
-- proof) lets the main proof progress. The book's solution has one lemma
-- for the `B0` case (which also uses `doubleIncrBin`) and one for the
-- `B1` case.

theorem binNatBin ∀ (b: Bin): natToBin (binToNat b) = normalize b := ?
