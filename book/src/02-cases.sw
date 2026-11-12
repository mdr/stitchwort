-- Proving with Stitchwort
--
-- Chapter 2. Cases
--
-- About 60 minutes.
--
-- Chapter 1 ended with a theorem `rfl` couldn't prove: no move beats
-- itself. `beats m m` is stuck, because the checker can't pick an arm of
-- `beats` without knowing which move `m` is. This chapter gets it
-- unstuck the obvious way: by looking at each move in turn. A proof by
-- cases has the same shape as the function it is about, and the editor
-- writes most of that shape for you.
--
-- The game comes from chapter 1: this line makes its definitions
-- available here.

namespace Book.Cases
import Std (Bool, Void)
import Book.Computing (Move, beats, Outcome, play, otherSide)

-- ## 2.1 One move at a time
--
-- The proof of `noSelfWin` below is finished. To see how it's built, take
-- it apart: select everything after `:=` and type `?`, so that it reads
--
--     theorem noSelfWin (m: Move): beats m m = False := ?
--
-- Read the parameter `(m: Move)` as "for every move `m`". Inside the
-- proof, `m` is a move you know nothing about, and that's why computing
-- gets stuck.
--
-- Put the cursor on the `?` and press Cmd-. (or click the light bulb that
-- appears). A short menu of quick actions opens. Pick "Split on `m`". The
-- `?` becomes
--
--     match m with
--       | Rock => ?
--       | Paper => ?
--       | Scissors => ?
--
-- one arm per constructor of `Move`, each with its own hole. Move the
-- cursor from one `?` to the next and watch the Goals panel. In the first
-- arm it shows
--
--     ⊢ beats Rock Rock = False
--       computes to False = False
--
-- Inside the arm for `Rock`, the checker knows that `m` is `Rock`, so
-- the goal says `Rock` where it said `m`. The second line, dimmed in the
-- editor, is what the goal computes to: `beats Rock Rock` is `False`,
-- since the first three arms of `beats` don't fit and the last one does.
-- Both sides are now the same, which is when `rfl` works. The other two
-- arms show `beats Paper Paper = False` and `beats Scissors Scissors =
-- False`, each computing to `False = False`. Replace each `?`
-- with `rfl`, and you have the proof back:

theorem noSelfWin (m: Move): beats m m = False :=
  match m with
    | Rock => rfl
    | Paper => rfl
    | Scissors => rfl

-- This is the same `match` you wrote in `otherSide` in chapter 1, used
-- in a proof. A proof by cases is a function that answers each case
-- separately, and the checker accepts it only if every case is answered.

-- ## 2.2 Missing arms
--
-- When you write a `match` by hand, it's easy to forget a case. Try it:
-- in `otherSideTwice` below, delete the arms for `Lose` and `Draw`.
--
-- `match` turns red: `E-NONEXHAUSTIVE`, the cases `Lose` and `Draw` are
-- missing. Put the cursor on `match` and press Cmd-.: "Add the missing
-- arms" adds one arm for each, with `?` for its proof. Fill them in with
-- `rfl` again.

theorem otherSideTwice (outcome: Outcome): otherSide (otherSide outcome) = outcome :=
  match outcome with
    | Win => rfl
    | Lose => rfl
    | Draw => rfl

-- A program's `match` has to cover every case for the same reason: a
-- function must give an answer for every input. In a proof that's what
-- makes it a proof about *every* outcome.

-- ## 2.3 Two moves
--
-- `otherSide` should agree with swapping the players: the round from the
-- other side is the round played the other way round. That is
-- `otherSideSwaps` below, a theorem with two moves. Replace its proof
-- with `?`, and build it again with the editor.
--
-- Splitting one move isn't enough: in the arm for `Rock` the goal is
-- `otherSide (play Rock theirs) = play theirs Rock`, still stuck on
-- `theirs`. So:
--
-- 1. On the `?`, Cmd-. and "Split on `mine`". Three arms.
-- 2. On the first arm's `?`, Cmd-. and "Split on `theirs`". The editor
--    doesn't put a second `match` inside the arm. It adds `theirs` as a
--    second column of the same `match`, so the arms list both moves:
--
--        match mine, theirs with
--          | Rock, Rock => ?
--          | Rock, Paper => ?
--          | Rock, Scissors => ?
--          | Paper, _ => ?
--          | Scissors, _ => ?
--
--    The two arms not yet split get `_` in the new column. `_` matches
--    any move, so those arms still cover every `theirs`.
-- 3. On the `?` of `| Paper, _ => ?`, Cmd-. and "Split on `theirs`" again.
--    The arm turns into three, `| Paper, Rock`, `| Paper, Paper` and
--    `| Paper, Scissors`. Do the same for `Scissors`.
--
-- Now there are nine arms, and in each the goal computes, so each is
-- `rfl`, as here:

theorem otherSideSwaps (mine: Move) (theirs: Move): otherSide (play mine theirs) = play theirs mine :=
  match mine, theirs with
    | Rock, Rock => rfl
    | Rock, Paper => rfl
    | Rock, Scissors => rfl
    | Paper, Rock => rfl
    | Paper, Paper => rfl
    | Paper, Scissors => rfl
    | Scissors, Rock => rfl
    | Scissors, Paper => rfl
    | Scissors, Scissors => rfl

-- Nine arms are the nine rounds the game can have; the proof checks every
-- one. A `match` inside an arm (a *nested* `match`) would do the same job:
--
--     match mine with
--       | Rock =>
--         match theirs with
--           | Rock => rfl
--           ...
--
-- Both are fine. Columns are shorter when every arm splits both moves.

-- ## 2.4 When `rfl` works with a variable
--
-- Splitting isn't always needed. `rfl` is stuck only when computing needs
-- to know a value it doesn't. Here is a function that sometimes doesn't
-- need to look at both of its arguments.
--
-- A question asked of a database may get the answer yes, no, or "don't
-- know" (a missing value). "Both" for such answers is no if either is no,
-- yes if both are yes, and otherwise unknown:

type Answer =
  | Yes
  | No
  | Unknown

--| "Both `a` and `b`", when either may be `Unknown`: `No` if either is
--| `No`, `Yes` if both are `Yes`, and `Unknown` otherwise.
def both: (a: Answer) → (b: Answer) → Answer
  | Yes, b => b
  | No, _ => No
  | Unknown, No => No
  | Unknown, _ => Unknown

theorem yesAndAnything (b: Answer): both Yes b = b := rfl

theorem noAndAnything (b: Answer): both No b = No := rfl

-- Both are `rfl`, with `b` unknown. To compute `both No b`, the checker
-- tries the arms in order: `Yes, b` doesn't fit, since the first answer
-- is `No`; `No, _` fits whatever `b` is. So the answer is `No` without
-- ever looking at `b`.
--
-- `both b No = No` is just as true, but it is stuck: the first arm
-- already needs to know whether `b` is `Yes`. Whether `rfl` works depends
-- on how the function is written, not only on what it computes. When it
-- fails, the message says what it's stuck on, and that's what to split.

-- ## 2.5 Hypotheses
--
-- A theorem can assume something. A parameter whose type is a statement,
-- such as `(h: beats mine theirs)`, is a *hypothesis*: "if `mine` beats
-- `theirs`, then ...". Inside the proof, `h` is evidence that it's true,
-- and you can use it.

-- Here is the proof one step at a time, as a `calc` chain (a chain of
-- equalities, read down the page: the first line says where it starts and
-- each `_ = ...` line says what the previous value equals):

theorem beatsMeansWinSteps (mine: Move) (theirs: Move) (h: beats mine theirs): play mine theirs = Win :=
  calc play mine theirs
    _ = (if beats mine theirs then Win else if beats theirs mine then Lose else Draw)
    _ = (if True then Win else if beats theirs mine then Lose else Draw) := rewrite h in rfl
    _ = Win

-- `_` stands for the value on the line above, so each line is one equation:
-- `play mine theirs = (if beats mine theirs ...)`, and so on. The chain
-- proves the first value equals the last, which is the theorem. A line with
-- no `:=` needs no reason: the checker just computes, and it must agree.
-- Here:
--
-- 1. The first step unfolds `play`, which is computing.
-- 2. The second uses `h`. It is the equation `beats mine theirs = True` (a
--    `Bool` used as a statement means it is `True`; the Goals panel writes
--    it as `h: beats mine theirs`). `rewrite h in rfl` replaces `beats mine
--    theirs` by `True`, and then `rfl` checks the two sides are now equal.
-- 3. The last step computes the `if`: `if True then Win else ...` is `Win`.
--
-- Put the cursor on each `_` line with the Goals panel open: it shows what
-- the chain has proved so far. On the last line it says
--
--     so far play mine theirs = (if True then Win else if beats theirs mine then Lose else Draw)
--            computes to play mine theirs = Win
--     line   ⊢ Win = Win
--
-- The same proof in one word:

theorem beatsMeansWin (mine: Move) (theirs: Move) (h: beats mine theirs): play mine theirs = Win :=
  rewrite h

-- `rewrite h` does all three steps. It computes until it finds `beats mine
-- theirs` (unfolding `play`), replaces it with `True`, and finishes by
-- computing, which turns `if True then Win else ...` into `Win`. No cases
-- at all: the proof follows `play`'s `if` instead of the moves.
--
-- Put the cursor on `rewrite`, with the Goals panel open: it shows the goal
-- before the rewrite, the rule and the goal after it:
--
--     before ⊢ play mine theirs = Win
--     rule   beats mine theirs
--     after  ⊢ (if True then Win else if beats theirs mine then Lose else Draw) = Win
--            computes to Win = Win
--
-- Sometimes a hypothesis rules a case out. Rock beats only scissors:

theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs with
    | Rock => Void.exfalso (Bool.falseNotTrue h)
    | Paper => Void.exfalso (Bool.falseNotTrue h)
    | Scissors => rfl

-- Replace the proof of the `Rock` arm with `?` and look at the panel:
--
--     h: False = True
--     ⊢ Rock = Scissors
--
-- The goal is false, but so is `h`: in this arm, `h` says rock beats
-- rock, which computes to `False = True`. This case can't happen, and the
-- proof says so in two steps. `Bool.falseNotTrue` states `False ≠ True`,
-- and `a ≠ b` is short for `a = b -> Void`: a function that takes a proof
-- of `a = b` and gives back a value of `Void`, the type with no values at
-- all. So `Bool.falseNotTrue h`, the function applied to `h`'s proof of
-- `False = True`, is a `Void`. Then `Void.exfalso` turns a `Void` into a
-- proof of anything, since there is never a `Void` to give it. Hover over
-- each to read its statement. They live in the library's `Bool` and `Void`
-- namespaces, which is what the line `import Std (Bool, Void)` at the top
-- of the file is for.
--
-- That is what happens in an impossible case, and there are two shorter
-- ways to say it. Match on `h` too, and write `()` where its pattern goes,
-- with no `=>` and no proof:

theorem rockBeatsOnlyScissorsAbsurd (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs, h with
    | Rock, ()
    | Paper, ()
    | Scissors, _ => rfl

-- `()` is the pattern for a value that can't exist. The checker computes
-- the type `h` has in that arm, `False = True`, sees that it has no
-- proofs, and builds the `Void.exfalso` proof above itself. If the type
-- could have a value, it says so instead (`E-NOT-EMPTY`).
--
-- Shorter still, leave the impossible arms out:

theorem rockBeatsOnlyScissorsLeftOut (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs with
    | Scissors => rfl

-- A `match` must cover every case, but a case where some hypothesis can't
-- hold, like `h` for `Rock` and `Paper`, doesn't need covering: the checker
-- fills in the `()` arm for it. Leave out a case that can happen, and the
-- error names the arm still to write.

-- ## 2.6 `cases`: all of this in one word
--
-- You've now split by hand often enough to see the pattern: split the
-- variable the goal is stuck on, compute, and close each case, with `rfl`
-- or from a hypothesis that can't hold. `cases` does all of that by
-- itself:

theorem otherSideSwapsAgain (mine: Move) (theirs: Move): otherSide (play mine theirs) = play theirs mine :=
  cases

theorem rockBeatsOnlyScissorsAgain (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  cases

-- Try replacing the proofs of `noSelfWin` and `otherSideTwice` with
-- `cases` too. On a `?`, Cmd-. also offers "Search for a proof" (after the
-- split actions), which looks for proofs that close the goal and lists
-- them, best first, each already checked; for goals like these the first is
-- `cases`.
--
-- When to use which:
--
-- - `cases` for routine splits like these, where seeing the cases teaches
--   you nothing;
-- - a `match` when you want to see each case, when the cases need
--   different proofs, or when `cases` fails and you want to know which
--   case is the problem. (Its error names the case it couldn't close.)
--
-- `cases` has limits: it stops at 64 cases, and it can't split a number
-- or a list, which have endlessly many values. Chapter 3 is about those.
--
-- What you've seen:
--
-- - a theorem's parameters mean "for every"; a hypothesis is a parameter
--   whose type is a statement;
-- - a proof by cases is a `match`, the same as in a program, and every
--   case must be covered;
-- - Cmd-. on a `?` splits a variable; on a `match` with cases missing it
--   adds them; on a variable in an arm's pattern it splits that arm;
-- - inside an arm, the goal knows which constructor it is, so it can
--   compute;
-- - `rfl` works with a variable when computing doesn't need its value;
-- - `rewrite h` uses an equation `h` to change the goal;
-- - `Void.exfalso (Bool.falseNotTrue h)` closes a case that can't happen;
-- - `cases` does routine splits in one word.

-- ## Exercises
--
-- Exercises 2.1 to 2.4 are marked "(by hand)": `cases` proves each in one
-- word, so write the `match` yourself first, using the splits. Then, if
-- you like, replace your proof with `cases` and check that it agrees.

-- Exercise 2.1 (one star, by hand). A move played against itself is a
-- draw.

theorem selfPlayDraws (m: Move): play m m = Draw := ?

-- Exercise 2.2 (two stars, by hand). Two moves can't beat each other. Some
-- of the nine cases can't happen; `h` says which.

theorem noMutualWins (mine: Move) (theirs: Move) (h: beats mine theirs): beats theirs mine = False := ?

-- Exercise 2.3 (two stars, by hand). The order of the answers doesn't
-- matter to `both`.

theorem bothSymmetric (a: Answer) (b: Answer): both a b = both b a := ?

-- Exercise 2.4 (one star, by hand). A `No` on the right decides it too,
-- though not by `rfl` alone (section 2.4 says why).

theorem anythingAndNo (a: Answer): both a No = No := ?

-- Exercise 2.5 (one star). If you win a round, the other player loses it.
-- Hint: one word.

theorem winMeansTheyLose (mine: Move) (theirs: Move) (h: play mine theirs = Win): play theirs mine = Lose := ?
