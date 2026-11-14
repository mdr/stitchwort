-- Proving with Stitchwort
--
-- Chapter 1. Computing
--
-- About 45 minutes.
--
-- In this chapter you write a small program, a game of rock, paper,
-- scissors, and test it. Then you state facts about it as theorems, and
-- prove them the simplest way there is: by computing. You also see what
-- happens when a statement is false, because the checker can often show
-- you an input that breaks it.
--
-- Keep the Goals panel open beside the editor ("Stitchwort: Show Goals",
-- chapter 0).

namespace Book.Computing

-- ## 1.1 A type with three values
--
-- In rock, paper, scissors, each player picks one of three moves. Here is
-- a type for them:

type Move = | Rock | Paper | Scissors

-- `type` lists every value a `Move` can be. `Rock`, `Paper` and `Scissors`
-- are its *constructors*: each one, on its own, is a `Move`, and there are
-- no others. Hover over `Paper` to see that the editor knows it as a
-- constructor of `Move`.
--
-- Constructors and functions are drawn in different colours, so you can
-- tell them apart at a glance in the code below.

-- ## 1.2 A function by cases
--
-- Rock blunts scissors, paper wraps rock, and scissors cut paper. Every
-- other pair is not a win:

--| Whether `mine` beats `theirs`.
def beats: (mine: Move) → (theirs: Move) → Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

-- `beats` takes two moves and gives a `Bool`, `True` or `False`. Its body
-- is a list of *arms*, one per line, each with a pattern for the two
-- moves on the left of `=>` and the answer on the right. To compute
-- `beats Paper Rock`, the arms are tried from the top, and the first whose
-- pattern fits gives the answer: here the second, so `True`. `_` fits any
-- move, so the last arm catches the six pairs that aren't wins.
--
-- `Bool` isn't built into the language. Press F12 on `Bool` in the line
-- `def beats` above: the editor opens the standard library at
--
--     type Bool: Type =
--       | False
--       | True
--
-- a type with two constructors, just like `Move` with three. Go back with
-- Ctrl-minus (Alt-Left if you aren't on a Mac).

-- ## 1.3 Tests

test "rock blunts scissors" := beats Rock Scissors
test "paper wraps rock" := beats Paper Rock
test "scissors cut paper" := beats Scissors Paper
test "rock doesn't beat paper" := not (beats Rock Paper)
test "nobody wins a draw" := not (beats Rock Rock)

-- A test is some code that should come out `True`. Click "▶ Run tests"
-- above the first one: it runs every test in the file, the five here and
-- the two in section 1.4, and the message says 7 passed.
--
-- Now break the program. In `beats`, change the arm `Paper, Rock => True`
-- to `Paper, Scissors => True`, a slip anyone could make. The tests don't
-- turn red, because tests run only when you ask. Two theorems further down
-- do turn red by themselves (section 1.6 is about those), but they don't
-- stop the tests: a test runs whenever everything it uses checks, and these
-- tests use `beats` and `play`, not the theorems. Click "▶ Run tests" and
-- two of them fail: "paper wraps rock", which is the arm you changed
-- ("evaluated to False"), and "rock against paper loses" in section 1.4
-- (`==` is False, with `Draw` on the left and `Lose` on the right). The
-- other five pass. Put the arm back and click again to see all seven pass.

-- ## 1.4 Outcomes, and `if`
--
-- A round has three possible outcomes for the player:

type Outcome = | Win | Lose | Draw

--| How a round ends for the player who chose `mine`.
def play (mine theirs: Move): Outcome := if beats mine theirs then Win else if beats theirs mine then Lose else Draw

test "rock against paper loses" := play Rock Paper == Lose
test "paper against paper is a draw" := play Paper Paper == Draw

-- `play` is written with `if`. Since `beats` gives a `Bool`, it can be
-- the condition of an `if` directly. `==` compares two values and gives a
-- `Bool`, so a test can use it.

-- ## 1.5 A hole in a definition
--
-- You don't have to write a function in one go. Here is one that gives
-- the outcome of the same round for the other player:

--| How the round that ended `outcome` for one player ended for the other.
def otherSide (outcome: Outcome): Outcome := match outcome with
  | Win => Lose
  | Lose => Win
  | Draw => Draw

-- It's finished, so take it apart to see how it could have been
-- written. Select everything after `:=` in `otherSide`, type `?`, and put
-- your cursor on the `?`. The Goals panel shows
--
--     outcome: Outcome
--     ⊢ Outcome
--
-- Above the line are the names you can use (`outcome`, a value of type
-- `Outcome`); below it, after `⊢`, what the hole must be: some `Outcome`.
-- `match` looks at a value and picks the arm for its constructor, as the
-- arms of `beats` did, but for a value you have in hand rather than the
-- function's arguments. Type the `match` back in, and as you type each arm,
-- watch the holes and the panel. Undo (Cmd-Z) works too.

-- ## 1.6 Theorems
--
-- A test checks one input when you run it. A *theorem* states a fact, and
-- the checker checks its proof as you type.

theorem rockBeatsScissors: beats Rock Scissors := rfl

theorem paperLosesToScissors: play Paper Scissors = Lose := rfl

theorem otherSideOfAWin: otherSide (play Paper Rock) = Lose := rfl

-- A theorem has a name, then a colon and its statement, then `:=` and its
-- proof. `rfl` proves an equation `a = b` when both sides compute to the
-- same value. In `paperLosesToScissors` the checker runs `play Paper
-- Scissors`, gets `Lose`, and compares it with `Lose`. That's all `rfl`
-- does, and it's surprising how far it goes.
--
-- `rockBeatsScissors` has no `=` at all. A `Bool` used as a statement means
-- "this is `True`", so the statement is `beats Rock Scissors = True`, and
-- `rfl` proves it by computing. Hover over `rockBeatsScissors` to see its
-- statement, which the box writes as just `beats Rock Scissors`.
--
-- So far a theorem is no better than a test: it says something about
-- one round. The point of theorems is that they can say something about
-- every round at once. That needs a variable, and the next section shows
-- what goes wrong when `rfl` meets one.

-- ## 1.7 When computing gets stuck
--
-- No move beats itself. Here is that fact for every move `m`: a
-- theorem's parameters, written like a function's, mean "for every".
-- Type this line at the end of this section, as it is:
--
--     theorem noSelfWin (m: Move): beats m m = False := rfl
--
-- `rfl` turns red. Hover over it:
--
--     `beats m m` and `False` aren't equal
--     Note 1: the left side is stuck on `m`: it can't compute further until
--             `m` is known; a `match` on `m` (or `cases m`) splits it
--     Note 2: `rfl` proves `a = b` only when both sides compute to the same
--             value
--
-- The statement is true, but `rfl` can't see that. To compute `beats m m`,
-- the checker has to pick an arm, and it can't pick one without knowing
-- which move `m` is. Computing is *stuck*. Chapter 2 is about exactly
-- this: proving a fact one case at a time. Delete the line for now.

-- ## 1.8 When a statement is false
--
-- Not every statement you write will be true, and it's worth finding out
-- early. Type this, which says rock beats everything:
--
--     theorem rockAlwaysWins (m: Move): beats Rock m := ?
--
-- Hover over the `?`. As well as the goal, the box says
--
--     Note: this statement is false; a counterexample:
--             m = Rock
--           `beats Rock m` is false:
--             left:  False
--             right: True
--
-- The checker tried the statement on moves, and found one that breaks it:
-- rock doesn't beat rock. A counterexample like this is worth more than
-- any amount of trying to prove the statement. When you see one, fix the
-- statement or the program, not the proof.
--
-- It works for a wrong proof too. Replace the `?` with `rfl`: the error
-- says `rfl` can't prove it, and the same counterexample is in the notes.
--
-- Now one with a wrong program instead. Change the first arm of `play` to
-- `if beats theirs mine then Win`, swapping the two moves.
-- `paperLosesToScissors` and `otherSideOfAWin` turn red straight away;
-- hover over the first, and the notes say that `play Paper Scissors` now
-- computes to `Win`, and that the statement is false. The tests catch the
-- slip too, and as in section 1.3 they run while the theorems are red:
-- "rock against paper loses" fails, with `Win` on the left and `Lose` on
-- the right. Put `play` back, and delete `rockAlwaysWins`.
--
-- What you've seen:
--
-- - a `type` lists its constructors, and a function picks an arm by them;
-- - a test checks one case when you run it; a theorem is checked as you
--   type;
-- - `rfl` proves an equation by computing both sides;
-- - a `Bool` as a statement means it is `True`;
-- - computing gets stuck on a variable whose constructor isn't known;
-- - a false statement often comes with a counterexample, on a `?` or on a
--   failed proof.

-- ## Exercises
--
-- Each exercise is a `?` for you to replace. The Problems panel lists the
-- ones still open.

-- Exercise 1.1 (one star). Write `counter`, the move that beats a given
-- move, so that `counterBeatsRock` holds. Prove it with `rfl`.

--| The move that beats `m`.
def counter (m: Move): Move := ?

theorem counterBeatsRock: beats (counter Rock) Rock := ?

-- Exercise 1.2 (one star). British traffic lights go red, red and amber
-- together, green, amber, and back to red. Write `next`, then prove that
-- four steps from amber come back to amber.

type Light = | Red | RedAndAmber | Green | Amber

--| The light that follows `light`.
def next (light: Light): Light := ?

theorem fourStepsFromAmber: (Amber |> next |> next |> next |> next) = Amber := ?

-- `|>` passes the value on its left to the function on its right, so the
-- statement reads in the order the lights change: `Amber |> next` is
-- `next Amber`.

-- Exercise 1.3 (two stars). `implies a b` is `False` only when `a` is
-- `True` and `b` is `False`: "if it rains, the ground is wet" is broken
-- only by rain on dry ground. Write it, then write four tests, one for
-- each pair of inputs, and run them.

--| Whether `a` implies `b`: `True` unless `a` holds and `b` doesn't.
def implies (a b: Bool): Bool := ?

-- Hint: a test of a function that is still `?` fails, naming the `?`:
-- `stitchwort test` marks it `not run` and says "`implies` isn't written
-- yet", and the test passes once the function is written.

theorem trueImpliesFalse: implies True False = False := ?

-- Then state one more theorem of your own, below: that `implies True True`
-- is `True`, and prove it.
