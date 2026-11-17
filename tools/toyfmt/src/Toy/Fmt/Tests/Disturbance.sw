--| The disturber over the goldens' formatted texts, 50 seeds each. These
--| tests check the disturber itself, that it changes layout and nothing
--| else; `Parsing.sw` runs the test that matters, that each disturbed text
--| formats back to the golden.

namespace Toy.Fmt.Tests
import Toy.Syntax (..)
import Std (List, Option, Text)

def goldens: List Golden := [groups, headers, bodies, calls, lists, operators, conditionals, comments, blankLines,
  longText, order, route, parameterGroups]

def seeds: List Nat := List.range 0 50

def Golden.disturbed (golden: Golden) (seed: Nat): Text := disturb golden.formatted seed

--| Whether every disturbed text formats back to the golden: idempotence and
--| independence from the author's layout, on real shapes.
def Golden.survivesDisturbance (golden: Golden) (format: Text → Option Text): Bool :=
  seeds.all (seed => format (golden.disturbed seed) == Some golden.formatted)

test "the layout disturber keeps every token" := goldens.all (golden =>
  seeds.all (seed => significant (disturbLayout golden.formatted seed) == significant golden.formatted))

test "the disturber keeps every comment, in order" :=
  let comments := (text: Text) => scan text |> .filter Piece.isRemark |> .map Piece.text
  goldens.all (golden => seeds.all (seed => comments (golden.disturbed seed) == comments golden.formatted))

test "the disturber changes every golden's layout" :=
  goldens.all (golden => seeds.any (seed => golden.disturbed seed != golden.formatted))

test "most seeds change the layout" :=
  goldens.all (golden => seeds.count (seed => golden.disturbed seed != golden.formatted) >= 40)

test "the same seed disturbs the same way" := goldens.all (golden => golden.disturbed 7 == golden.disturbed 7)

-- The five changes of the tree's freedoms, each taken wherever it can be
-- (odds 1), on one declaration's pieces.

def changed (change: Nat → Dice → List Piece → (List Piece, Dice)) (text: Text): Text :=
  let (pieces, _) := change 1 { state = 1 } (scan text)
  render pieces

test "a name in an expression gets brackets, a binder, a field name and a header do not" :=
  let (pieces, _) :=
    wrapOperands 1
      { state = 1 }
      { inBody = False, lineStart = True, before = None }
      (scan "fn f takes (a: Int) = g(a).b + c")
  render pieces == "fn f takes (a: Int) = (g)((a)).b + (c)"

test "a name beside a comment is not wrapped, or one at a line start" :=
  let (pieces, _) :=
    wrapOperands 1
      { state = 1 }
      { inBody = False, lineStart = True, before = None }
      (scan "let x =\n  a -- c\nlet y = b")
  render pieces == "let x =\n  a -- c\nlet y = (b)"

test "a trailing comma goes after the last item of a list, a call and a parameter list" :=
  changed (odds dice => addTrailingCommas odds dice [] None None) "fn f takes (a: Int, b: Int) = g([1, 2], (3))"
    == "fn f takes (a: Int, b: Int,) = g([1, 2,], (3),)"

test "no comma goes in an empty list, or after a comment" :=
  changed (odds dice => addTrailingCommas odds dice [] None None) "let x = f([], g(a -- c\n))"
    == "let x = f([], g(a -- c\n),)"

test "takes is dropped from a header" := changed dropTakes "fn f takes (a: Int) = a" == "fn f(a: Int) = a"

test "takes with a comment beside it stays" :=
  changed dropTakes "fn f takes -- c\n  (a: Int) = a" == "fn f takes -- c\n  (a: Int) = a"

test "a group of names is split, a group of one is not" :=
  changed (odds dice => splitGroups 100 odds dice) "fn f takes (a b c: Int, d: Nat) = a"
    == "fn f takes (a: Int, b: Int, c: Int, d: Nat) = a"

test "a comment after a closer moves before it" :=
  changed moveCommentsBeforeClosers "let x = f(g(a)) -- c" == "let x = f(g(a) -- c\n  )"

test "freedoms are changed on some golden by some seed" :=
  goldens.any (golden => seeds.any (seed => disturb golden.formatted seed != disturbLayout golden.formatted seed))

--| Whether `change`, at the default odds, alters some golden's formatted
--| text for some seed: the goldens have somewhere for each change to land.
--| (Seeds are spread wider than `disturb`'s, whose first roll barely varies
--| over 50 neighbouring seeds.)
def firesOnGoldens (change: Nat → Dice → List Piece → (List Piece, Dice)): Bool := goldens.any (golden =>
  seeds.any (seed =>
    let (pieces, _) := change defaultOdds { state = seed * 1000003 + 17 } (scan golden.formatted)
    render pieces != golden.formatted))

test "each of the five changes lands somewhere on the goldens" :=
  firesOnGoldens (odds dice => wrapOperands odds dice { inBody = False, lineStart = True, before = None })
    && firesOnGoldens (odds dice => addTrailingCommas odds dice [] None None)
    && firesOnGoldens dropTakes
    && firesOnGoldens (odds dice => splitGroups 1000 odds dice)
    && firesOnGoldens moveCommentsBeforeClosers
