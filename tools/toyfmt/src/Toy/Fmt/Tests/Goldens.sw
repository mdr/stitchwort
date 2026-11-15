--| The golden pairs: one for each printing rule, P1 to P10, and two mixed.
--| Each has a source as an author might write it, the tree the parser must
--| make of it, and the formatted text. The tests here print the tree;
--| `Parsing.sw` checks that the source parses to it and that both texts
--| format to the formatted one.

namespace Toy.Fmt.Tests
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (List, Option, Text)

type Golden = { width: Nat, source: Text, tree: SourceFile, formatted: Text }

def Golden.printed (golden: Golden): Text := (golden.tree.print golden.width).text

--| P1: a group goes on one line if it fits, else all its breaks break; the
--| group inside decides again, and fits.
def groups: Golden :=
  {
    width = 40,
    source = """
      let big = scale(area(width, height),
            factorOfSafety)
      """,
    tree = sprig [value "big" (call "scale" [call "area" [v "width", v "height"], v "factorOfSafety"])],
    formatted = """
      let big =
        scale(
          area(width, height),
          factorOfSafety
        )
      """
  }

test "P1: a group breaks every break, and an inner group decides again" := groups.printed == groups.formatted

--| P2: a header's parameters, one a line at +4 when they don't fit, with
--| `) =` back at column 0.
def headers: Golden :=
  {
    width = 40,
    source = """
      fn add(a,b) = a+b
      fn distance(fromRow, fromColumn, toRow, toColumn) = abs(fromRow - toRow) + abs(fromColumn - toColumn)
      """,
    tree = sprig [
      fn "add" ["a", "b"] (expr (op Plus (v "a") (v "b"))),
      fn "distance"
        ["fromRow", "fromColumn", "toRow", "toColumn"]
        (expr
          (op Plus
            (call "abs" [op Minus (v "fromRow") (v "toRow")])
            (call "abs" [op Minus (v "fromColumn") (v "toColumn")])))
    ],
    formatted = """
      fn add(a, b) = a + b
      fn distance(
          fromRow,
          fromColumn,
          toRow,
          toColumn
      ) =
        abs(fromRow - toRow)
          + abs(fromColumn - toColumn)
      """
  }

test "P2: parameters go one a line at +4" := headers.printed == headers.formatted

--| P3: a body on the `=` line, else one line below, else broken below; a
--| block always below.
def bodies: Golden :=
  {
    width = 40,
    source = """
      let short =
          1 + 2
      let medium = someFunction(alpha, beta, gamma)
      let long = combine(firstArgument, secondArgument, third)
      fn two() =
        let x = 1
        x + 1
      """,
    tree = sprig [
      value "short" (op Plus (num "1") (num "2")),
      value "medium" (call "someFunction" [v "alpha", v "beta", v "gamma"]),
      value "long" (call "combine" [v "firstArgument", v "secondArgument", v "third"]),
      fn "two" [] (block [letIn "x" (num "1"), bare (op Plus (v "x") (num "1"))])
    ],
    formatted = """
      let short = 1 + 2
      let medium =
        someFunction(alpha, beta, gamma)
      let long =
        combine(
          firstArgument,
          secondArgument,
          third
        )
      fn two() =
        let x = 1
        x + 1
      """
  }

test "P3: a body goes on the line, one line below, or broken below" := bodies.printed == bodies.formatted

--| P4: a call's arguments one a line at +2, `)` back at the call's line.
def calls: Golden :=
  {
    width = 40,
    source = """
      fn main() =
        let order = load( path )
        print(describe(order), total(order.items,
          order.rates))
      """,
    tree = sprig [
      fn "main" []
        (block [
          letIn "order" (call "load" [v "path"]),
          bare
            (call "print" [call "describe" [v "order"], call "total" [dots "order" ["items"], dots "order" ["rates"]]])
        ])
    ],
    formatted = """
      fn main() =
        let order = load(path)
        print(
          describe(order),
          total(order.items, order.rates)
        )
      """
  }

test "P4: arguments go one a line at +2" := calls.printed == calls.formatted

--| P5: list items fill their lines, the `]` after the last.
def lists: Golden :=
  {
    width = 40,
    source = """
      let none = [ ]
      let few = [1,2,3]
      let primes = [2, 3, 5, 7, 11, 13, 17, 19, 23,
                    29, 31, 37, 41, 43, 47, 53, 59, 61]
      """,
    tree = sprig [
      value "none" (list []),
      value "few" (list [num "1", num "2", num "3"]),
      value "primes"
        (list
          (["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "31", "37", "41", "43", "47", "53", "59", "61"].map
              num))
    ],
    formatted = """
      let none = []
      let few = [1, 2, 3]
      let primes = [2, 3, 5, 7, 11, 13, 17,
        19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61]
      """
  }

test "P5: list items fill their lines" := lists.printed == lists.formatted

--| P6: a chain of one level breaks before every operator, at +2; tighter
--| levels stay whole if they fit; brackets stay.
def operators: Golden :=
  {
    width = 40,
    source = """
      let mixed = (a+b)*c - d
      let check = first.ready && second.ready && third.ready && fourth.ready
      let sum = alphaValue * betaValue + gammaValue * deltaValue - epsilonValue
      """,
    tree = sprig [
      value "mixed" (op Minus (op Times (Bracketed (op Plus (v "a") (v "b"))) (v "c")) (v "d")),
      value "check"
        (op And
          (op And (op And (dots "first" ["ready"]) (dots "second" ["ready"])) (dots "third" ["ready"]))
          (dots "fourth" ["ready"])),
      value "sum"
        (op Minus
          (op Plus (op Times (v "alphaValue") (v "betaValue")) (op Times (v "gammaValue") (v "deltaValue")))
          (v "epsilonValue"))
    ],
    formatted = """
      let mixed = (a + b) * c - d
      let check =
        first.ready
          && second.ready
          && third.ready
          && fourth.ready
      let sum =
        alphaValue * betaValue
          + gammaValue * deltaValue
          - epsilonValue
      """
  }

test "P6: an operator chain breaks before every operator of its level" := operators.printed == operators.formatted

--| P7: `if` on one line, else `else` at the `if`'s column, and a branch
--| that doesn't fit after its keyword below at +2.
def conditionals: Golden :=
  {
    width = 40,
    source = """
      fn sign(x) =
        if x < 0 then -1 else 1
      fn describe(count) = if count == 0 then "nothing at all" else "some things"
      fn classify(n) = if n < 10 then "small" else if n < 100 then "medium" else "large"
      fn pick(flag) = if flag then computeTheFirstAnswer(alpha, beta) else 0
      """,
    tree = sprig [
      fn "sign" ["x"] (expr (If (op LessThan (v "x") (num "0")) (expr (Negate (num "1"))) (expr (num "1")))),
      fn "describe"
        ["count"]
        (expr (If (op EqualTo (v "count") (num "0")) (expr (str "nothing at all")) (expr (str "some things")))),
      fn "classify"
        ["n"]
        (expr
          (If
            (op LessThan (v "n") (num "10"))
            (expr (str "small"))
            (expr (If (op LessThan (v "n") (num "100")) (expr (str "medium")) (expr (str "large")))))),
      fn "pick"
        ["flag"]
        (expr (If (v "flag") (expr (call "computeTheFirstAnswer" [v "alpha", v "beta"])) (expr (num "0"))))
    ],
    formatted = """
      fn sign(x) = if x < 0 then -1 else 1
      fn describe(count) =
        if count == 0 then "nothing at all"
        else "some things"
      fn classify(n) =
        if n < 10 then "small"
        else if n < 100 then "medium"
        else "large"
      fn pick(flag) =
        if flag then
          computeTheFirstAnswer(alpha, beta)
        else 0
      """
  }

test "P7: an if puts else at its column, and a long branch below" := conditionals.printed == conditionals.formatted

--| P8: own-line comments above their item, trailing ones after it, and a
--| comment no rule places leaves its declaration as written.
def comments: Golden :=
  {
    width = 40,
    source = """
      -- Totals for one order.
      fn total(order) =
          -- the base price
          let base = sum(order.items)   -- before tax
          base + tax(base)
      let weights = [
        -- light
        1, 2, -- two
        3]
      fn odd(x) = -- why
        x  %  2
      """,
    tree = sprig [
      note "-- Totals for one order.",
      fn "total"
        ["order"]
        (block [
          plain (StatementNote { text = "-- the base price" }),
          plain
            (Let "base" {
              statements = [plain (Bare (call "sum" [dots "order" ["items"]]) (Some { text = "-- before tax" }))]
            }),
          bare (op Plus (v "base") (call "tax" [v "base"]))
        ]),
      value "weights"
        (ListLiteral [
          { comments = [{ text = "-- light" }], value = num "1", trailing = None },
          { comments = [], value = num "2", trailing = Some { text = "-- two" } },
          item (num "3")
        ]),
      plain (AsWritten "fn odd(x) = -- why\n  x  %  2")
    ],
    formatted = """
      -- Totals for one order.
      fn total(order) =
        -- the base price
        let base = sum(order.items) -- before tax
        base + tax(base)
      let weights = [
        -- light
        1, 2, -- two
        3]
      fn odd(x) = -- why
        x  %  2
      """
  }

test "P8: comments stay with their items" := comments.printed == comments.formatted

test "P8: a declaration left as written is counted" := (comments.tree.print comments.width).asWritten == 1

--| P9: blank lines kept, as one, between declarations and statements.
def blankLines: Golden :=
  {
    width = 40,
    source = """
      let a = 1



      let b = 2
      fn f() =

        let x = 1


        let y = 2
        x +

          y
      """,
    tree = sprig [
      value "a" (num "1"),
      afterBlank (Value "b" (expr (num "2"))),
      fn "f" [] (block [letIn "x" (num "1"), afterBlank (Let "y" (expr (num "2"))), bare (op Plus (v "x") (v "y"))])
    ],
    formatted = """
      let a = 1

      let b = 2
      fn f() =
        let x = 1

        let y = 2
        x + y
      """
  }

test "P9: blank lines are kept, as one, between lines of a list" := blankLines.printed == blankLines.formatted

--| P10: a string never splits, and a line that can't fit stays long; width
--| counts characters, so twenty arrows are twenty columns.
def longText: Golden :=
  {
    width = 40,
    source = """
      let greeting = "a string much too long to fit in forty columns"
      let arrows =
        "→→→→→→→→→→→→→→→→→→→→"
      """,
    tree = sprig [
      value "greeting" (str "a string much too long to fit in forty columns"),
      value "arrows" (str "→→→→→→→→→→→→→→→→→→→→")
    ],
    formatted = """
      let greeting =
        "a string much too long to fit in forty columns"
      let arrows = "→→→→→→→→→→→→→→→→→→→→"
      """
  }

test "P10: strings never split, and width counts characters" := longText.printed == longText.formatted

--| Mixed: the plan's example, at width 80.
def order: Golden :=
  {
    width = 80,
    source = """
      -- Totals for one order.
      fn total(order,rates) =
        let base = sum(order.items.map(price))
        let tax = base*rates.tax/100

        if rates.threshold < base then base + tax - discount(order, rates) -- loyal
        else base+tax

      let names = ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"]
      """,
    tree = sprig [
      note "-- Totals for one order.",
      fn "total"
        ["order", "rates"]
        (block [
          letIn "base" (call "sum" [Call (dots "order" ["items", "map"]) [item (v "price")]]),
          letIn "tax" (op Divide (op Times (v "base") (dots "rates" ["tax"])) (num "100")),
          afterBlank
            (Bare
              (If
                (op LessThan (dots "rates" ["threshold"]) (v "base"))
                {
                  statements = [
                    plain
                      (Bare
                        (op Minus (op Plus (v "base") (v "tax")) (call "discount" [v "order", v "rates"]))
                        (Some { text = "-- loyal" }))
                  ]
                }
                (expr (op Plus (v "base") (v "tax"))))
              None)
        ]),
      afterBlank
        (Value "names" (expr (list (["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"].map str))))
    ],
    formatted = """
      -- Totals for one order.
      fn total(order, rates) =
        let base = sum(order.items.map(price))
        let tax = base * rates.tax / 100

        if rates.threshold < base then base + tax - discount(order, rates) -- loyal
        else base + tax

      let names = ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta",
        "theta"]
      """
  }

test "mixed: the plan's example" := order.printed == order.formatted

--| Mixed: nesting at width 30, an `if` in a block, a list in a call.
def route: Golden :=
  {
    width = 30,
    source = """
      fn route(map, start) =
        let path = search(map, start, [north, south, east, west])
        if empty(path) then fail("no route from here") else path
      """,
    tree = sprig [
      fn "route"
        ["map", "start"]
        (block [
          letIn "path" (call "search" [v "map", v "start", list [v "north", v "south", v "east", v "west"]]),
          bare (If (call "empty" [v "path"]) (expr (call "fail" [str "no route from here"])) (expr (v "path")))
        ])
    ],
    formatted = """
      fn route(map, start) =
        let path =
          search(
            map,
            start,
            [north, south, east,
              west]
          )
        if empty(path) then
          fail("no route from here")
        else path
      """
  }

test "mixed: nesting in a narrow width" := route.printed == route.formatted

test "P8: a trailing comment on a list's last item puts the ] below" :=
  let tree := sprig [
    value "pair" (ListLiteral [item (num "1"), { comments = [], value = num "2", trailing = Some { text = "-- two" } }])
  ]
  (tree.print 40).text == "let pair = [1, 2 -- two\n]\n"

test "a tree's dump shows its structure" :=
  headers.tree.dump
    == "(fn add (a b) (body (bare (+ (var a) (var b)))))\n(fn distance (fromRow fromColumn toRow toColumn) (body (bare (+ (call (var abs) (item (- (var fromRow) (var toRow)))) (call (var abs) (item (- (var fromColumn) (var toColumn))))))))\n"

--| The printer writes indentation only before text, so no line it prints
--| ends with a space, at any width.
test "no printed line ends with a space" := goldens.all (golden =>
  List.range 1 13 |> .all (step => (golden.tree.print (step * 8)).text.lines.all (line => not (line.endsWith " "))))
