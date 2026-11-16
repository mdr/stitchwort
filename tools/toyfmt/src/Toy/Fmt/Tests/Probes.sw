--| Comments in every awkward place (every-comment-placed.md §1.3), at
--| width 40: each probe's source, the tree it parses to (as its dump, which
--| says which token holds each comment), and the formatted text. None is
--| left as written; some layouts are odd, as D3619 accepts.

namespace Toy.Fmt.Tests
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (List, Option, Result, Text)

type Probe = { name: Text, source: Text, dump: Text, formatted: Text }

def probeWidth: Nat := 40

def Probe.formats (probe: Probe) (text: Text): Option Text := format text probeWidth |> .toOption

def probes: List Probe :=
  [
    { name = "a trailing comment after =", source = """
      fn odd(x) = -- after =
        x % 2
      """, dump = "(fn odd (x){ after -- after = } (body (bare (% (var x) (number 2)))))\n", formatted = """
        fn odd(x) = -- after =
          x % 2
        """ },
    {
      name = "trailing comments after then and else",
      source = """
        fn f(x) =
          if x then -- after then
            1
          else -- after else
            2
        """,
      dump = "(fn f (x) (body (bare (if (var x){ after -- after then } (body (bare (number 1))){ after -- after else } (body (bare (number 2)))))))\n",
      formatted = """
        fn f(x) =
          if x then -- after then
            1
          else -- after else
            2
        """
    },
    {
      name = "a trailing comment after [",
      source = """
        let xs = [ -- after [
          1, 2]
        """,
      dump = "(let xs (body (bare (list{ after -- after [ } (item (number 1)) (item (number 2))))))\n",
      formatted = """
        let xs = [ -- after [
          1, 2]
        """
    },
    {
      name = "a trailing comment after a call's (",
      source = """
        let y = f( -- after (
          1, 2)
        """,
      dump = "(let y (body (bare (call (var f){ after -- after ( } (item (number 1)) (item (number 2))))))\n",
      formatted = """
        let y =
          f( -- after (
            1,
            2
          )
        """
    },
    { name = "a trailing comment after an operator", source = """
      let y = a + -- after +
        b
      """, dump = "(let y (body (bare (+{ after -- after + } (var a) (var b)))))\n", formatted = """
        let y =
          a
            + -- after +
              b
        """ },
    {
      name = "a trailing comment after the callee",
      source = """
        let y = f -- after the callee
          (1)
        """,
      dump = "(let y (body (bare (call (var f{ after -- after the callee }) (item (number 1))))))\n",
      formatted = """
        let y =
          f -- after the callee
            (
            1
          )
        """
    },
    { name = "a trailing comment after a header's (", source = """
      fn f( -- inside a header
        x) = x
      """, dump = "(fn f { after -- inside a header }(x) (body (bare (var x))))\n", formatted = """
        fn f( -- inside a header
            x
        ) = x
        """ },
    { name = "a trailing comment after a header's )", source = """
      fn f(x) -- after the header
        = x
      """, dump = "(fn f (x){ after -- after the header } (body (bare (var x))))\n", formatted = """
        fn f(
            x
        ) -- after the header
          = x
        """ },
    {
      name = "an own-line comment before ]",
      source = """
        let xs = [1,
          2
          -- before ]
          ]
        """,
      dump = "(let xs (body (bare (list (item (number 1)) (item (number 2)){ above -- before ] }))))\n",
      formatted = """
        let xs = [1, 2
          -- before ]
        ]
        """
    },
    {
      name = "a trailing comment after a let's =",
      source = """
        fn f(x) =
          let y = -- after let =
            x
          y
        """,
      dump = "(fn f (x) (body (let y{ after -- after let = } (body (bare (var x)))) (bare (var y))))\n",
      formatted = """
        fn f(x) =
          let y = -- after let =
            x
          y
        """
    },
    { name = "an own-line comment before an operator", source = """
      let y = a
        -- own-line before +
        + b
      """, dump = "(let y (body (bare (+{ above -- own-line before + } (var a) (var b)))))\n", formatted = """
        let y =
          a
            -- own-line before +
            + b
        """ },
    {
      name = "own-line comments before then and else",
      source = """
        let y = if a
          -- own-line before then
          then b
          -- own-line before else
          else c
        """,
      dump = "(let y (body (bare (if (var a){ above -- own-line before then } (body (bare (var b))){ above -- own-line before else } (body (bare (var c)))))))\n",
      formatted = """
        let y =
          if a
            -- own-line before then
            then b
          -- own-line before else
          else c
        """
    },
    { name = "a trailing comment before )", source = """
      let y = (a -- before )
        )
      """, dump = "(let y (body (bare (bracketed (var a{ after -- before ) })))))\n", formatted = """
        let y =
          (a -- before )
          )
        """ },
    { name = "a trailing comment after .", source = """
      let y = order. -- after .
        items
      """, dump = "(let y (body (bare (field (var order){ after -- after . } items))))\n", formatted = """
        let y =
          order. -- after .
            items
        """ },
    { name = "a trailing comment after a unary -", source = """
      let y = - -- after unary minus
        x
      """, dump = "(let y (body (bare (negate{ after -- after unary minus } (var x)))))\n", formatted = """
        let y =
          - -- after unary minus
            x
        """ },
    {
      name = "a trailing comment after a comma",
      source = """
        let y = f(1, -- after a comma
          2)
        """,
      dump = "(let y (body (bare (call (var f) (item (number 1){ after -- after a comma }) (item (number 2))))))\n",
      formatted = """
        let y =
          f(
            1, -- after a comma
            2
          )
        """
    },
    {
      name = "an own-line comment before a call's (",
      source = """
        let y = f
          -- own-line between callee and (
          (1)
        """,
      dump = "(let y (body (bare (call (var f){ above -- own-line between callee and ( } (item (number 1))))))\n",
      formatted = """
        let y =
          f
            -- own-line between callee and (
            (
            1
          )
        """
    },
    { name = "an own-line comment above a body", source = """
      let y =
        -- above the body
        x + 1
      """, dump = "(let y (body (note -- above the body) (bare (+ (var x) (number 1)))))\n", formatted = """
        let y =
          -- above the body
          x + 1
        """ },
    { name = "a trailing comment after fn", source = """
      fn -- after fn
        f(x) = x
      """, dump = "(fn{ after -- after fn } f (x) (body (bare (var x))))\n", formatted = """
        fn -- after fn
          f(
            x
        ) = x
        """ },
    {
      name = "an if's trailing comment before )",
      source = """
        let y = (if a then b else c -- k
        )
        """,
      dump = "(let y (body (bare (bracketed (if (var a) (body (bare (var b))) (body (bare (var c{ after -- k }))))))))\n",
      formatted = """
        let y =
          (if a then b else c -- k
          )
        """
    }
  ]

test "each probe parses to its tree" :=
  probes.all (probe => (parse probe.source |> .map (file => file.dump)) == Ok probe.dump)

test "each probe formats to its formatted text" :=
  probes.all (probe => probe.formats probe.source == Some probe.formatted)

test "each probe's formatted text formats to itself" :=
  probes.all (probe => probe.formats probe.formatted == Some probe.formatted)

test "each probe survives 50 disturbances" :=
  probes.all (probe => seeds.all (seed => probe.formats (disturb probe.formatted seed) == Some probe.formatted))
