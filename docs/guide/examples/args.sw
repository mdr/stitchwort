-- Chapter 11: a command line with `Args`, and its tests.
--
--   $ stitchwort run args.sw -- --shout --times 2 Ada Grace

import Std (Args, Fail, IO, List, Nat, Text)
import Std.Args.Error (BadValue, Missing)
import Std.Args.Outcome (Help, Run, Wrong)

-- begin spec
type Options = { shout: Bool, times: Nat, names: List Text }

def program: Args.Program := { name = "greet", about = "Greets each person." }

def options: Args.Spec Options :=
  Args.Spec.start ((shout: Bool) (times: Nat) (names: List Text) => ({ shout, times, names }: Options))
    |> .and (Args.flag "shout" (help := "Greet with three exclamation marks."))
    |> .and (Args.option "times" (default := 1) (help := "How often to greet each person."))
    |> .and (Args.arguments "NAME" (atLeast := 1) (help := "Who to greet."))
-- end spec

-- begin main
def greet (options: Options): {IO} () := options.names.forEach (name =>
  let line := if options.shout then "Hello, ${name}!!!" else "Hello, ${name}."
  List.replicate options.times line |> .forEach IO.print)

def main(): {IO, Fail} () := Args.run program options greet
-- end main

-- begin tests
def parse (arguments: List Text): Args.Outcome Options := Args.parse program options arguments

test "options, in any order, and the defaults" :=
  parse ["Ada", "--times=2", "--shout"] == Run { shout = True, times = 2, names = ["Ada"] }
    && parse ["Ada"] == Run { shout = False, times = 1, names = ["Ada"] }

test "after -- everything is a name" := parse ["--", "--shout"] == Run { shout = False, times = 1, names = ["--shout"] }

test "what is wrong" :=
  parse [] == Wrong (Missing "NAME")
    && parse ["--times", "twice", "Ada"] == Wrong (BadValue "--times" "twice" "a whole number")

test "--help is an outcome, not an effect" := match parse ["--help"] with
  | Help text => text.startsWith "usage: greet [--shout] [--times N] NAME..."
  | _ => False
-- end tests
