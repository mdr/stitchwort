import Args.Tests.Colour (Red, Green, Blue)
import Args.Kind (Flag, Single, Many, Positionals)
import Args.Error (NeedsValue, BadValue, TakesNoValue, Repeated, Missing, Unexpected)
import Args.Outcome (Run, Help, Wrong)
import Args.Scan (Scanned, HelpAsked)

--| `Args`: a program's command line, described once and parsed as a pure
--| function of a list of text, so a program's command line is tested with
--| plain `test`s. A spec is built from combinators, one per option, joined
--| with `.and`; from it come the parser, the usage line, `--help`, and the
--| error messages.
--|
--|   type Options = { check: Bool, width: Nat, paths: List Path }
--|
--|   def options: Args.Spec Options :=
--|     Args.Spec.start ((check: Bool) (width: Nat) (paths: List Path) => ({ check, width, paths }: Options))
--|       |> .and (Args.flag "check" (help := "Write nothing; list the files that would change"))
--|       |> .and (Args.option "width" (default := 80) (metavar := "N") (help := "The widest a line may be."))
--|       |> .and (Args.arguments "PATH" (atLeast := 1) (help := "Files or folders to format."))
--|
--|   def program: Args.Program := { name = "toyfmt", about = "Formats Sprig files in place." }
--|
--|   def main (): {IO, Fail} ExitStatus := Args.run program options (options => …)
--|
--| A bad command line exits with status 2 (`Args.misuse`), `--help` with 0;
--| a body that wants other statuses uses `Args.runStatus`.
--|
--| The lambda's parameters must be in the order of the `.and`s, and their
--| types must be written: an unannotated lambda there isn't accepted yet
--| (SW-3379).
--|
--| The command line it accepts: `--check` (a flag); `--width 80` and
--| `--width=80` (an option with a value; the value may start with `-`);
--| `--keep A --keep B` (a repeated option, `Args.many`); options and
--| positional arguments in any order. `--` ends the options: everything after
--| it is a positional argument, verbatim. A lone `-` is a positional
--| argument. `--help` and `-h` ask for the help. There are no short options
--| and no abbreviations. An option that doesn't repeat is an error the
--| second time, and a flag takes no `=value`: nothing is dropped silently.
--| A program has at most one positional spec (`Args.arguments`); `--help` and
--| `-h` are the library's, so a spec can't use those names
--| (`Args.problems` lists such mistakes).

--| The kinds of command-line item a spec describes: a flag, an option with
--| one value (`required` when the command line has to give it), a repeatable
--| option, or the positional arguments (at least `atLeast` of them).
type Args.Kind =
  | Flag
  | Single (required: Bool)
  | Many
  | Positionals (atLeast: Nat)

--| What help and usage say about one item. `long` is the option's name
--| without its `--`, or the positional's name; `metavar` stands for a value
--| (`N`); `default` is the shown default, if the option has one.
type Args.Info = {
  long: Text,
  kind: Args.Kind,
  metavar: Text,
  help: Text,
  default: Option Text
}

--| What was found on a command line: the flags named, each option value in
--| order with its option's name (without `--`), and the positional arguments.
type Args.Found = {
  flags: List Text,
  values: List (Pair Text Text),
  positionals: List Text
}

--| What is wrong with a command line. The names are as they are written on
--| it, with their dashes.
type Args.Error =
  | Unknown (name: Text) (suggestion: Option Text)
  | NeedsValue (name: Text) (metavar: Text)
  | BadValue (name: Text) (value: Text) (expected: Text)
  | TakesNoValue (name: Text) (value: Text)
  | Repeated (name: Text)
  | Missing (name: Text)
  | Unexpected (argument: Text)

--| What a command line asks for: to run with these options, to print this
--| help, or it is wrong.
type Args.Outcome (a: Type) =
  | Run (options: a)
  | Help (text: Text)
  | Wrong (error: Args.Error)

--| Who is running: its `name` (for usage lines and error messages) and what
--| it `about` does (the help's description; may be empty).
type Args.Program = { name: Text, about: Text := "" }

--| A description of a command line that reads an `a`: the items it takes
--| (for help and for the parser) and how to read the value from what the
--| parser found. Built with `Args.Spec.start` and `.and`.
type Args.Spec (a: Type) = {
  items: List Args.Info,
  read: Args.Found → Result a Args.Error
}

--| How a type is read from one piece of a command line: `read` gives the
--| value, or says what was expected (`a whole number`); `show` writes a
--| default; `metavar` is what help calls the value (`N`).
interface Args.Value (a: Type) = {
  read: Text → Result a Text,
  show: a → Text,
  metavar: Text
}

instance Text.instArgsValue: Args.Value Text := { read = text => Ok text, show = text => text, metavar = "TEXT" }

instance Nat.instArgsValue: Args.Value Nat := {
  read = text =>
    match text.toNat with
      | Some number => Ok number
      | None => Err "a whole number",
  show = number => "${number}",
  metavar = "N"
}

instance Int.instArgsValue: Args.Value Int := {
  read = text =>
    match text.toInt with
      | Some number => Ok number
      | None => Err "an integer",
  show = number => "${number}",
  metavar = "N"
}

instance Path.instArgsValue: Args.Value Path :=
  { read = text => Ok text.toPath, show = path => path.show, metavar = "PATH" }

--| The `Args.Value` of a type with a finite list of values, read as the
--| text each shows as: `instance Colour.instArgsValue: Args.Value Colour :=
--| Args.choice`. The error lists the choices.
def Args.choice [auto finite: Finite a] [auto show: Show a]: Args.Value a :=
  let choices: List a := Finite.all
  {
    read = text =>
      match choices.find (choice => Show.toText choice == text) with
        | Some choice => Ok choice
        | None => Err "one of ${choices.map (choice => Show.toText choice) |> .joinWith ", "}",
    show = choice => Show.toText choice,
    metavar = "CHOICE"
  }

--| The name help gives a value: `metavar` if one was given, else the type's own.
def Args.metavarOr [auto value: Args.Value a] (metavar: Text): Text :=
  if metavar.isEmpty then Args.Value.metavar [a := a] else metavar

--| The values given for the option `name`, in order.
def Args.valuesOf (found: Args.Found) (name: Text): List Text :=
  found.values.filterMap (entry => if entry.fst == name then Some entry.snd else None)

--| One piece of a command line as an `a`, or the error naming place it was
--| found (`--width`, or a positional's name).
def Args.readPiece [auto value: Args.Value a] (place text: Text): Result a Args.Error := match value.read text with
  | Ok result => Ok result
  | Err expected => Err (BadValue place text expected)

--| Every piece as an `a`, or the first error.
def Args.readEach [auto value: Args.Value a] (place: Text): (texts: List Text) → Result (List a) Args.Error
  | [] => Ok []
  | [text, ..rest] =>
    match (Args.readPiece [a := a] place text, Args.readEach [a := a] place rest) with
      | (Ok first, Ok others) => Ok [first, ..others]
      | (Err error, _) => Err error
      | (_, Err error) => Err error

--| A flag: `True` if it is on the command line. `help` says what it does.
def Args.flag (name: Text) (help: Text := ""): Args.Spec Bool := {
  items = [{ long = name, kind = Flag, metavar = "", help, default = None }],
  read = found => Ok (found.flags.contains name)
}

--| An option with one value, `--name VALUE` or `--name=VALUE`, that is
--| `default` when it isn't given. `metavar` stands for the value in help
--| (the type's own if omitted).
def Args.option [auto value: Args.Value a] (name: Text) (default: a) (metavar: Text := "") (help: Text := ""):
    Args.Spec a :=
  {
    items = [
      {
        long = name,
        kind = Single False,
        metavar = Args.metavarOr [a := a] metavar,
        help,
        default = Some (value.show default)
      }
    ],
    read = found =>
      match Args.valuesOf found name with
        | [] => Ok default
        | [text, .._] => Args.readPiece [a := a] "--${name}" text
  }

--| An option with one value that must be given: without it, `Missing`.
def Args.required [auto value: Args.Value a] (name: Text) (metavar: Text := "") (help: Text := ""): Args.Spec a := {
  items = [{ long = name, kind = Single True, metavar = Args.metavarOr [a := a] metavar, help, default = None }],
  read = found =>
    match Args.valuesOf found name with
      | [] => Err (Missing "--${name}")
      | [text, .._] => Args.readPiece [a := a] "--${name}" text
}

--| An option with one value that may be left out: `None` then.
def Args.optional [auto value: Args.Value a] (name: Text) (metavar: Text := "") (help: Text := ""):
    Args.Spec (Option a) :=
  {
    items = [{ long = name, kind = Single False, metavar = Args.metavarOr [a := a] metavar, help, default = None }],
    read = found =>
      match Args.valuesOf found name with
        | [] => Ok None
        | [text, .._] =>
          match Args.readPiece [a := a] "--${name}" text with
            | Ok result => Ok (Some result)
            | Err error => Err error
  }

--| An option that may be given any number of times, `--name A --name B`:
--| all its values in order.
def Args.many [auto value: Args.Value a] (name: Text) (metavar: Text := "") (help: Text := ""): Args.Spec (List a) := {
  items = [{ long = name, kind = Many, metavar = Args.metavarOr [a := a] metavar, help, default = None }],
  read = found => Args.readEach [a := a] "--${name}" (Args.valuesOf found name)
}

--| The positional arguments, at least `atLeast` of them (`Missing` below
--| that). `metavar` is what the usage line calls them.
def Args.arguments [auto value: Args.Value a] (metavar: Text) (atLeast: Nat := 0) (help: Text := ""):
    Args.Spec (List a) :=
  {
    items = [{ long = metavar, kind = Positionals atLeast, metavar, help, default = None }],
    read = found =>
      if found.positionals.length < atLeast then Err (Missing metavar)
      else Args.readEach [a := a] metavar found.positionals
  }

--| A spec that finds `value` and takes no part of the command line; the start
--| of a chain of `.and`s, with a function from the options' values to the
--| result: `Args.Spec.start ((flag: Bool) (n: Nat) => …) |> .and … |> .and …`.
def Args.Spec.start (value: a): Args.Spec a := { items = [], read = found => Ok value }

--| The spec of a function's result when its first argument is read by
--| `functions` and the next by `argument`; the first error is the one given.
def Args.Spec.and (functions: Args.Spec (a → b)) (argument: Args.Spec a): Args.Spec b := {
  items = functions.items ++ argument.items,
  read = found =>
    match (functions.read found, argument.read found) with
      | (Ok function, Ok result) => Ok (function result)
      | (Err error, _) => Err error
      | (_, Err error) => Err error
}

--| Whether the item is an option, as opposed to the positional arguments.
def Args.Info.isOption (info: Args.Info): Bool := match info.kind with
  | Positionals _ => False
  | _ => True

--| The names a spec uses twice, and the other mistakes in it that a command
--| line can't show: more than one positional spec, the library's own `help`
--| and `h`. A program's tests assert this is empty.
def Args.problems (spec: Args.Spec a): List Text :=
  let names := (spec.items.filter .isOption).map .long
  let twice := names.filter (name => (names.filter (other => other == name)).length > 1) |> .dedup
  let positionals := (spec.items.filter (info => !info.isOption)).length
  twice.map (name => "the option --${name} is used twice")
    ++ (if positionals > 1 then ["more than one positional spec"] else [])
    ++ (names.filter (name => name == "help" || name == "h")).map (name => "--${name} is the library's own")

--| Splits `--name=value` (without its dashes) at the first `=`.
def Args.splitEquals (body: Text): Pair Text (Option Text) :=
  let (name, rest) := body.toList.span (char => char != '=')
  match rest with
    | [] => MkPair (Text.fromList name) None
    | [_, ..value] => MkPair (Text.fromList name) (Some (Text.fromList value))

--| The option or flag `name`, if the spec has one.
def Args.findOption (items: List Args.Info) (name: Text): Option Args.Info :=
  items.find (info => info.isOption && info.long == name)

--| The option a mistyped `name` is a start of, when that is one option.
def Args.suggest (items: List Args.Info) (name: Text): Option Text :=
  match items.filter (info => info.isOption && !name.isEmpty && info.long.startsWith name) with
    | [only] => Some "--${only.long}"
    | _ => None

--| What reading the command line's words found: everything, or a request
--| for help.
type Args.Scan = | Scanned (found: Args.Found) | HelpAsked

--| Records an option's value or flag, unless it is a second one for something that doesn't repeat.
def Args.record (items: List Args.Info) (found: Args.Found) (info: Args.Info) (value: Option Text):
    Result Args.Found Args.Error :=
  let name := "--${info.long}"
  let seen := found.flags.contains info.long || found.values.any (entry => entry.fst == info.long)
  match info.kind, value with
    | Flag, Some given => Err (TakesNoValue name given)
    | Flag, None => if seen then Err (Repeated name) else Ok { found | flags = found.flags ++ [info.long] }
    | Many, Some given => Ok { found | values = found.values ++ [(info.long, given)] }
    | _, Some given =>
      if seen then Err (Repeated name) else Ok { found | values = found.values ++ [(info.long, given)] }
    | _, None => Err (NeedsValue name info.metavar)

--| Reads the words of a command line against the spec's items.
def Args.scan (items: List Args.Info) (found: Args.Found): (arguments: List Text) → Result Args.Scan Args.Error
  | [] => Ok (Scanned found)
  | ["--", ..rest] => Ok (Scanned { found | positionals = found.positionals ++ rest })
  | ["--help", .._] => Ok HelpAsked
  | ["-h", .._] => Ok HelpAsked
  | [argument, ..rest] =>
    match argument.stripPrefix "--" with
      | Some body =>
        let (name, inline) := Args.splitEquals body
        match Args.findOption items name with
          | None => Err (Args.Error.Unknown "--${name}" (Args.suggest items name))
          | Some info =>
            match info.kind, inline, rest with
              | Flag, _, _ =>
                match Args.record items found info inline with
                  | Ok next => Args.scan items next rest
                  | Err error => Err error
              | _, Some _, _ =>
                match Args.record items found info inline with
                  | Ok next => Args.scan items next rest
                  | Err error => Err error
              | _, None, [] => Err (NeedsValue "--${name}" info.metavar)
              | _, None, [given, ..more] =>
                match Args.record items found info (Some given) with
                  | Ok next => Args.scan items next more
                  | Err error => Err error
      | None =>
        if argument != "-" && argument.startsWith "-" then Err (Args.Error.Unknown argument None)
        else Args.scan items { found | positionals = found.positionals ++ [argument] } rest

--| What the item looks like in a usage line: `[--check]`, `[--width N]`,
--| `--name N`, `[--keep X]...`, `PATH...`, `[PATH...]`.
def Args.Info.usage (info: Args.Info): Text := match info.kind with
  | Flag => "[--${info.long}]"
  | Single True => "--${info.long} ${info.metavar}"
  | Single False => "[--${info.long} ${info.metavar}]"
  | Many => "[--${info.long} ${info.metavar}]..."
  | Positionals atLeast => if atLeast == 0 then "[${info.long}...]" else "${info.long}..."

--| What the item looks like at the start of its help line: `--check`,
--| `--width N`, `PATH...`.
def Args.Info.syntax (info: Args.Info): Text := match info.kind with
  | Flag => "--${info.long}"
  | Positionals _ => "${info.long}..."
  | _ => "--${info.long} ${info.metavar}"

--| The usage line: `usage: toyfmt [--check] [--width N] PATH...`. The
--| options come first, in the order the spec lists them, then the positionals.
def Args.usage (program: Args.Program) (spec: Args.Spec a): Text :=
  let items := (spec.items.filter .isOption) ++ (spec.items.filter (info => !info.isOption))
  ([program.name] ++ items.map .usage).joinWith " "

--| What an item says about itself in help: its help, then its default.
def Args.Info.description (info: Args.Info): Text := match info.default with
  | Some shown => "${info.help} (default: ${shown})".trim
  | None => info.help

--| Breaks `words` into lines of at most `width` characters (a longer word
--| gets a line to itself), joining the pieces of the line being built with spaces.
def Args.wrapStep (width: Nat) (state: Pair (List Text) Text) (word: Text): Pair (List Text) Text :=
  if state.snd.isEmpty then MkPair state.fst word
  else if state.snd.length + 1 + word.length <= width then MkPair state.fst "${state.snd} ${word}"
  else MkPair (state.fst ++ [state.snd]) word

--| The lines `text` wraps to, at most `width` characters each.
def Args.wrap (width: Nat) (text: Text): List Text :=
  let state := text.words.foldLeft (MkPair [] "") (Args.wrapStep width)
  if state.snd.isEmpty then state.fst else state.fst ++ [state.snd]

--| One entry of the help: `left` in a column `column` wide, then its
--| `description`, wrapped so that no line is over 80 characters.
def Args.helpRow (column: Nat) (left description: Text): List Text :=
  let margin := column + 4
  let room := if margin + 20 < 80 then 80 - margin else 20
  match Args.wrap room description with
    | [] => ["  ${left}"]
    | [first, ..rest] => ["  ${left.padRight column ' '}  ${first}", ..rest.map (line => "${" ".repeat margin}${line}")]

--| The width of the help's left column: the longest syntax among the
--| positionals, the options and `-h, --help`.
def Args.helpColumn (spec: Args.Spec a): Nat :=
  let positionals := spec.items.filter (info => !info.isOption)
  let options := spec.items.filter .isOption
  let lefts := (positionals ++ options).map .syntax ++ ["-h, --help"]
  (lefts.maximumOf .length).getOrElse 0

--| The lines of the help, before they are joined: usage, what the program
--| does, then each positional and each option, ending with `-h, --help`.
def Args.helpLines (program: Args.Program) (spec: Args.Spec a): List Text :=
  let positionals := spec.items.filter (info => !info.isOption)
  let options := spec.items.filter .isOption
  let column := Args.helpColumn spec
  let rows := (items: List Args.Info) => items.flatMap (info => Args.helpRow column info.syntax info.description)
  ["usage: ${Args.usage program spec}"]
    ++ (if program.about.isEmpty then [] else [program.about])
    ++ [""]
    ++ (if positionals.isEmpty then [] else ["arguments:"] ++ rows positionals)
    ++ ["options:"]
    ++ rows options
    ++ Args.helpRow column "-h, --help" "Show this help."

--| The help: usage, what the program does, then each positional and each
--| option with its help and default. `-h, --help` is always listed.
def Args.help (program: Args.Program) (spec: Args.Spec a): Text := (Args.helpLines program spec).joinWith "\n"

--| The start of an option's help line names it: the syntax contains `--` and the
--| option's name.
theorem Args.syntaxContainsLong ∀ (info: Args.Info)
    (option: info.isOption = True):
    Text.contains info.syntax "--${info.long}" = True :=
  match info with
    | { long = long, kind = kind, metavar = metavar, help = help, default = default } =>
      match kind with
        | Flag => Text.containsSelf "--${long}"
        | Single required =>
          Text.containsAppendLeft "--${long}" " ${metavar}" "--${long}" (Text.containsSelf "--${long}")
        | Many => Text.containsAppendLeft "--${long}" " ${metavar}" "--${long}" (Text.containsSelf "--${long}")
        | Positionals atLeast => (Bool.falseNotTrue option).impossible

--| Some line of a help entry contains what its left text contains: the entry's
--| first line starts with that text, padded to the column.
theorem Args.helpRowContains ∀ (column: Nat) (left description needle: Text)
    (h: Text.contains left needle = True):
    ∃ (line: Text) => line ∈ Args.helpRow column left description ∧ Text.contains line needle = True :=
  match Args.wrap (if column + 4 + 20 < 80 then 80 - (column + 4) else 20) description with
    | [] => Witness "  ${left}" (Both (Inl byComputing) (Text.containsAppendRight "  " left needle h))
    | [first, ..rest] =>
      Witness
        "  ${left.padRight column ' '}  ${first}"
        (Both
          (Inl byComputing)
          (Text.containsAppendRight "  "
            (Text.append (left.padRight column ' ') (Text.append "  " first))
            needle
            (Text.containsAppendLeft
              (left.padRight column ' ')
              (Text.append "  " first)
              needle
              (Text.padRightContains left column ' ' needle h))))

--| The help lists every option: for each option of the spec, the help text
--| contains `--` and its name.
--|
--| Proof idea: the option's help entry ([`Args.helpRowContains`]) has a line
--| that contains its syntax, which contains `--` and the name
--| ([`Args.syntaxContainsLong`]). That entry is among the rows of the options,
--| so the line is one of the lines the help joins, and a joined text contains
--| what one of its parts contains ([`Text.containsJoinWithPart`]).
theorem Args.helpListsOption ∀ (program: Args.Program) (spec: Args.Spec a) (info: Args.Info)
    (declared: info ∈ spec.items)
    (option: info.isOption = True):
    Text.contains (Args.help program spec) "--${info.long}" = True :=
  let column := Args.helpColumn spec
  let lines := Args.helpLines program spec
  match Args.helpRowContains column info.syntax info.description
    "--${info.long}"
    (Args.syntaxContainsLong info option) with
    | Witness line (Both entry holds) =>
      Text.containsJoinWithPart lines "\n" line
        "--${info.long}"
        (Inr
          (List.memAppendRight line _ _
            (Inr
              (List.memAppendRight line _ _
                (Inr
                  (List.memAppendLeft line _ _
                    (List.memFlatMapIntro
                      (item => Args.helpRow column item.syntax item.description)
                      info
                      line _
                      (List.memFilterIntro spec.items .isOption declared option)
                      entry)))))))
        holds

--| The message for a mistake in a command line, without the program's name.
def Args.Error.describe: (error: Args.Error) → Text
  | Args.Error.Unknown name (Some suggestion) => "unknown option ${name} (did you mean ${suggestion}?)"
  | Args.Error.Unknown name None => "unknown option ${name}"
  | NeedsValue name metavar => "${name} needs a value (${metavar})"
  | BadValue name value expected => "${name} wants ${expected}, got '${value}'"
  | TakesNoValue name value => "${name} takes no value, got '${name}=${value}'"
  | Repeated name => "${name} is given twice"
  | Missing name => "missing ${name}"
  | Unexpected argument => "unexpected argument '${argument}'"

--| What a program prints to standard error for a mistake: the message, the
--| usage line, and where to find the help.
def Args.complaint (program: Args.Program) (spec: Args.Spec a) (error: Args.Error): Text :=
  "${program.name}: ${error.describe}\nusage: ${Args.usage program spec}\nRun '${program.name} --help' for more."

--| What the command line `arguments` asks `program` to do: run with its
--| options, print its help (`--help` or `-h` before a `--`), or it is wrong.
--| Pure, so a program's command line is tested on lists of text.
def Args.parse (program: Args.Program) (spec: Args.Spec a) (arguments: List Text): Args.Outcome a :=
  match Args.scan spec.items { flags = [], values = [], positionals = [] } arguments with
    | Err error => Wrong error
    | Ok HelpAsked => Help (Args.help program spec)
    | Ok (Scanned found) =>
      match found.positionals, spec.items.any (info => !info.isOption) with
        | [extra, .._], False => Wrong (Unexpected extra)
        | _, _ =>
          match spec.read found with
            | Ok options => Run options
            | Err error => Wrong error

--| The exit status of a command line that is wrong: 2, the convention for
--| misuse of a command (Bash's builtins, Python's `argparse` and Go's `flag`
--| all use it; docs/proposals/exit-status.md, D3616). It is told apart from 1,
--| which a program's own failure (`Fail`, or `ExitStatus.failure`) uses, so
--| a script can tell "you called it wrongly" from "it ran and failed".
def Args.misuse: ExitStatus := ExitStatus.of 2

--| Runs a program on the command line `arguments`, with a body that
--| decides its own exit status. `--help` prints the help and gives status 0;
--| a mistake prints the complaint (the message, usage and where to find the
--| help) to standard error and gives status 2 (`Args.misuse`); otherwise
--| `body` runs on the options and its status is the program's. A `Fail`
--| left unhandled in `body` is status 1, as in any program.
def Args.runStatusOn (program: Args.Program) (spec: Args.Spec a) (arguments: List Text) (body: a → {IO | e} ExitStatus):
    {IO | e} ExitStatus :=
  match Args.parse program spec arguments with
    | Run options => body options
    | Help text =>
      IO.print text
      ExitStatus.success
    | Wrong error =>
      IO.printError (Args.complaint program spec error)
      Args.misuse

--| `Args.runStatusOn` the program's own command line (`IO.args`):
--| `def main (): {IO} ExitStatus := Args.runStatus program options (options => …)`.
def Args.runStatus (program: Args.Program) (spec: Args.Spec a) (body: a → {IO | e} ExitStatus): {IO | e} ExitStatus :=
  Args.runStatusOn program spec IO.args() body

--| Runs a program on the command line `arguments` whose body returns `()`:
--| as `Args.runStatusOn`, with status 0 when the body finishes (and 1 if it
--| fails).
def Args.runOn (program: Args.Program) (spec: Args.Spec a) (arguments: List Text) (body: a → {IO | e} ()):
    {IO | e} ExitStatus :=
  Args.runStatusOn program spec arguments (options =>
    body options
    ExitStatus.success)

--| `Args.runOn` the program's own command line (`IO.args`):
--| `def main (): {IO, Fail} ExitStatus := Args.run program options (options => …)`.
def Args.run (program: Args.Program) (spec: Args.Spec a) (body: a → {IO | e} ()): {IO | e} ExitStatus :=
  Args.runOn program spec IO.args() body

--| A spec's items are those of the parts it was joined from, in order.
theorem Args.Spec.andItems ∀ (functions: Args.Spec (a → b)) (argument: Args.Spec a):
    (functions.and argument).items = functions.items ++ argument.items :=
  byComputing

--| Everything after `--` reaches the positionals unchanged, in order: a file
--| called `-x` is always reachable.
theorem Args.scanAfterDashes ∀ (items: List Args.Info) (found: Args.Found) (rest: List Text):
    Args.scan items found ["--", ..rest] = Ok (Scanned { found | positionals = found.positionals ++ rest }) :=
  byComputing

-- Tests

type Args.Tests.Colour = | Red | Green | Blue

instance Args.Tests.Colour.instArgsValue: Args.Value Args.Tests.Colour := Args.choice

type Args.Tests.Options = { check: Bool, width: Nat, paths: List Path }

def Args.Tests.program: Args.Program := { name = "toyfmt", about = "Formats Sprig files in place." }

def Args.Tests.options: Args.Spec Args.Tests.Options :=
  Args.Spec.start ((check: Bool) (width: Nat) (paths: List Path) => ({ check, width, paths }: Args.Tests.Options))
    |> .and (Args.flag "check" (help := "Write nothing; list the files that would change, and fail if any would."))
    |> .and (Args.option "width" (default := 80) (metavar := "N") (help := "The widest a line may be."))
    |> .and (Args.arguments "PATH" (atLeast := 1) (help := "Files or folders to format."))

type Args.Tests.Everything = {
  name: Text,
  offset: Int,
  keep: List Text,
  colour: Args.Tests.Colour,
  level: Option Nat,
  files: List Path
}

def Args.Tests.everything: Args.Spec Args.Tests.Everything :=
  Args.Spec.start ((name: Text) (offset: Int) (keep: List Text) (colour: Args.Tests.Colour) (level: Option
      Nat) (files: List Path) =>
    ({ name, offset, keep, colour, level, files }: Args.Tests.Everything))
    |> .and (Args.required "name" (help := "Who to greet"))
    |> .and (Args.option "offset" (default := 0))
    |> .and (Args.many "keep")
    |> .and (Args.option "colour" (default := Green) (help := "How loud"))
    |> .and (Args.optional "level")
    |> .and (Args.arguments "FILE")

def Args.Tests.parse (arguments: List Text): Args.Outcome Args.Tests.Options :=
  Args.parse Args.Tests.program Args.Tests.options arguments

def Args.Tests.parseAll (arguments: List Text): Args.Outcome Args.Tests.Everything :=
  Args.parse Args.Tests.program Args.Tests.everything arguments

def Args.Tests.wrong (arguments: List Text): Option Args.Error := match Args.Tests.parse arguments with
  | Wrong error => Some error
  | _ => None

def Args.Tests.wrongAll (arguments: List Text): Option Args.Error := match Args.Tests.parseAll arguments with
  | Wrong error => Some error
  | _ => None

test "Args: flags, an option, positionals" :=
  Args.Tests.parse ["--check", "--width", "40", "a", "b/c"]
    == Run { check = True, width = 40, paths = ["a".toPath, "b/c".toPath] }

test "Args: the defaults" := Args.Tests.parse ["a"] == Run { check = False, width = 80, paths = ["a".toPath] }

test "Args: --name=value, and options after positionals" :=
  Args.Tests.parse ["a", "--width=100", "b", "--check"]
    == Run { check = True, width = 100, paths = ["a".toPath, "b".toPath] }

test "Args: -- ends the options" :=
  Args.Tests.parse ["--width", "5", "--", "-x", "--check", "--help"]
    == Run { check = False, width = 5, paths = ["-x".toPath, "--check".toPath, "--help".toPath] }

test "Args: a lone - is a positional" :=
  Args.Tests.parse ["-", "--check"] == Run { check = True, width = 80, paths = ["-".toPath] }

test "Args: the value of an option may start with a dash" :=
  Args.Tests.parseAll ["--name", "-n", "--offset", "-5"]
    == Run { name = "-n", offset = -5, keep = [], colour = Green, level = None, files = [] }

test "Args: every kind of option" :=
  Args.Tests.parseAll ["--name=x", "--keep", "a", "--colour", "Blue", "--keep=b", "--level", "3", "f", "g"]
    == Run {
      name = "x",
      offset = 0,
      keep = ["a", "b"],
      colour = Blue,
      level = Some 3,
      files = ["f".toPath, "g".toPath]
    }

test "Args: an empty value after = is a value" :=
  Args.Tests.parseAll ["--name="] == Run { name = "", offset = 0, keep = [], colour = Green, level = None, files = [] }

test "Args: --help and -h ask for the help, wherever they are" :=
  Args.Tests.parse ["--help"] == Help (Args.help Args.Tests.program Args.Tests.options)
    && Args.Tests.parse ["a", "-h"] == Help (Args.help Args.Tests.program Args.Tests.options)
    && Args.Tests.parse [] == Wrong (Missing "PATH")

test "Args: help comes before a mistake that follows it, and a mistake before help that follows it" :=
  Args.Tests.parse ["--help", "--bogus"] == Help (Args.help Args.Tests.program Args.Tests.options)
    && Args.Tests.wrong ["--bogus", "--help"] == Some (Args.Error.Unknown "--bogus" None)

test "Args: an unknown option, with a suggestion when it starts one" :=
  Args.Tests.wrong ["--widht", "a"] == Some (Args.Error.Unknown "--widht" None)
    && Args.Tests.wrong ["--wid", "a"] == Some (Args.Error.Unknown "--wid" (Some "--width"))
    && Args.Tests.wrong ["--wid=3", "a"] == Some (Args.Error.Unknown "--wid" (Some "--width"))
    && Args.Tests.wrong ["-x", "a"] == Some (Args.Error.Unknown "-x" None)
    && Args.Tests.wrong ["--", "--x"] == None

test "Args: an option without its value" :=
  Args.Tests.wrong ["a", "--width"] == Some (NeedsValue "--width" "N")
    && Args.Tests.wrongAll ["--name"] == Some (NeedsValue "--name" "TEXT")
    && Args.Tests.wrongAll ["--keep"] == Some (NeedsValue "--keep" "TEXT")

test "Args: a value of the wrong kind" :=
  Args.Tests.wrong ["--width", "x", "a"] == Some (BadValue "--width" "x" "a whole number")
    && Args.Tests.wrong ["--width=-3", "a"] == Some (BadValue "--width" "-3" "a whole number")
    && Args.Tests.wrongAll ["--name", "n", "--offset", "x"] == Some (BadValue "--offset" "x" "an integer")
    && Args.Tests.wrongAll ["--name", "n", "--colour", "Pink"]
      == Some (BadValue "--colour" "Pink" "one of Red, Green, Blue")
    && Args.Tests.wrongAll ["--name", "n", "--keep", "a", "--level", "x"]
      == Some (BadValue "--level" "x" "a whole number")

test "Args: a flag takes no value" := Args.Tests.wrong ["--check=yes", "a"] == Some (TakesNoValue "--check" "yes")

test "Args: nothing is given twice" :=
  Args.Tests.wrong ["--width", "1", "--width", "2", "a"] == Some (Repeated "--width")
    && Args.Tests.wrong ["--width=1", "--width", "2", "a"] == Some (Repeated "--width")
    && Args.Tests.wrong ["--check", "--check", "a"] == Some (Repeated "--check")
    && Args.Tests.wrongAll ["--name", "a", "--name", "b"] == Some (Repeated "--name")
    && Args.Tests.parseAll ["--name", "a", "--keep", "x", "--keep", "x"]
      == Run { name = "a", offset = 0, keep = ["x", "x"], colour = Green, level = None, files = [] }

test "Args: what is missing" :=
  Args.Tests.wrong ["--check"] == Some (Missing "PATH") && Args.Tests.wrongAll [] == Some (Missing "--name")

test "Args: an argument no spec takes" :=
  Args.Tests.wrongAll ["--name", "n", "--", "a"] == None
    && Args.parse Args.Tests.program (Args.flag "x") ["b.sw"] == Wrong (Unexpected "b.sw")
    && Args.parse Args.Tests.program (Args.flag "x") ["--x"] == Run True

test "Args: the first mistake wins" :=
  Args.Tests.wrong ["--bogus", "--width", "x"] == Some (Args.Error.Unknown "--bogus" None)
    && Args.Tests.wrong ["--width", "x"] == Some (BadValue "--width" "x" "a whole number")

test "Args: the messages" :=
  (Args.Error.Unknown "--widht" (Some "--width")).describe == "unknown option --widht (did you mean --width?)"
    && (Args.Error.Unknown "--bogus" None).describe == "unknown option --bogus"
    && (NeedsValue "--width" "N").describe == "--width needs a value (N)"
    && (BadValue "--width" "x" "a whole number").describe == "--width wants a whole number, got 'x'"
    && (TakesNoValue "--check" "yes").describe == "--check takes no value, got '--check=yes'"
    && (Repeated "--width").describe == "--width is given twice"
    && (Missing "PATH").describe == "missing PATH"
    && (Missing "--name").describe == "missing --name"
    && (Unexpected "b.sw").describe == "unexpected argument 'b.sw'"

test "Args: a complaint is the message, the usage line and where the help is" :=
  Args.complaint Args.Tests.program Args.Tests.options (BadValue "--width" "x" "a whole number")
    == "toyfmt: --width wants a whole number, got 'x'\nusage: toyfmt [--check] [--width N] PATH...\nRun 'toyfmt --help' for more."

test "Args: the usage line" :=
  Args.usage Args.Tests.program Args.Tests.options == "toyfmt [--check] [--width N] PATH..."
    && Args.usage Args.Tests.program Args.Tests.everything
      == "toyfmt --name TEXT [--offset N] [--keep TEXT]... [--colour CHOICE] [--level N] [FILE...]"

test "Args: the help" :=
  Args.help Args.Tests.program Args.Tests.options
    == ["usage: toyfmt [--check] [--width N] PATH...", "Formats Sprig files in place.", "", "arguments:",
          "  PATH...     Files or folders to format.", "options:",
          "  --check     Write nothing; list the files that would change, and fail if any", "              would.",
          "  --width N   The widest a line may be. (default: 80)", "  -h, --help  Show this help."].joinWith "\n"

test "Args: long help wraps under its column, and a spec without text has bare lines" :=
  Args.help
    { name = "t" }
    (Args.flag "a"
      (help := "one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen"))
    == ["usage: t [--a]", "", "options:",
          "  --a         one two three four five six seven eight nine ten eleven twelve",
          "              thirteen fourteen fifteen sixteen", "  -h, --help  Show this help."].joinWith "\n"
    && Args.help { name = "t" } (Args.flag "a") == "usage: t [--a]\n\noptions:\n  --a\n  -h, --help  Show this help."

test "Args: a spec's mistakes" :=
  Args.problems Args.Tests.options == []
    && Args.problems Args.Tests.everything == []
    && Args.problems (Args.Spec.start ((a b: Bool) => a) |> .and (Args.flag "x") |> .and (Args.flag "x"))
      == ["the option --x is used twice"]
    && Args.problems (Args.Spec.start ((a: Bool) => a) |> .and (Args.flag "help")) == ["--help is the library's own"]
    && Args.problems (Args.Spec.start ((a b: List Text) => a) |> .and (Args.arguments "A") |> .and (Args.arguments "B"))
      == ["more than one positional spec"]

test "Args.run: with no command line, the spec reads nothing" :=
  (IO.simulate [] (() =>
    Fail.toResult (() => Args.run Args.Tests.program (Args.Spec.start 7) (number => IO.print "got ${number}")))).fst
    == ["got 7"]

test "Args.run: a mistake exits 2 and prints nothing to standard output" :=
  let (printed, status) :=
    IO.simulate [] (() => Args.run Args.Tests.program Args.Tests.options (options => IO.print "ran"))
  printed == [] && status == Args.misuse

test "Args.Value: Text, Nat, Int, Path read and show" :=
  (Args.Value.read "a b": Result Text Text) == Ok "a b"
    && (Args.Value.read "12": Result Nat Text) == Ok 12
    && (Args.Value.read "-12": Result Int Text) == Ok (-12)
    && (Args.Value.read "src/a.sw": Result Path Text) == Ok "src/a.sw".toPath
    && (Args.Value.read "1.5": Result Nat Text) == Err "a whole number"
    && Args.Value.show (-3: Int) == "-3"
    && Args.Value.show "src/a.sw".toPath == "src/a.sw"

def Args.Tests.runWith (arguments: List Text): (List Text, ExitStatus) :=
  let pair :=
    IO.simulate [] (() => Args.runOn Args.Tests.program Args.Tests.options arguments (options => IO.print "ran"))
  (pair.fst, pair.snd)

test "Args: a bad command line exits 2 and prints nothing to standard output" :=
  Args.Tests.runWith ["--bogus"] == ([], Args.misuse) && Args.misuse == ExitStatus.of 2

test "Args: --help exits 0, and a good command line runs the body" :=
  (Args.Tests.runWith ["--help"]).snd == ExitStatus.success && Args.Tests.runWith ["a"] == (["ran"], ExitStatus.success)

test "Args: runStatusOn takes the body's own status" :=
  (IO.simulate [] (() => Args.runStatusOn Args.Tests.program Args.Tests.options ["a"] (options => ExitStatus.of 7))).snd
    == ExitStatus.of 7
