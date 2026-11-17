--| The formatter, end to end: lex (stage 1's `Syntax.lex`), rule N
--| (stage 1's `Lexed.settled`), parse, the four passes, print. The
--| grammar, the lowering's three errors and the printer are stages 2, 2
--| and 5–6; they stand open here so that the theorems about `format` can
--| be stated against them.

namespace Fmt.Sketch
import Syntax (Lexed, lex)
import Std (List, Nat, Option, Result, Text)

type FormatResult = | Formatted (text: Text) | Refused (message: Text)

--| Stage 2's grammar on `Parse`, run over settled leaves, and its error as
--| the message the Rust parser gives. Each recursion (`expression`,
--| `pattern`) and each loop starts with fuel the items left there and one
--| more, as `Parse.recursiveWith` does, plus `extra`.
def grammarWith (extra: Nat) (lexed: Lexed): Result SourceFile Text := ?

--| The errors the lowering raises that the formatter must refuse too
--| (§3.5): a parameter named twice in a header, an or-pattern that binds
--| names, a condition on an arm with `()` and no body.
def SourceFile.refusal (file: SourceFile): Option Text := ?

--| The tree of settled leaves. No extra fuel is needed for any nesting
--| (`fuelEnough`).
def parseLexed (lexed: Lexed): Result SourceFile Text := match grammarWith 0 lexed with
  | Err message => Err message
  | Ok file =>
    match file.refusal with
      | Some message => Err message
      | None => Ok file

def parse (source: Text): Result SourceFile Text := match lex source with
  | Err message => Err message
  | Ok lexed => parseLexed lexed.settled

--| The printing rules and the engine, at `width`: only white space is
--| chosen here.
def SourceFile.print (file: SourceFile) (width: Nat): Text := ?

def format (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => Refused message
  | Ok tree => Formatted (tree.tidy.print width)
