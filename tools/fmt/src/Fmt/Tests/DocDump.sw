--| The engine harness's reader (`Fmt.DocDump`) on small dumps: what a node
--| line stands for, escapes, and the three outcomes.

namespace Fmt.Tests
import Fmt.DocDump (answer, escape, unescape)
import Std (Bool, Result, Text)

def decl (number printed nodes: Text): Text := "decl ${number}\nsize 10\ntext ${printed}\n${nodes}"

test "a document that prints as Rust printed matches" :=
  answer (decl "1" "[a, b]" "Group\nConcat 3\nText [\nText a, b\nText ]\n") == Ok "decl 1 matched\n"

test "a closer text is a Closing: it stays before a waiting comment" :=
  answer (decl "1" "f x) -- c" "Concat 3\nText f x\nLineSuffix -- c\nText )\n") == Ok "decl 1 matched\n"

test "a different text is a mismatch, with the first line that differs" :=
  answer (decl "7" "a\\nb" "Concat 3\nText a\nHardLine\nText c\n")
    == Ok "decl 7 mismatched 2\n  expected: b\n  got: c\n"

test "text is escaped in the dump: backslash and line break" :=
  unescape "a\\\\b\\nc" == "a\\b\nc" && escape "a\\b\nc" == "a\\\\b\\nc"

test "a breaking group prints broken in the width" :=
  answer (decl "1" "a\\nb" "Group\nConcat 3\nText a\nHardLine\nText b\n") == Ok "decl 1 matched\n"

test "nodes Doc lacks are unsupported, by kind, and not compared" :=
  answer (decl "2" "whatever" "Concat 3\nAlign\nText x\nNarrowGroup 40\nText y\nMark 4\n")
    == Ok "decl 2 unsupported Align,Mark,NarrowGroup\n"

test "an IfBroken reads the mode its IdGroup printed in" :=
  answer (decl "1" "(a, b) ok" "Concat 2\nIdGroup 7\nText (a, b)\nIfBroken 7\nText broke\nText  ok\n")
    == Ok "decl 1 matched\n"

test "two declarations answer a line each" :=
  answer (decl "1" "a" "Text a\n" ++ decl "2" "b" "Text b\n") == Ok "decl 1 matched\ndecl 2 matched\n"

test "a dump that ends inside a node is an error" := match answer (decl "1" "a" "Concat 2\nText a\n") with
  | Err _ => True
  | Ok _ => False

test "a shared doc is written once and referred to after" :=
  answer (decl "1" "ab ab" "Concat 3\nShared 1\nText ab\nText  \nRef 1\n") == Ok "decl 1 matched\n"

test "a reference to a doc not shared yet is an error" := match answer (decl "1" "a" "Concat 2\nRef 1\nText a\n") with
  | Err _ => True
  | Ok _ => False

test "a document too large written out in full is counted and not read" :=
  answer "decl 3\nsize 50001\ntext x\nBogus node\n" == Ok "decl 3 oversized 50001\n"
