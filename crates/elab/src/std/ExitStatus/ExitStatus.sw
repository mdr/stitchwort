--| `ExitStatus`: the number a finished program hands to the shell, 0 to 255.
--| `main` may return one instead of `()`: `stitchwort run`, `--js`, a built
--| executable and the playground each report it, so a program can tell its
--| caller more than "worked" and "failed". `0` is the only code with a
--| meaning everywhere (success); a program names the others itself.
--|
--|   import Std (ExitStatus, IO)
--|
--|   def main(): {IO} ExitStatus :=
--|     IO.print "checked"
--|     if clean then ExitStatus.success else ExitStatus.of 3
--|
--| The code is a [`Fin`] below 256, because a larger number means different
--| things on different systems (256 is success on Linux and an error on
--| Windows): `ExitStatus.of 300` is refused when the program is checked.
--| `Fail` left unhandled is still status 1, and a runtime error is 2.
-- (docs/proposals/exit-status.md, D3616)

--| An exit status: its code is a position below 256, so it runs as a machine
--| number.
type ExitStatus = { code: Fin 256 }

--| The status for `code`, which must be below 256 (decided for a written
--| number, so `ExitStatus.of 3` needs no proof): `ExitStatus.of 300` is an
--| error. For a computed number use [`ExitStatus.ofNatCheck`].
def ExitStatus.of (code: Nat) [auto ok: code < 256]: ExitStatus := { code = Fin.ofNatLt 256 code ok }

--| The status for `code`, if it is below 256: `None` otherwise.
def ExitStatus.ofNatCheck (code: Nat): Option ExitStatus := match Fin.ofNatCheck 256 code with
  | Some c => Some { code = c }
  | None => None

--| The number itself, as the shell sees it.
def ExitStatus.toNat (status: ExitStatus): Nat := Fin.toNat status.code

--| Status 0: the program did what it was asked. A `main` returning `()` ends
--| this way.
def ExitStatus.success: ExitStatus := ExitStatus.of 0

--| Status 1: the program failed. An unhandled `Fail` ends this way too.
def ExitStatus.failure: ExitStatus := ExitStatus.of 1

--| The number itself: `"${ExitStatus.of 3}"` is `3`.
instance ExitStatus.instShow: Show ExitStatus := Show.fromText (status => Nat.toText (ExitStatus.toNat status))

test "exitStatus: of" := ExitStatus.toNat (ExitStatus.of 3) == 3
test "exitStatus: success and failure" :=
  ExitStatus.toNat ExitStatus.success == 0 && ExitStatus.toNat ExitStatus.failure == 1
test "exitStatus: ofNatCheck in range" := (ExitStatus.ofNatCheck 255).map ExitStatus.toNat == Some 255
test "exitStatus: ofNatCheck out of range" := ExitStatus.ofNatCheck 256 == None
test "exitStatus: ==" := ExitStatus.of 2 == ExitStatus.of 2 && ExitStatus.of 2 != ExitStatus.failure
test "exitStatus: show" := "${ExitStatus.of 42}" == "42"
test "exitStatus: through IO.simulate" := (IO.simulate [] (() => (IO.print "hi"; ExitStatus.of 2))).snd.toNat == 2

theorem ExitStatus.simulateExample: (IO.simulate [] (() => (IO.print "hi"; ExitStatus.of 2))).snd.code = Fin.ofNat 2 :=
  byComputing
