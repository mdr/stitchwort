--| `meaning` on small cases: what it forgets, what it keeps, and that the
--| four passes keep it. Meanings are compared by their dumps, which leave
--| comments out; a bracket pair kept for its comment still shows as a
--| `Paren`.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, List, Option, Result, Text)
import Syntax (SourceFile)

def sameMeaning (one other: Text): Bool := match parsed one, parsed other with
  | Ok first, Ok second => first.meaning.plain.dump == second.meaning.plain.dump
  | _, _ => False

def differentMeaning (one other: Text): Bool := match parsed one, parsed other with
  | Ok first, Ok second => first.meaning.plain.dump != second.meaning.plain.dump
  | _, _ => False

def tidyKeepsMeaning (source: Text): Bool := match parsed source with
  | Ok file => file.tidy.meaning.plain.dump == file.meaning.plain.dump
  | Err _ => False

test "meaning: a pair around an application's head is kept away from a row" :=
  differentMeaning "def a: T := (f) x" "def a: T := f x" && differentMeaning "def a: T := (f a) b" "def a: T := f a b"

test "meaning: a pair at a row's left end is forgotten" :=
  sameMeaning "def a: {Fail} (List Nat) := []" "def a: {Fail} List Nat := []"
    && sameMeaning "def a: {IO} (f) x" "def a: {IO} f x"
    && sameMeaning "def a: {IO} (f a) + 1" "def a: {IO} f a + 1"
    && sameMeaning "def a: {IO} ((f a)) b" "def a: {IO} (f a) b"
    && sameMeaning "def a: {e} (Nat -> Nat) := id" "def a: {e} ((Nat -> Nat)) := id"

test "meaning: a pair P3 must keep after a row is kept" :=
  differentMeaning "def a: {IO} (f a) b" "def a: {IO} f a b"
    && differentMeaning "def a: {Fail} (a + b) * c" "def a: {Fail} a + b * c"
    && differentMeaning "def a: {Fail}\n  -- why\n  (List Nat) := []" "def a: {Fail} List Nat := []"

test "meaning: a pair around a binder's whole type is forgotten" :=
  sameMeaning "theorem c ∀ (h: (∀ (i: Nat) => i = i)): True := h" "theorem c ∀ (h: ∀ (i: Nat) => i = i): True := h"
    && sameMeaning "def f: Nat := fun (x: ((Nat))) => x" "def f: Nat := fun (x: Nat) => x"
    && sameMeaning "def f: Nat := (x: (Nat))" "def f: Nat := (x: Nat)"
    && differentMeaning "def f: Nat := g (Nat)" "def f: Nat := g Nat"

test "meaning: a group is split where P4 could have merged it" :=
  sameMeaning "def f (a b: Nat): Nat := a" "def f (a: Nat) (b: Nat): Nat := a"
    && sameMeaning "theorem t ∀ (a b: Nat): a = a := byComputing" "theorem t ∀ (a: Nat) (b: Nat): a = a := byComputing"
    && sameMeaning "def f: Nat := fun (a b: Nat) => a" "def f: Nat := fun (a: Nat) (b: Nat) => a"
    && differentMeaning "def f (x y: P x): Nat := 1" "def f (x: P x) (y: P x): Nat := 1"
    && differentMeaning "def f (a b: Nat := 1): Nat := a" "def f (a: Nat := 1) (b: Nat := 1): Nat := a"
    && differentMeaning "theorem t: ∃ (a b: Nat) => a = b := h" "theorem t: ∃ (a: Nat) (b: Nat) => a = b := h"

test "meaning: ∀ and trailing commas are forgotten" :=
  sameMeaning "theorem t (a: Nat): a = a := byComputing" "theorem t ∀ (a: Nat): a = a := byComputing"
    && differentMeaning "theorem t [a: Nat]: a = a := byComputing" "theorem t ∀ [a: Nat]: a = a := byComputing"
    && sameMeaning "def x: T := [1, 2,]" "def x: T := [1, 2]"
    && sameMeaning "def f: Nat := match x with | (p, q,) => 1" "def f: Nat := match x with | (p, q) => 1"

test "meaning: the four passes keep it" :=
  tidyKeepsMeaning "def a (x: (T)) (y: ((U))): {Fail} ((List Nat)) := x"
    && tidyKeepsMeaning "theorem t (a: Nat) (b: Nat) (c: (Nat)): a = a := byComputing"
    && tidyKeepsMeaning "def f: {IO} ((f a)) + (g) x := [1, 2,]"
    && tidyKeepsMeaning "def f (x: P x) (y: P x) (z: Nat) (w: Nat): Nat := fun (a: Nat) (b: (Nat)) => a"
    && tidyKeepsMeaning "def f: {Fail} (-1) → z := (1, 2,)"
