-- Braces after a constructor declared with brackets are an ordinary record
-- argument, as after a function (docs/proposals/brace-syntax-review.md §5):
-- a literal, an update, or a record pattern. Which reading applies is fixed
-- by how the constructor is declared, never by field names or types.

import Std (Eq, List, Nat, Option)

type Item = { name: Text, price: Nat }

def tea: Option Item := Some { name = "tea", price = 3 }

-- An update.
def dearer (item: Item): Option Item := Some { item | price = 4 }

-- A record pattern.
def nameOf: Option Item → Text
  | Some { name, .. } => name
  | None => "none"

test "a literal, an update and a pattern" :=
  nameOf tea == "tea" ∧ (dearer { name = "tea", price = 3 }) == Some { name = "tea", price = 4 }

-- Both readings may name the same fields: `Some` is declared with brackets, so
-- `value` below is the `Item`'s own field, not `Some`'s.
type Counter = { value: Nat, step: Nat }

def counted: Option Counter := Some { value = 3, step = 1 }

test "the record's own field" := (counted.map .value) == Some 3

-- More arguments may follow the braces, and they may be an argument.
type Labelled = | Label (item: Item) (tag: Text)

def hot: Labelled := Label { name = "tea", price = 3 } "hot"

def tagOf: Labelled → Text
  | Label ({ name, .. }) tag => name ++ " " ++ tag

test "braces then more arguments" := tagOf hot == "tea hot"

type Mode = | Filling | Draining

def describe (mode: Mode) (item: Item): Text := match mode with
  | Filling => "fill " ++ item.name
  | Draining => "drain " ++ item.name

test "braces as the next argument after a constructor" := describe Filling { name = "tea", price = 3 } == "fill tea"

-- Inside a list, with the bracketed form still working.
def items: List (Option Item) := [Some { name = "tea", price = 3 }, Some { name = "cake", price = 5 }, None]

test "both spellings" := items.length == 3
