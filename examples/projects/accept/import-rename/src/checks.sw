-- A type imported under another name: its constructors keep their own
-- names, and its namespace is reached through the new one. A library
-- function renamed too.
namespace Shop.Checks

import Shop.Spec (Status as Owing, total as specTotal)
import Std.List (length as count)

def owed: Owing -> Nat
  | Paid => 0
  | Due n => n

def owedAll (all: List Owing): Nat := specTotal (all.map owed)

test "owed" := owed (Owing.Due 3) == 3

test "all" := owedAll [Paid, Due 2, Due 5] == 7

test "count" := count [Paid, Paid] == 2
