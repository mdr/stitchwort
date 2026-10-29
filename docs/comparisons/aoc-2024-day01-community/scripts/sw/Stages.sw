-- Day 1 cut at each stage, to see where the time goes on a large input.
-- `Parse` only parses (the program's parser); `Sort` also sorts both lists;
-- `Counts` parses and builds the count map. Each prints something that
-- depends on all of its work, so none is skipped.
namespace Scratch.Stages
import Aoc.Year2024.Day01 (parseLocationLists)
import Std (Fail, IO, List, Map, Nat, Text)

def parse(): {IO, Fail} () :=
  let lists := parseLocationLists IO.readAll()
  IO.print "${lists.left.sum + lists.right.sum}"

def sort(): {IO, Fail} () :=
  let lists := parseLocationLists IO.readAll()
  IO.print "${lists.left.sort.headOr 0 + lists.right.sort.headOr 0}"

def counts(): {IO, Fail} () :=
  let lists := parseLocationLists IO.readAll()
  IO.print "${(Map.counts lists.right).size}"

def words(): {IO} () :=
  let ids := IO.readAll().words.filterMap Text.toNat
  IO.print "${ids.sum}"
