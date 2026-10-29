-- Part 2 by topological sort of the rules restricted to each update: take a
-- page no remaining page must precede, then the rest. Unlike sorting with the
-- rules as a comparison, it needs no rule between every pair of pages, only
-- no cycle among the update's pages (on a cycle it keeps the rest as is).
namespace Scratch.Topo
import Aoc.Year2024.Day05 (..)
import Std (Fail, IO, List, Nat, Option)

-- A page of `pages` that no other page of `pages` must precede.
def firstPage (precedes: Nat → Nat → Bool) (pages: List Nat): Option Nat :=
  pages.findMap (page => if pages.any (other => precedes other page) then None else Some page)

def topo (precedes: Nat → Nat → Bool): Nat → List Nat → List Nat
  | Zero, pages => pages
  | Succ fuel, pages =>
    match firstPage precedes pages with
      | None => pages
      | Some first => Cons first (topo precedes fuel (pages.removeFirst first))

def solvePart2Topo (queue: PrintQueue): Nat :=
  let precedes := mustPrecede (ruleSet queue.rules)
  queue.updates.filter (update => !(inOrder precedes update.pages))
    |> .map (update => ({ pages = topo precedes update.pages.length update.pages }: Update))
    |> .sumBy .middlePage

def main(): {IO, Fail} () :=
  let queue := parsePrintQueue IO.readAll()
  IO.print "Part 2: ${solvePart2Topo queue}"
