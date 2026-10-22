-- Day 5's lemmas from aoc/src/Aoc/Day05/Proofs/Part2.sw, rewritten with `omega`.

import Std (Nat, Bool, Void, List, Eq)

type Range = { from: Nat, to: Nat }

def Range.contains (r: Range) (id: Nat): Bool := r.from <= id && id <= r.to

def absorb (merged: List Range) (r: Range): List Range :=
  match merged with
    | Nil => [r]
    | Cons last earlier =>
      if r.from <= last.to + 1
      then Cons { from = last.from, to = Nat.max last.to r.to } earlier
      else Cons r merged

def covered (rs: List Range) (id: Nat): Bool := rs.any (r => r.contains id)

def Below (b: Nat) (rs: List Range): Prop := (id: Nat) -> covered rs id = True -> id < b

def Stacked: List Range -> Prop
  | Nil         => Unit
  | Cons m rest => Below m.from rest && Stacked rest

def LoAtMost (b: Nat): List Range -> Prop
  | Nil         => Unit
  | Cons last _ => last.from <= b

theorem absorbLo (r: Range) (b: Nat) (h: r.from <= b): (merged: List Range) -> LoAtMost r.from merged -> LoAtMost b (absorb merged r)
  | Nil,               ok => h
  | Cons last earlier, ok =>
    match e: Nat.leq r.from (last.to + 1) with
      | True  => omega
      | False => h

theorem absorbStacked (r: Range): (merged: List Range) -> LoAtMost r.from merged -> Stacked merged -> Stacked (absorb merged r)
  | Nil,               ok, s           => Both (id h => Void.exfalso (Bool.falseNotTrue h)) Trivial
  | Cons last earlier, ok, Both b rest =>
    match e: Nat.leq r.from (last.to + 1) with
      | True  => Both b rest
      | False =>
        Both
          (id h =>
            match i: last.contains id with
              | True  => omega
              | False => omega [b id h])
          (Both b rest)

theorem topGe: (z: Nat) -> (rs: List Range) -> z <= rs.foldLeft (m r => Nat.max m r.to) z
  | z, Nil       => Nat.leRefl z
  | z, Cons r rs => omega [Nat.leMaxLeft z r.to, topGe (Nat.max z r.to) rs]

theorem coveredTop: (z: Nat) -> (rs: List Range) -> (id: Nat) -> covered rs id = True -> id <= rs.foldLeft (m r => Nat.max m r.to) z
  | z, Nil,       id, h => Void.exfalso (Bool.falseNotTrue h)
  | z, Cons r rs, id, h =>
    match e: r.contains id with
      | True  => omega [Nat.leMaxRight z r.to, topGe (Nat.max z r.to) rs]
      | False => coveredTop (Nat.max z r.to) rs id h

theorem mergedContains (a: Range) (r: Range) (id: Nat) (h1: a.from <= r.from) (h2: r.from <= a.to + 1):
    Range.contains { from = a.from, to = Nat.max a.to r.to } id = (a.contains id || r.contains id) :=
  match t: Nat.leq a.from id, i: Nat.leq id a.to with
    | True, True =>
      Eq.trans (Bool.decTrueToBool (Nat.leq id (Nat.max a.to r.to))) (omega [Nat.leMaxLeft a.to r.to])
    | True, False =>
      Eq.trans (Bool.decTrueToBool (Nat.leq id (Nat.max a.to r.to)))
        (Eq.trans (Nat.leqMaxAbove id a.to r.to i)
          (Eq.sym (Nat.betweenFrom r.from r.to id omega)))
    | False, _ => Eq.sym (Nat.betweenBelow r.from r.to id omega)
