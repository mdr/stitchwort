-- `List.attach`: the elements of a list, each with the proof that it is in
-- the list. For a recursive call inside a function passed to `sumBy`, `map`
-- and the like, whose `decreasing` proof needs to know where its argument
-- came from: `xs.attach.sumBy (e => f e.value [decreasing := … e.isIn …])`
-- (docs/proposals/well-founded-recursion.md, stage 3b). Membership itself,
-- `List.Mem`, and its facts (`List.memRangeFrom`, `List.memBetween`,
-- `List.memFilter`, `List.memMap`) are in Toolkit.sw.

-- An element of `xs`, with the proof that it is one.
type List.Member (a: Type) (xs: List a) = { value: a, isIn: List.Mem value xs }

-- The elements of `rest`, a part of `whole`, as members of `whole`: `sub`
-- says that what is in `rest` is in `whole`. One pass, structural.
def List.attachFrom (whole: List a): (rest: List a) -> ((x: a) -> List.Mem x rest -> List.Mem x whole) -> List (List.Member a whole)
  | Nil, sub => Nil
  | Cons x xs, sub => Cons { value = x, isIn = sub x (Inl rfl) } (List.attachFrom whole xs (y h => sub y (Inr h)))

-- The elements of `xs`, in order, each with the proof that it's in `xs`.
-- It builds a new list (for now: returning `xs` itself at run time is a
-- later optimisation).
def List.attach (xs: List a): List (List.Member a xs) := List.attachFrom xs xs (x h => h)

theorem List.attachExample: List.map (e => e.value) (List.attach [3, 1, 2]) = [3, 1, 2] := rfl

-- The lemmas are proved for `attachFrom` first, with `whole`, `rest` and
-- `sub` general, and then for `attach`: the tail of `attach (Cons x xs)` is
-- an `attachFrom`, not `attach xs`.

-- Dropping the proofs gives back the list.
theorem List.attachFromValues (whole: List a): (rest: List a) -> (sub: (x: a) -> List.Mem x rest -> List.Mem x whole) ->
    List.map (e => e.value) (List.attachFrom whole rest sub) = rest
  | Nil, sub => rfl
  | Cons x xs, sub => Eq.cong (Cons x) (List.attachFromValues whole xs (y h => sub y (Inr h)))

theorem List.attachValues (xs: List a): List.map (e => e.value) (List.attach xs) = xs := List.attachFromValues xs xs (x h => h)

-- A sum over the attached list that only looks at the values is the sum over
-- the list.
theorem List.sumByAttachFrom [auto add: Add b] (f: a -> b) (whole: List a) (rest: List a) (sub: (x: a) -> List.Mem x rest -> List.Mem x whole):
    List.sumBy (e => f e.value) (List.attachFrom whole rest sub) = List.sumBy f rest :=
  Eq.trans (Eq.sym (List.sumByMap f (e => e.value) (List.attachFrom whole rest sub)))
    (Eq.cong (List.sumBy f) (List.attachFromValues whole rest sub))

theorem List.sumByAttach [auto add: Add b] (f: a -> b) (xs: List a): List.sumBy (e => f e.value) (List.attach xs) = List.sumBy f xs :=
  List.sumByAttachFrom f xs xs (x h => h)

-- The same for `map`.
theorem List.mapAttach (f: a -> b) (xs: List a): List.map (e => f e.value) (List.attach xs) = List.map f xs :=
  Eq.trans (Eq.sym (List.mapMap f (e => e.value) (List.attach xs))) (Eq.cong (List.map f) (List.attachValues xs))
