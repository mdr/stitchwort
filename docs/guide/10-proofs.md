# 10. Proofs

A test checks that a program does the right thing for one input. A **theorem** states that it does for every input, and the compiler checks the proof. This chapter explains how to write them, without assuming you've done it before.

## Statements are types

A theorem looks like a definition: a name, parameters, a type, and a body. The type is the statement, and the body is the proof:

<!-- snippet: proofs.sw#rfl -->
```stitchwort
def double (n: Nat): Nat := n + n

theorem doubleFour: double 4 = 8 := rfl

theorem zeroPlus (n: Nat): 0 + n = n := rfl
```

`double 4 = 8` is a type whose values are proofs that `double 4` equals `8`. `rfl` ("reflexivity") is the proof that a thing equals itself, and the checker accepts it when both sides **compute** to the same value. `double 4` computes to `8`, so `rfl` proves the first theorem.

The second is about every `n`, and `rfl` still works, because `+` is defined by recursion on its first argument: `0 + n` computes to `n` without knowing what `n` is. When `rfl` fails, the message shows what each side computed to:

<!-- snippet: errors/rfl.sw -->
```stitchwort
def double (n: Nat): Nat := n + n

theorem doubleFour: double 4 = 9 := rfl
```

<!-- output: check errors/rfl.sw -->
```text
[E-REFL] Error: `rfl` can't prove this
   ╭─[ errors/rfl.sw:3:37 ]
   │
 3 │ theorem doubleFour: double 4 = 9 := rfl
   │                                     ─┬─
   │                                      ╰─── `double 4` and `9` aren't equal
   │
   │ Note 1: computing the left side gives `8`
   │
   │ Note 2: `rfl` proves `a = b` only when both sides compute to the same value
   │
   │ Note 3: this statement is false:
   │         `double 4 = 9` is false:
   │           left:  8
   │           right: 9
───╯
1 error: in `doubleFour`
```

The last note comes from a **counterexample search**: when a proof fails, the checker also tries the statement itself on inputs, small ones first, then random ones. Here there are no inputs to try, and the statement computes to false, so no proof could work. A search that finds nothing says nothing.

Two proofs of the same statement are interchangeable: the checker treats them as equal, so a function that takes a proof gives the same result whichever proof it is handed. A theorem is erased when the program runs: it costs nothing. In a project, `stitchwort run` doesn't even check the namespaces it doesn't need, which is why proofs usually have a namespace of their own.

## Induction is recursion

`n * 1 = n` is true, but `rfl` can't prove it for an unknown `n`: `*` recurses on its first argument, and `n` isn't a known number. (`n + 0 = n` and `n + 1 = Succ n` do hold by computing: `+` is special, and computes on its second argument too when the first is unknown.) The proof goes by cases on `n`, like a function with arms. A theorem's variables go before the colon, like a function's parameters, and a proof by cases is a `match` on them (the house style for theorems, D3470; a `def` keeps its arms):

<!-- snippet: proofs.sw#induction -->
```stitchwort
theorem timesOne (n: Nat): n * 1 = n := match n with
  | Zero => rfl
  | Succ k => Eq.cong Succ (timesOne k)
```

In the `Zero` arm the statement is `0 * 1 = 0`, which computes. In the `Succ k` arm it is `Succ k * 1 = Succ k`, which computes to `Succ (k * 1) = Succ k` (`Succ k * 1` is `1 + k * 1`, which messages write `k * 1 + 1`: a sum stuck on an unknown is shown with its number last). The recursive call `timesOne k` proves `k * 1 = k`: this is the induction hypothesis, and calling the theorem on a smaller value is how induction is written. The compiler checks that it terminates, like any recursion. `Eq.cong Succ` turns `x = y` into `Succ x = Succ y`.

The skill is in reading what each case needs. Using the induction hypothesis directly gives a message that shows it:

<!-- snippet: errors/induction.sw -->
```stitchwort
import Std (Eq)

theorem timesOne (n: Nat): n * 1 = n := match n with
  | Zero => rfl
  | Succ k => timesOne k
```

<!-- output: check errors/induction.sw -->
```text
[E-TYPE-MISMATCH] Error: type mismatch
   ╭─[ errors/induction.sw:5:15 ]
   │
 5 │   | Succ k => timesOne k
   │               ─────┬────
   │                    ╰────── expected `k * 1 + 1 = Succ k`, but this has type `k * 1 = k`
───╯
1 error: in `timesOne`
```

## Goals: `?`

You don't have to know what a case needs before writing it. Put `?` where a proof (or any expression) is missing, and the checker reports the **goal**: the names in scope with their types, and after `⊢`, what has to go there:

<!-- snippet: errors/hole.sw -->
```stitchwort
import Std (Eq)

theorem timesOne (n: Nat): n * 1 = n := match n with
  | Zero => rfl
  | Succ k => ?
```

<!-- output: check errors/hole.sw -->
```text
[GOAL] Goal: in `timesOne`
   ╭─[ errors/hole.sw:5:15 ]
   │
 5 │   | Succ k => ?
   │               ┬
   │               ╰── k: Nat
   │                   ⊢ k * 1 + 1 = Succ k
───╯
1 goal open
```

A declaration with a `?` isn't an error, but it isn't finished either: it is checked assuming the goal holds, and so is what uses it, so a mistake in them shows now, but none of them is finished, and `check` fails until every goal is closed (unless the project's `stitchwort.yaml` says `check: open-goals: warn`, which makes `check` report each as a warning and pass; `audit` still fails them).

`check` says what depends on the goals, in the same breath as it counts them. A declaration that *relies on* a goal was checked, assuming the goal holds; one that has to compute through a `?` (`half 1 = 0` by `rfl`, while `half`'s `Succ` case is still `?`) *can't be checked until the goal is filled*, so it wasn't checked at all, and `check` names it and the goal it waits for:

```text
2 goals open
3 declarations rely on open goals, checked assuming they hold (`stitchwort goal` lists them)
1 declaration can't be checked until a goal is filled (not checked at all):
  Demo.halfOne  needs `half`'s goal (src/Demo/Demo.sw:11:17)
```

`stitchwort goal`, with no `--at`, lists every open goal with what relies on it, and `stitchwort audit` fails each of them and names the goal. A definition with a `?` has equation lemmas (`half.eq1`, `half.eq2`) too, and they are unfinished as well. You can state a lemma with `?` as its proof and use it in the main theorem first, then come back to it. In the editor, the goal shows on hover, and "Stitchwort: Show Goals" opens a panel that follows the cursor. It works anywhere in a file, not only on a `?`: put the cursor in a proof, on an arm's body or a step of a `calc`, and it shows the names in scope and `⊢` what that expression has to prove. In program code it shows `expected T` instead, or `has type T` where nothing was expected. Moving the cursor updates the panel after a short pause (about a third of a second, longer in a big file); until then the last answer stays, and where there is nothing to show (a comment, a pattern, a signature) it is kept, dimmed.

The goal is shown as you wrote it, with the values of the case put in. When it computes to something that prints differently, a second line says so, dimmed in the editor: in the `Rock` arm of a proof that `beats m m = False`, the goal reads `⊢ beats Rock Rock = False`, then `computes to False = False`. The first line is the statement you are proving; the second is what `rfl` and the checker see. A computed line over 240 characters is cut. Hypotheses are shown as the checker has them.

## Proofs about lists

The same pattern works for any recursive type. A proof about lists has a `[]` case and a `[x, ..rest]` case:

<!-- snippet: proofs.sw#lists -->
```stitchwort
def mapList (f: a → b): List a → List b
  | [] => []
  | [x, ..rest] => [f x, ..mapList f rest]

theorem lengthMapList (f: a → b) (xs: List a): (mapList f xs).length = xs.length := match xs with
  | [] => rfl
  | [x, ..rest] => Eq.cong Succ (lengthMapList f rest)
```

`(mapList f xs).length` in the `[x, ..rest]` case computes to `Succ (mapList f rest).length`, so `Eq.cong Succ` of the hypothesis is the proof.

## Rewriting and chains

`rewrite p in t` uses an equation `p: a = b` to replace `a` with `b` in the goal, then proves what's left with `t`. With no `in`, what's left must hold by computing. Several rules are applied in order:

<!-- snippet: proofs.sw#rewrite -->
```stitchwort
theorem swapTimesOne (a: Nat) (b: Nat): (a + b) * 1 = b + a :=
  rewrite Nat.mulOne (a + b), Nat.addComm a b
```

`Nat.mulOne (a + b)` turns `(a + b) * 1` into `a + b`, and `Nat.addComm a b` turns `a + b` into `b + a`, leaving `b + a = b + a`. The library's lemmas are named after what they say: `Nat.addComm`, `Nat.addAssoc`, `List.lengthMap`, `List.lengthAppend`. `rewrite <- p` rewrites from right to left, and `rewrite p at h` rewrites the type of a hypothesis `h` instead of the goal. `rewrite` also goes inside a function passed as an argument, through the congruence lemma of the function it is passed to: `rewrite Nat.mulOne _` proves `List.map xs (x => x * 1) = List.map xs (x => x)` by `List.mapCong`, with `_` standing for `x`. Arguments left off a rule's end are filled in the same way, and a premise the rule needs, such as `x <= n` for `Nat.addSubCancel x n`, is proved by a hypothesis or by `omega`; inside `(0 ..< n).sumBy f` the congruence lemma also says that `x` is below `n`, which proves it, so `rewrite Nat.addSubCancel` turns `x + (n - x)` into `n` there.

`calc` writes a proof as a chain of steps, each with its own justification, like a calculation on paper. The chain may mix `=`, `<=` and `<`:

<!-- snippet: proofs.sw#calc -->
```stitchwort
theorem chain (a: Nat) (b: Nat) (c: Nat) (ab: a = b) (bc: b ≤ c) (small: c < 10): a < 10 :=
  calc a
    _ = b := ab
    _ ≤ c := bc
    _ < 10 := small
```

A step with no proof is proved by computing.

## Arithmetic: `omega`

For statements in linear arithmetic over `Nat` and `Int` (`+`, `-`, comparisons, multiplication, division and remainder by a constant, `n.toInt`), `omega` finds the proof itself, using every fact in scope:

<!-- snippet: proofs.sw#omega -->
```stitchwort
theorem roomForOne (x: Nat) (y: Nat) (before: x < y) (limit: y ≤ 10): x + 1 ≤ 10 := omega

theorem twiceIsDouble (n: Nat): double n = 2 * n := omega

theorem stepBack (n: Nat) (x: Int) (h: x < n.toInt): x - 1 < n.toInt - 1 := omega

theorem thirdOfTriple (k: Int): (3 * k) / 3 = k := omega

theorem sizeOfSum (x: Int) (y: Int): (x + y).natAbs ≤ x.natAbs + y.natAbs := omega
```

On `Int`, an unknown may be negative, while `n.toInt` of a `Nat` is known to be at least 0, so `Nat` and `Int` facts mix; `x / 3` and `x % 3` are unknowns with `3 * (x / 3) + x % 3 = x` and `0 ≤ x % 3 < 3`. `x.natAbs`, the size of `x`, is known to be `x` or `0 - x`, so `(x + y).natAbs ≤ x.natAbs + y.natAbs` is `omega` too. If the facts contradict each other, `omega` proves any goal, not only an arithmetic one. `omega [p, q]` adds the facts `p` and `q`, such as lemmas applied to arguments. Anything that isn't linear arithmetic (`x * y`, `xs.length`, a function call) is treated as an unknown number, though a field of a record written out, `{ row = 1, column = 0 }.row`, is computed first.

Comparisons may be joined with `&&`, `||` and `not`, as `Bool`s (`(a == b || a < c) = True`) or as propositions (`p ∨ q`, `p ∧ q`, `¬p`), and `==` and `!=` on numbers count as comparisons. A fact that is a disjunction is split into its two cases, each proved separately, when the other facts aren't enough (up to 8 splits); a goal that is one is proved by cases on one side, the other side proved where it fails:

<!-- snippet: proofs.sw#omega-logic -->
```stitchwort
def isNeighbour (a: Nat) (b: Nat): Bool := a + 1 == b || b + 1 == a

theorem neighboursDiffer (a: Nat) (b: Nat) (near: isNeighbour a b = True): a != b := omega

theorem nearZero (a: Nat) (h: a ≤ 1): a = 0 ∨ a = 1 := omega
```

When `omega` fails, it says which facts it used and gives values that satisfy them but not the goal, which usually points at the missing fact:

<!-- snippet: errors/omega.sw -->
```stitchwort
theorem roomForOne (x: Nat) (y: Nat) (before: x ≤ y) (limit: y ≤ 10): x + 1 ≤ 10 := omega
```

<!-- output: check errors/omega.sw -->
```text
[E-OMEGA] Error: `omega` can't prove `x ≤ 9`
   ╭─[ errors/omega.sw:1:85 ]
   │
 1 │ theorem roomForOne (x: Nat) (y: Nat) (before: x ≤ y) (limit: y ≤ 10): x + 1 ≤ 10 := omega
   │                                                                                     ──┬──
   │                                                                                       ╰──── an integer model of the arithmetic abstraction satisfies the facts and the goal's negation
   │
   │ Note 1: facts: `x ≤ y` (before), `y ≤ 10` (limit)
   │
   │ Note 2: atoms: `x`, `y`
   │
   │ Note 3: an integer model of the arithmetic abstraction (it may not be a real counterexample): x = 10, y = 10
   │
   │ Note 4: this statement is false; a counterexample:
   │           x = 10
   │           y = 10
   │         `x ≤ y` holds
   │         `y ≤ 10` holds
   │         `x + 1 ≤ 10` is false
───╯
1 error: in `roomForOne`
```

With `x = 10`, `x + 1 <= 10` is false: the hypothesis needs to be `x < y`. Note 3 is `omega`'s own model, which may not be real; Note 4 is from the counterexample search, which ran the statement on those values and found every hypothesis true and the conclusion false, so the theorem as written is false.

## Algebra: `ring`

`omega` doesn't multiply unknowns together. For an equation that holds by the laws of `+` and `*` (`x * y = y * x`, multiplying out brackets), `ring` multiplies both sides out, collects like terms, and checks that they match. It works over `Nat` and `Int`, and treats anything else (`xs.length`, `a - b` between `Nat`s, a function call) as an unknown. `ring [h]` also uses the equation `h`:

<!-- snippet: proofs.sw#ring -->
```stitchwort
theorem squareOfSum (a: Nat) (b: Nat): (a + b) * (a + b) = a * a + 2 * a * b + b * b := ring

theorem areaGrows (w: Nat) (h: Nat): (w + 1) * (h + 1) = w * h + w + h + 1 := ring

theorem pairCount (n: Nat) (p: Nat) (twice: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n := ring [twice]
```

When the two sides differ, the error shows both multiplied out, and the difference:

<!-- snippet: errors/ring.sw -->
```stitchwort
theorem squareOfSum (a: Int) (b: Int): (a + b) * (a + b) = a * a + b * b := ring
```

<!-- output: check errors/ring.sw -->
```
[E-RING] Error: `ring` can't prove `(a + b) * (a + b) = a * a + (b * b)`
   ╭─[ errors/ring.sw:1:77 ]
   │
 1 │ theorem squareOfSum (a: Int) (b: Int): (a + b) * (a + b) = a * a + b * b := ring
   │                                                                             ──┬─
   │                                                                               ╰─── the two sides are different polynomials
   │
   │ Note 1: left:  a * a + 2 * a * b + b * b
   │
   │ Note 2: right: a * a + b * b
   │
   │ Note 3: the left side has `2 * a * b` more
   │
   │ Note 4: this statement is false; a counterexample:
   │           a = 1
   │           b = 1
   │         `(a + b) * (a + b) = a * a + (b * b)` is false:
   │           left:  4
   │           right: 2
───╯
1 error: in `squareOfSum`
```

A hypothesis can have a coefficient, any `Nat` or `Int` expression, written in front of it: `ring [4 * h]` uses `h: l = r` as `4 * l = 4 * r`, and `ring [-h]` uses it turned round. `ring` then checks that the goal's left side minus its right side is exactly the sum of each coefficient times its hypothesis's `l - r`. A hypothesis written without a `-` is also tried the other way round, so the sign is only needed when you want to say it:

<!-- snippet: proofs.sw#ring-coefficients -->
```stitchwort
theorem scaledUp (a: Int) (b: Int) (half: a = 2 * b): 4 * a = 8 * b := ring [4 * half]

theorem bothScaled (x: Int) (y: Int) (k: Int) (sum: x + y = 10) (gap: x - y = 2): 2 * k * x = 12 * k := ring [k * sum, k * gap]

theorem turnedRound (a: Int) (b: Int) (h: a = b + 1): b - a = -1 := ring [-h]
```

When the coefficients are wrong, the error shows what is left over:

<!-- snippet: errors/ring-coefficient.sw -->
```stitchwort
theorem scaledUp (a: Int) (b: Int) (half: a = 2 * b): 4 * a = 8 * b := ring [2 * half]
```

<!-- output: check errors/ring-coefficient.sw -->
```
[E-RING] Error: `ring` can't prove `4 * a = 8 * b`
   ╭─[ errors/ring-coefficient.sw:1:72 ]
   │
 1 │ theorem scaledUp (a: Int) (b: Int) (half: a = 2 * b): 4 * a = 8 * b := ring [2 * half]
   │                                                                        ───────┬───────
   │                                                                               ╰───────── the two sides are different polynomials
   │
   │ Note 1: with the hypotheses `l = r` added, each times its coefficient, the left side plus every `r` against the right side plus every `l`:
   │
   │ Note 2: left:  4 * a + 4 * b
   │
   │ Note 3: right: 2 * a + 8 * b
   │
   │ Note 4: the left side has `2 * a` more and `4 * b` less
   │
   │ Note 5: left over: `2 * a - 4 * b`, the goal's left minus its right, minus each coefficient times its hypothesis's `l - r`; it has to be 0
───╯
1 error: in `scaledUp`
```

`(ring: a = b)` states the equation, so it can be given to `rewrite`: `rewrite (ring: i + (p + q) = i + p + q)`.

## Proof by cases: `cases`

Many facts about `Bool`s, `Option`s and `if`s hold because every case works out: check `a = True` and `a = False`, and each side computes to the same thing. `cases` does that for you. It finds what the goal is stuck on (`a` in `a ∨ b`, the `x < lo` in `clamp`'s `if`), splits on it as a `match` would, and keeps going until each case is closed: by computation, by a hypothesis that can't hold in that case (`h: (a ∧ b) = True` when `a = False`), by a hypothesis that is the goal, or, when nothing is left to split, by `omega`:

<!-- snippet: proofs.sw#cases -->
```stitchwort
theorem orComm (a: Bool) (b: Bool): (a ∨ b) = (b ∨ a) := cases

theorem andLeft (a: Bool) (b: Bool) (h: (a ∧ b) = True): a = True := cases

def clamp (lo: Nat) (hi: Nat) (x: Nat): Nat := if x < lo then lo else if hi < x then hi else x

theorem clampBelow (lo: Nat) (hi: Nat) (x: Nat) (ordered: lo ≤ hi): clamp lo hi x ≤ hi := cases
```

`cases in t` tries the proof `t` in each case first, for the cases that `cases` can't close alone. When a case can't be closed, the error names it by its splits and shows what that case knows:

<!-- snippet: errors/cases.sw -->
```stitchwort
theorem atMostTwo (a: Bool) (n: Nat) (h: (a ∧ n ≤ 3) = True): n ≤ 2 := cases
```

<!-- output: check errors/cases.sw -->
```
[E-CASES] Error: `cases` couldn't close the case it reached by the splits a = True, (n <= 2) = False
   ╭─[ errors/cases.sw:1:72 ]
   │
 1 │ theorem atMostTwo (a: Bool) (n: Nat) (h: (a ∧ n ≤ 3) = True): n ≤ 2 := cases
   │                                                                        ──┬──
   │                                                                          ╰──── this `cases`
   │
   │ Note 1: h: n ≤ 3
   │
   │ Note 2: goal: False = True
   │
   │ Note 3: the goal isn't stuck on anything `cases` can take apart, and neither `rfl`, a contradiction, a hypothesis, `omega` nor deciding it (as `byDecision` does) proves it; give this case's proof as `cases in t`
   │
   │ Note 4: 2 other cases were closed (1 by computation, 1 by contradiction)
   │
   │ Note 5: this statement is false; a counterexample:
   │           a = True
   │           n = 3
   │         `(a && n <= 3) = True` holds
   │         `n ≤ 2` is false
───╯
1 error: in `atMostTwo`
```

Here the case `a = True` with `n ≤ 2` false is a real counterexample, `n = 3`: the hypothesis should say `n ≤ 2`. `cases` doesn't take apart lists or numbers, which is induction (written as recursion, above), and stops at 64 cases.

## Induction that follows a function

Induction on a list or a number is induction on the type. A function with an `if` in it has more cases than its type does: one for each branch. Every recursive function comes with an **induction principle** shaped like its own equations, and `match induct (f args)` proves a statement about a call of `f` by it. The goal is worked out from the statement, so the proof has one alternative for each branch of `f`, named after its equation (`eq2IfTrue` is the true branch of the `if` in arm 2), and each gets the variables of the branch, the fact the branch was taken under, and an induction hypothesis for each recursive call:

<!-- snippet: proofs.sw#induct -->
```stitchwort
def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if k ≤ x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length :=
  match induct (countAbove k xs) with
    | eq1 => omega
    | eq2IfTrue y ys h ih => ih
    | eq2IfFalse y ys h ih => omega

theorem skipsSmall (k: Nat) (x: Nat) (xs: List Nat) (h: (k <= x) = False): countAbove k [x, ..xs] = countAbove k xs :=
  countAbove.eq2.ifFalse k x xs h
```

Leaving an alternative as `?` shows what that branch has to prove, and what it can use:

<!-- snippet: errors/induct.sw -->
```stitchwort
def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if k ≤ x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length :=
  match induct (countAbove k xs) with
    | eq1 => omega
    | eq2IfTrue y ys h ih => ?
    | eq2IfFalse y ys h ih => omega
```

<!-- output: check errors/induct.sw -->
```text
[GOAL] Goal: in `countAboveLe`
   ╭─[ errors/induct.sw:8:30 ]
   │
 8 │     | eq2IfTrue y ys h ih => ?
   │                              ┬
   │                              ╰── k: Nat
   │                                  xs: List Nat
   │                                  y: Nat
   │                                  ys: List Nat
   │                                  h: k ≤ y
   │                                  ih: countAbove k ys ≤ ys.length
   │                                  ⊢ countAbove k ys ≤ ys.length
───╯
1 goal open
```

The names after the case bind its variables, then the condition it was taken under, then the induction hypotheses. Here `ih` is the statement for the tail `ys`. In the true branch the goal, once computed, is the same statement, so `ih` is the proof; in the false branch `omega` closes the goal from `ih`. Without `match induct`, the same proof is a function by cases on `xs` that also splits on the `if`.

The pieces are theorems you can use directly. Every arm of a definition gets an equation, `f.eq1`, `f.eq2`, …, and every `if` or `match` in tail position inside it gets one for each way through, named for the split (`countAbove.eq2.ifFalse`, `.some`, `.cons`). Each says what a call is when the branch was taken, taking the fact it was taken under as a hypothesis, as `skipsSmall` above does. These are most useful where the call is stuck on a condition, which `rfl` and `rewrite` can't compute through. The induction principle itself is `f.induct`, and `match induct` is shorthand for applying it. `stitchwort doc f` lists a function's equations, and marks those whose left side is stuck. Not every definition gets them (mutually recursive groups, and arms whose branches can't be stated, say so when named), and a definition that doesn't call itself has no `f.induct`. The rules are in [syntax.md](../syntax.md#generated-equations).

## Cases with conditions

A condition on a case ([chapter 3](03-data.md#conditions-on-cases)) is an `if` as far as proofs go. The arm that has it gets an equation with the condition as its last hypothesis, and each arm below it gets one with the fact that the condition failed:

<!-- snippet: proofs.sw#guard-eqs -->
```stitchwort
def cap (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

theorem capKeeps (limit: Nat) (n: Nat) (fits: n ≤ limit): cap limit n = n := cap.eq1 limit n fits

theorem capCuts (limit: Nat) (n: Nat) (over: (n <= limit) = False): cap limit n = limit := cap.eq2 limit n over

def skipThree: Nat → Nat
  | n if n != 3 => n
  | _ => 0

theorem skipThreeKeeps (n: Nat) (other: n ≠ 3): skipThree n = n := skipThree.eq1 n other

theorem skipThreeDrops: skipThree 3 = 0 := skipThree.eq2 3 rfl
```

`cap.eq1` has the hypothesis `n ≤ limit`, and `cap.eq2` has `(n <= limit) = False`. A condition on numbers or equality is stated as the proposition it decides, even when the program tests it as a `Bool`: `n != 3` gives `n ≠ 3`, and for the arm below it, `n = 3`. Another `Bool` is stated as `c = True`, and as `c = False` below. Equations are still numbered by arm, so a condition adds no name.

`match induct` splits at each condition too: the case of a guarded arm knows the condition, and the case of the arms below it knows it failed. The cases are named by arm, `eq1`, `eq2`, `eq3`, and `eq2` and `eq3` each get the fact; leaving `eq2` as `?` shows it:

<!-- snippet: proofs.sw#guard-induct -->
```stitchwort
def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMost (xs: List Nat): countBig xs ≤ xs.length :=
  match induct (countBig xs) with
    | eq1 => omega
    | eq2 x rest big ih => omega
    | eq3 x rest small ih => omega
```

<!-- snippet: errors/guard-induct.sw -->
```stitchwort
def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMost (xs: List Nat): countBig xs ≤ xs.length :=
  match induct (countBig xs) with
    | eq1 => omega
    | eq2 x rest big ih => ?
    | eq3 x rest small ih => omega
```

<!-- output: check errors/guard-induct.sw -->
```text
[GOAL] Goal: in `countBigAtMost`
   ╭─[ errors/guard-induct.sw:9:28 ]
   │
 9 │     | eq2 x rest big ih => ?
   │                            ┬
   │                            ╰── xs: List Nat
   │                                x: Nat
   │                                rest: List Nat
   │                                big: 4 ≤ x
   │                                ih: countBig rest ≤ rest.length
   │                                ⊢ countBig rest ≤ rest.length
───╯
1 goal open
```

Not every arm gets an equation. Where the right side computes on the proof of a condition, the equation isn't generated and naming it says why; prove that case by hand, with `f.unfold` or by matching on the condition. An arm that only passes the proof on, where nothing computes on it (as `Fin.ofNatLt n i h` takes `h: i < n`), gets its equation. The rules are in [syntax.md](../syntax.md), under "Guards".

## Decisions and facts

`Bool` and statements are different things. `n == 0` is a `Bool`, a value computed at run time. `n = 0` is a statement, a type whose values are proofs. A statement that can be **decided** (equations on types with `==`, comparisons on numbers) can be used as a condition, and then the branches know which way it went:

- `if n != 0 then a else b` makes the fact `n != 0` available in `a`, where an `auto` argument finds it: in `if n != 0 then Nat.modLt x n else …`, the lemma's `[auto ok: n ≠ 0]` is that fact ([chapter 2](02-values-and-definitions.md#dividing-by-zero)).
- `if a && b then …` gives the branch `a ∧ b`, and `auto` uses each part of a conjunction in scope: `if i < xs.length && j < xs.length then xs.getLt i` checks. It uses a fact about a test, such as the `(a && b) = True` a `match` on `a && b` gives, the same way: as what the test reads as (below). (When `b` itself needs the fact from `a`, as in `i < xs.length && xs.getLt i == x`, the branch doesn't get the conjunction.)
- `if h: P then a else b` also names the fact: `h: P` in `a`, and `h: ¬P` in `b`.
- A parameter `[auto ok: P]` asks the caller for a proof of `P`, found automatically from the facts in scope, or by deciding `P` when its values are known.

<!-- snippet: proofs.sw#decide -->
```stitchwort
def firstOr (fallback: Nat) (xs: List Nat): Nat :=
  if nonempty: 0 < xs.length then xs.headOr fallback else fallback

def safeAt (v: Vec Nat 3) (i: Nat): Option Nat :=
  if inRange: i < 3 then Some (v.getLt i) else None
```

`Vec.getLt` takes `[auto ok: i < n]`, so it can't be called out of range. Inside the `then` branch of `if inRange: i < 3`, the fact is in scope and `auto` finds it.

A `Bool` can be stated too. Where a statement is expected (after the colon, in a parameter's type, in `if h: …`, or beside `∧`, `∨`, `¬`, `→` and `↔`), a `Bool` `b` means `b = True`, the statement that it computes to `True`. `∧`, `∨` and `¬` there are always the statement operators, each `Bool` beside them read on its own: `isSmall m ∧ isSmall n` is `isSmall m = True ∧ isSmall n = True`.

<!-- snippet: proofs.sw#bool-statement -->
```stitchwort
def isSmall (n: Nat): Bool := n <= 3

theorem smallBoth (m: Nat) (n: Nat) (h: isSmall m ∧ isSmall n): isSmall n := h.right

theorem smallSame (n: Nat) (h: isSmall n): isSmall n = True := h
```

The two ways of writing it are the same statement, so `smallSame` is proved by `h` itself, and goals show `isSmall n = True` as `isSmall n`. The one place to write `= True` out is a fact about the `Bool` `a && b` itself, as a program's `if` hands it over: `(a && b) = True`, which goals show that way too, since `a && b` alone would mean `a ∧ b`. A side of `=` is never read as a statement, so `(a == b) = c` still compares `Bool`s.

A fact about a test can also be used as the statement the test stands for. A **reading** says what that is: a theorem `test ↔ P` marked `@[reading]`, declared next to the test's function. Then a fact `within lo x hi` is taken apart with `P`'s patterns, built with `P`'s constructors or record, and `h.read` is the whole fact as `P` (a field such as `h.read.low` can be written `h.low` too):

<!-- snippet: proofs.sw#readings -->
```stitchwort
type Within (lo: Nat) (x: Nat) (hi: Nat): Prop = {
  low: lo ≤ x,
  high: x ≤ hi
}

def within (lo: Nat) (x: Nat) (hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem withinReads (lo: Nat) (x: Nat) (hi: Nat): within lo x hi ↔ Within lo x hi := {
  forward = h => { low = h.left, high = h.right },
  backward = r => Both r.low r.high
}

theorem withinHigh (lo: Nat) (x: Nat) (hi: Nat) (h: within lo x hi): x ≤ hi :=
  match h with
    | { low, high } => high

theorem withinLow (lo: Nat) (x: Nat) (hi: Nat) (h: within lo x hi): lo ≤ x := h.read.low

theorem withinSelf (x: Nat): within x x x := { low = Nat.leRefl x, high = Nat.leRefl x }

theorem eitherSide (a: Bool) (b: Bool) (h: (a || b) = True): b ∨ a :=
  match h with
    | Inl ha => Inr ha
    | Inr hb => Inl hb
```

The library gives `&&`, `||` and `not` their readings: `(a && b) = True` reads as `a ∧ b`, `(a || b) = True` as `a ∨ b`, `not a = True` as `a = False`, and each `= False` as what you'd expect (`(a && b) = False` as `a = False ∨ b = False`). Each pattern reads one layer: `Both _ rest` leaves `rest` the fact `(b || c) = True`, and a pattern under it reads that in turn. A test whose function has no reading is unfolded to one that has, so `def isDigit (n: Nat): Bool := within 48 n 57` reads as `Within 48 n 57`. A fact `e = False` with no reading reads as `¬e`. Where nothing reads (`h: a = True` with `a` a variable), the error `E-NO-READING` says what the test is. A test has one reading for `= True` and one for `= False`, declared in the namespace (or library file) of its function. It can go anywhere there: whatever mentions the test is checked after its reading, except what the reading's own proof uses.

A decision's test needs no reading of its own. Where the decision is only known by its type, as `==` is on a type known only to have `DecEq`, a fact about its test reads as what it decides: `(a == b) = True` as `a = b`, and `(a == b) = False` as `a ≠ b`:

<!-- snippet: proofs.sw#readings-decisions -->
```stitchwort
theorem sameKey [auto eq: DecEq k] (a b c: k) (h: (a == b && b == c) = True): a = c :=
  match h with
    | Both ab bc => rewrite ab.read, bc.read in rfl

theorem differ [auto eq: DecEq k] (a b: k) (h: (a == b) = False): a ≠ b := h.read
```

`auto` and `cases` read the facts in scope the same way, so a fact about a test is used as what it reads as without a `.read`. A fact `xs.all p = True` reads as "every member of `xs` passes `p`", and `auto` applies that to a member it can see:

<!-- snippet: proofs.sw#readings-auto -->
```stitchwort
def small (x: Nat) [auto ok: x < 5]: Nat := x

def member (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: xs.all (x => x < 5) = True): Nat := small y

theorem inRight (x: Nat) (xs: List Nat) (b: Bool) (h: (b && xs.contains x) = True): x ∈ xs := cases
```

Given a fact where what it reads as is wanted, the error's note says what it reads as and to add `.read`. And when you write a decision of a statement that some test reads as, write it with that test, `{ holds = isSmall n, … }`, so `if Small n` and `if isSmall n` are the same computation; a decision that tests with another function gets the warning `W-DECISION-TEST`.

To use a condition in a proof, `match` on it. `match fits: e with` splits on the value of `e`, replaces `e` with that value in the goal, and names the equation `fits`:

<!-- snippet: proofs.sw#match-equation -->
```stitchwort
def clampTo (limit: Nat) (n: Nat): Nat := if n ≤ limit then n else limit

theorem clampToAtMost (limit: Nat) (n: Nat): clampTo limit n ≤ limit :=
  match fits: Nat.leq n limit with
    | True => fits
    | False => Nat.leRefl limit
```

`a <= b` used as a `Bool` is `Nat.leq a b`, so matching on `Nat.leq n limit` finds the `if`'s condition, and in each branch the `if` computes. With `?` in both branches, the goals show what's left:

<!-- snippet: errors/split-goals.sw@clampToAtMost -->
```stitchwort
theorem clampToAtMost (limit: Nat) (n: Nat): clampTo limit n ≤ limit :=
  match fits: Nat.leq n limit with
    | True => ?
    | False => ?
```

<!-- output: check errors/split-goals.sw -->
```text
[GOAL] Goal: in `clampToAtMost`
   ╭─[ errors/split-goals.sw:7:15 ]
   │
 7 │     | True => ?
   │               ┬
   │               ╰── limit: Nat
   │                   n: Nat
   │                   fits: n ≤ limit
   │                   ⊢ (if True = True then n else limit) ≤ limit
   │                     computes to n ≤ limit
───╯
[GOAL] Goal: in `clampToAtMost`
   ╭─[ errors/split-goals.sw:8:16 ]
   │
 8 │     | False => ?
   │                ┬
   │                ╰── limit: Nat
   │                    n: Nat
   │                    fits: (n <= limit) = False
   │                    ⊢ (if False = True then n else limit) ≤ limit
   │                      computes to limit ≤ limit
───╯
2 goals open
```

On `Nat`, the statement `a <= b` computes to `Nat.leq a b = True`, shown as `a ≤ b`, and the `Bool` `Nat.leq a b` alone as `a <= b`. Each goal is the statement with the branch's value put in (`if True = True then n else limit`), and the `computes to` line is what that computes to. In the `True` branch the computed goal is exactly `fits`, and in the `False` branch it is `limit ≤ limit`, which `Nat.leRefl limit` proves.

The `match` looks for `e` in the goal as you wrote it first, so where it finds every occurrence there, the branches keep the goal's calls: matching on `flag` in `(if flag then double a else 0) = …` leaves `double a = …` in the `True` branch, not `a + a = …`. Here the condition is only inside `clampTo`, so it is found in what `clampTo limit n` computes to, and the branches show that.

The `match` replaces `e` in the goal and in the hypotheses, but not in a lemma you call inside a branch: `clampToAtMost limit n` still says `clampTo limit n ≤ limit`, where the `True` branch's goal has `n ≤ limit`. Since they differ only in `e` against its value, the lemma's proof is rewritten along `fits` for you:

<!-- snippet: proofs.sw#match-lemma -->
```stitchwort
theorem clampToFits (limit: Nat) (n: Nat): clampTo limit n ≤ limit ∧ clampTo limit n ≤ n :=
  match fits: Nat.leq n limit with
    | True => Both (clampToAtMost limit n) (Nat.leRefl n)
    | False => Both (clampToAtMost limit n) omega
```

The lemma's type is searched for `e` as the goal is, so it fits even where it writes `e` differently, up to computation (`xs.map (y => f a y)` for `xs.map (f a)`). That needs the equation's name: in a `match` without one, the error says to add it. If the expression isn't in the goal at all, every arm gets the goal unchanged, and when an arm then fails the compiler warns (`W-MATCH-NOT-FOUND`), showing the goal as written: write the expression as the goal shows it, or bind it with a `let` first. The same goes the other way: a lemma's premise `Nat.leq n limit = True`, written in the `True` branch, is proved by `fits`, which says exactly that, and `rfl` can't prove it.

To split on an `if`, match on its condition. Matching on the comparison's decision (`match Nat.decLessThan n limit with | { holds = True, sound = s, complete = _ } => … | { holds = False, … } => …`) refines the `if` as well, and also gives you evidence: `s rfl` proves `n < limit` in the first arm (`examples/accept/match-decision-refines-if.sw`).

## Membership, "if and only if", "there exists", "for all"

Three more forms come up in statements, each with a Unicode spelling you may use instead:

<!-- snippet: proofs.sw#logic -->
```stitchwort
theorem headIn (x: Nat) (rest: List Nat): x ∈ [x, ..rest] := Inl rfl

theorem notInEmpty (x: Nat): x ∉ [] := none => none

theorem bothWays (p: Prop) (q: Prop): p ∧ q ↔ q ∧ p := {
  forward = h => Both (And.right h) (And.left h),
  backward = h => Both (And.right h) (And.left h)
}

theorem hasSquareRoot: ∃ (n: Nat) => n * n = 49 := Witness 7 rfl

def unseen (seen: List Nat) (xs: List Nat): List Nat := xs.filter (x => x ∉ seen)
```

- `x in xs` (or `x ∈ xs`) says `x` is in the list `xs`; `x !in xs` (`x ∉ xs`) says it isn't. On a `Set`, or the keys of a `Map`, it works the same way. As a condition, membership is decided like `<=`: `xs.filter (x => x !in seen)` keeps what hasn't been seen.
- `p <-> q` (`p ↔ q`) says each implies the other. A proof is a record of the two directions, `forward` and `backward`.
- `exists (n: Nat) => P` (`∃ (n: Nat) => P`) says some `n` makes `P` true. A proof is a `Witness`: the value, and a proof that it works.

The other Unicode spellings are `→ ∧ ∨ ¬ ≤ ≥ ≠` for `-> && || ! <= >= !=`. They mean exactly the same as the ASCII. Messages show a statement in the Unicode forms (`n ≤ limit`, `a ∧ b`) and a `Bool` computation in ASCII (`(n <= limit) = False`, `a && b`), whichever you wrote, so a message tells you which of the two you have. [The syntax reference](../syntax.md#logic-notation-in--and-exists) has the full list and the precedence table.

"For all" has a form of its own too:

<!-- snippet: proofs.sw#forall -->
```stitchwort
theorem zeroPlusAll: ∀ (n: Nat) => 0 + n = n := n => rfl

theorem atOneAndTwo (p: Nat -> Prop) (all: ∀ (n: Nat) => p n): p 1 ∧ p 2 := Both (all 1) (all 2)

theorem swapSum (comm: ∀ (a b: Nat) => a + b = b + a): 2 + 5 = 5 + 2 := comm 2 5
```

`forall (n: Nat) => P` (`∀ (n: Nat) => P`) says `P` holds for every `n`. It's another way to write the function type `(n: Nat) -> P`, so a proof of it is a function from each `n` to a proof of `P`, and using one is a call: `all 1` is a proof of `p 1`. Several parameters go together, as in `∀ (a b: Nat) => …`, and like `exists` the statement runs to the end, so `∀ (n: Nat) => n > 0 -> P n` says `P n` for every positive `n`.

Write `∀` for a hypothesis that is about every value, as `all` and `comm` are, and for a statement after the colon. A theorem's own parameters stay parameters: `theorem zeroPlus (n: Nat): 0 + n = n` and `theorem zeroPlusAll: ∀ (n: Nat) => 0 + n = n` state the same thing, and the first reads better when the proof starts from `n`. Goals and messages show a function type whose result is plainly a statement with `∀`, however it was written ([the syntax reference](../syntax.md#logic-notation-in--and-exists) says when).

## Types that mention values

A type can mention values: `Vec Nat 3` is a list of exactly three numbers, and `Fin 3` a number below 3. A function's type can then say more than its name does, and the checker holds callers to it:

<!-- snippet: proofs.sw#dependent -->
```stitchwort
def pick (v: Vec Nat 3): Nat := v.get 2

theorem pickTrio: pick (VCons 1 (VCons 2 (VCons 3 VNil))) = 3 := rfl
```

`v.get 2` needs a `Fin 3`; a `2` is accepted because it's below 3, and `v.get 3` would be an error. A proof is just the most extreme case of this: a type that mentions values, such as `x + 1 <= 10`, with no data in it. You'll find proofs inside ordinary types too, as fields: `type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }` is a number that is known to be in range, everywhere it goes. Reading the field, `d.inRange`, gives that proof at its type as the record declares it, `d.position <= highest`: hovers and messages show a field's type as written, not what the definitions in it compute to.

## A specification and its program

The useful theorems say that a program meets a **specification**: a definition that is obviously right, even if it's slow. Here the specification is the plain recursive sum, the program a loop with an accumulator, and the theorem says they agree on every input:

<!-- snippet: proofs.sw#spec -->
```stitchwort
-- The specification: the plain recursive sum.
def sumTo: Nat → Nat
  | 0 => 0
  | Succ k => Succ k + sumTo k

-- The program: a loop with an accumulator.
def sumFast (n: Nat): Nat :=
  def loop: Nat → Nat → Nat
    | 0, total => total
    | Succ k, total => loop k (total + Succ k)
  loop n 0

-- What the loop computes, for any accumulator: the general statement is
-- what makes the induction go through.
theorem loopIsSum (n: Nat) (total: Nat): sumFast.loop n total = total + sumTo n := match n, total with
  | Zero, total => rfl
  | Succ k, total => omega [loopIsSum k (total + Succ k)]

theorem sumFastIsSum (n: Nat): sumFast n = sumTo n := loopIsSum n 0
```

The proof shows a common move: the statement about `sumFast` alone isn't provable by induction, because `loop` is called with a changing accumulator. So the lemma `loopIsSum` states what `loop` computes for *every* accumulator, and the main theorem is the case `total = 0`. In the `Succ` case, `sumFast.loop (Succ k) total` computes to `sumFast.loop k (total + Succ k)`, the hypothesis says what that is, and `omega` does the arithmetic.

Two habits help:

- **Prove the function callers use.** The theorem is about `sumFast`, the function the program exports, not just about its inner loop. A proof about a helper says nothing about a wrapper that calls it wrongly.
- **State the specification the way the problem does**, even if it's slow, and let the proof bridge the gap. If the specification is clever, it can be wrong in the same way as the program.

The same applies to exported functions ([chapter 11](11-running-and-shipping.md)), which are where a theorem is worth most:

<!-- snippet: proofs.sw#export -->
```stitchwort
export def clampPercent (n: Nat): Nat := clampTo 100 n

theorem clampPercentAtMost (n: Nat): clampPercent n ≤ 100 := clampToAtMost 100 n
```

## Hiding a definition: `opaque`

The checker looks inside definitions: `rfl` computes through them, and so does every later proof, even when the body is long or only an implementation detail. An `opaque def` is checked and run like any other, but other declarations see only its name and type. A call is equal to another call only through its arguments:

<!-- snippet: errors/opaque.sw -->
```stitchwort
opaque def checksum (xs: List Nat): Nat := xs.foldLeft 0 (sum x => (sum * 31 + x) % 65521)

theorem checksumNil: checksum [] = 0 := rfl
```

<!-- output: check errors/opaque.sw -->
```text
[E-REFL] Error: `rfl` can't prove this
   ╭─[ errors/opaque.sw:3:41 ]
   │
 3 │ theorem checksumNil: checksum [] = 0 := rfl
   │                                         ─┬─
   │                                          ╰─── `checksum []` and `0` aren't equal
   │
   │ Note 1: `rfl` proves `a = b` only when both sides compute to the same value
   │
   │ Note 2: `checksum` is opaque, so its body isn't used here
   │
   │ Note 3: add `unfolding checksum` after this declaration's signature, or rewrite with `checksum.unfold`
───╯
1 error: in `checksumNil`
```

A declaration that needs the body says so with `unfolding` after its type, or rewrites with the equation `checksum.unfold`:

<!-- snippet: proofs.sw#opaque -->
```stitchwort
opaque def checksum (xs: List Nat): Nat := xs.foldLeft 0 (sum x => (sum * 31 + x) % 65521)

theorem checksumNil: checksum [] = 0 unfolding checksum := rfl

test "checksum" := checksum [1, 2] == 33
```

The program still runs the body, and the test uses it. What opacity changes is what other proofs can see: one that doesn't say `unfolding` can't depend on the body, and its check doesn't have to compute through it. `unfolding` is for a theorem or another `opaque def`, and not for a plain `def`, whose body is always visible.

## Proofs about effectful code

A handler applied to a computation of a known shape computes, so many facts about effectful code are `rfl` ([chapter 8](08-abilities.md)). A law about *any* computation needs to split on what the computation does. `match reify t with` does that, with clauses written as a handler's: one for finishing with a value, and one per operation:

<!-- snippet: proofs.sw#reify -->
```stitchwort
theorem orElseIsGetOrElse (fallback: a) (t: () → {Fail} a): Fail.orElse fallback t = (Fail.toOption t).getOrElse fallback :=
  match reify t with
    | return x => rfl
    | Fail.stop message, _ => rfl
```

In each clause, the computation in the goal is replaced by what it did, and both handlers compute. `reify` is only allowed in proofs: a program can run a computation or hand it to a handler, but can't look inside it.

## The goal at any point, from the command line

To see what a step of a finished proof has to prove, without editing it, ask for the goal at a line and column (counted from 1):

```sh
stitchwort goal --at proofs.sw:42:5
stitchwort goal --at proofs.sw:42        # the line's first character
stitchwort goal --at proofs.sw:42 --json # the same, for a script
```

```
proofs.sw:42:5
in `swapSum`
  a: Nat
  b: Nat
  ⊢ b + a = b + a
```

It names the declaration, then prints the names in scope and `⊢` the goal in a proof, or `expected T` in program code (with `has type U` below it when the expression's own type is different). The point can be anywhere inside an expression: in the body of a `rewrite`, you get the goal after the rules before it; on an expression that fails to check, the goal it was meant to prove.

On a step of a proof, where the goal changes, it shows the goal before the step and after it. A rule of a `rewrite` chain shows the rule as it was used between the two:

```
proofs.sw:12:26
in `multN0M0`, rule 2 of 2 of `rewrite`
  p: Nat
  q: Nat
  before ⊢ q * 0 = 0
  rule   q * 0 = 0
  after  ⊢ 0 = 0
```

The cursor on a rule's `rewrite`, `at` or `in` shows the same step as on the rule itself (with several rules, the first rule's). The other steps are an arm's pattern (the `match`'s goal before, the arm's after, and its pattern's variables marked `+`), a line of a `calc` (what the lines before it prove, and the line's own statement), a lambda's parameter, a `let`'s name, the `then` and `else` of `if h:`, and the signature (the statement to prove, with the parameters). The editor's Goals panel shows the same.

It exits with 0 with an answer and 2 with none (a comment, a blank line, between declarations), and checks the file as `check` does, so it takes as long as that. A file of a project is read in the project from any folder.

## Checking one theorem

In a project with many theorems, `stitchwort check --only` checks just the ones you name, by full name, and the theorems they use:

```sh
stitchwort check --only Shop.Proofs.totalNonNegative
stitchwort check Shop.Proofs --only Shop.Proofs.totalNonNegative,Shop.Proofs.discountBounded
```

The other theorems of those namespaces are left unchecked, and the command says so in its last line (`checked 2 of 49 theorems of the namespaces named: the other 47 were NOT checked`), so it is never mistaken for a full check. Definitions, tests and the namespaces the proofs use are checked as usual. A name that is not a theorem is an error. Run a plain `stitchwort check` before you rely on the result: `--only` is for working on a theorem, and for timing it.

## Axioms

A proof is only as good as what it assumes. Stitchwort has one axiom, `Quot.sound` (that equal elements of a quotient type are equal), and `stitchwort axioms` lists the axioms a theorem depends on, through everything it uses:

<!-- output: axioms proofs.sw sumFastIsSum -->
```text
no axioms are used
```

Nothing: the proof assumes nothing. Function extensionality (two functions that agree on every input are equal) is a theorem, proved from `Quot.sound`, so a proof that uses it shows the axiom:

<!-- snippet: proofs.sw#funext -->
```stitchwort
theorem doubleIsTimesTwo: double = (n => 2 * n) := Quot.funext Nat (n => Nat) double (n => 2 * n) twiceIsDouble
```

<!-- output: axioms proofs.sw doubleIsTimesTwo -->
```text
Quot.sound
```

`stitchwort axioms` answers for one theorem. A theorem can also check and still be worth little: a lemma it uses may be an unfinished `?`, or its hypotheses may contradict each other, so that it proves its conclusion only for inputs that don't exist (`theorem vacuous (n: Nat) (h: n + 1 = 0): n = 42 := omega` checks). `stitchwort audit` looks at every theorem of a file, a namespace or a project for these and for axioms you didn't allow, and prints a line for each one with a finding:

<!-- output: audit proofs.sw sumFastIsSum -->
```text
audited 1 theorem: 0 failed, 0 with warnings, 1 passed
```

A project can narrow the allowed axioms in its `stitchwort.yaml` ([projects.md](../projects.md)). A warning about hypotheses means the counterexample search found no input that satisfies them, which is evidence and not proof, so read the statement. [syntax.md](../syntax.md#auditing-theorems-stitchwort-audit) has the rest.

## A worked example: Advent of Code 2025, day 1

The [aoc/](../../aoc/) project solves Advent of Code puzzles and proves the answers right. Day 1 turns a dial numbered 0 to 99, starting at 50, and part 2 asks how many clicks land on 0 during a list of turns. The program counts them with arithmetic, one turn at a time:

<!-- snippet: ../../../aoc/src/Aoc/Year2025/Day01/Day01.sw@zerosPassed,Dial.zerosDuring -->
```stitchwort
def zerosPassed (turns: List Turn) (startingDial: Dial n): Nat :=
  turns
    |> .scanLeft startingDial .move
    |> .zipWith turns .zerosDuring
    |> .sum

def Dial.zerosDuring [n: Nat] (dial: Dial n): Turn → Nat
  | Right distance => (dial.position.value + distance) / Mod.size n
  | Left distance => ((Mod.size n - dial.position.value) % Mod.size n + distance) / Mod.size n
```

That arithmetic is easy to get wrong. The specification, in its own namespace, says what the puzzle says: turn the dial one click at a time, and count the clicks that land on 0:

<!-- snippet: ../../../aoc/src/Aoc/Year2025/Day01/Spec/Spec.sw -->
```stitchwort
--| Day 1, part 2 as the puzzle states it: turn the dial one click at a time, and
--| count the positions after each click that are 0. The proofs (Proofs/Part2.sw)
--| and the tests (Tests/Spec.sw) compare the program's arithmetic count with it.

namespace Aoc.Year2025.Day01.Spec
import Aoc.Year2025.Day01 (..)
import Std (List, Nat)

--| The specification of part 2: turn the dial one click at a time, and count
--| the positions after each click that are 0.
def zerosPassedSpec (turns: List Turn) (startingDial: Dial n): Nat :=
  turns |> .concatMap Turn.clicks |> zerosLandedOn startingDial
```

The theorem, in `Aoc.Year2025.Day01.Proofs`, says they agree for a dial of any size, any start and any turns, and so for the puzzle's answer:

<!-- snippet: ../../../aoc/src/Aoc/Year2025/Day01/Proofs/Part2.sw@zerosPassedCorrect,part2Puzzle -->
```stitchwort
theorem zerosPassedCorrect [n: Nat] (startingDial: Dial n) (turns: List Turn): zerosPassed turns startingDial = zerosPassedSpec turns startingDial :=
  zerosPassedFrom startingDial turns

theorem part2Puzzle (turns: List Turn): solvePart2 turns = zerosPassedSpec turns Dial.start :=
  zerosPassedCorrect Dial.start turns
```

The proof ([Proofs/Part2.sw](../../aoc/src/Aoc/Year2025/Day01/Proofs/Part2.sw)) is about 130 lines: induction on the turns, a lemma for one turn split into clicks, and arithmetic lemmas about one click, with `calc`, `rewrite` and `omega` doing the steps. The day is laid out the way the other days are:

- `Aoc/Year2025/Day01/Day01.sw`, namespace `Aoc.Year2025.Day01`: the program, `parseTurns`, `solvePart1`, `solvePart2` and `main`;
- `Spec/Spec.sw`, `Aoc.Year2025.Day01.Spec`: the specification, written the way the puzzle states it;
- `Proofs/`, `Aoc.Year2025.Day01.Proofs`: the theorems, about the parsed model of the input rather than its text;
- `Tests/`, `Aoc.Year2025.Day01.Tests`: the puzzle's example, edge cases, and the real input through `include`.

`stitchwort run Aoc.Year2025.Day01.main` checks only the program; `stitchwort test Aoc.Year2025.Day01` checks the proofs and runs the tests. [docs/aoc-2025.md](../aoc-2025.md) describes each day's proofs and what was hard about them.

More: [syntax.md](../syntax.md) sections [Goals](../syntax.md#goals-), [`calc`](../syntax.md#calc), [`rewrite`](../syntax.md#rewrite), [`omega`](../syntax.md#omega), [`ring`](../syntax.md#ring), [`match`](../syntax.md#match), [Proofs about effectful code](../syntax.md#proofs-about-effectful-code); the design notes [calc-rewrite.md](../proposals/calc-rewrite.md), [omega.md](../proposals/omega.md), [proof-reification.md](../proposals/proof-reification.md) and [indexed-families.md](../proposals/indexed-families.md).
