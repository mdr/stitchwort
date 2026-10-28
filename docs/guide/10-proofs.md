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
```

The last note comes from a **counterexample search**: when a proof fails, the checker also tries the statement itself on inputs, small ones first, then random ones. Here there are no inputs to try, and the statement computes to false, so no proof could work. A search that finds nothing says nothing.

A theorem is erased when the program runs: it costs nothing. In a project, `stitchwort run` doesn't even check the namespaces it doesn't need, which is why proofs usually have a namespace of their own.

## Induction is recursion

`n + 0 = n` is true, but `rfl` can't prove it for an unknown `n`: `+` recurses on its first argument, and `n` isn't a known number. The proof goes by cases on `n`, like a function with arms:

<!-- snippet: proofs.sw#induction -->
```stitchwort
theorem plusZero: (n: Nat) → n + 0 = n
  | Zero => rfl
  | Succ k => Eq.cong Succ (plusZero k)
```

In the `Zero` arm the statement is `0 + 0 = 0`, which computes. In the `Succ k` arm it is `Succ k + 0 = Succ k`, which computes to `Succ (k + 0) = Succ k`. The recursive call `plusZero k` proves `k + 0 = k`: this is the induction hypothesis, and calling the theorem on a smaller value is how induction is written. The compiler checks that it terminates, like any recursion. `Eq.cong Succ` turns `x = y` into `Succ x = Succ y`.

The skill is in reading what each case needs. Using the induction hypothesis directly gives a message that shows it:

<!-- snippet: errors/induction.sw -->
```stitchwort
import Std (Eq)

theorem plusZero: (n: Nat) → n + 0 = n
  | Zero => rfl
  | Succ k => plusZero k
```

<!-- output: check errors/induction.sw -->
```text
[E-TYPE-MISMATCH] Error: type mismatch
   ╭─[ errors/induction.sw:5:15 ]
   │
 5 │   | Succ k => plusZero k
   │               ─────┬────
   │                    ╰────── expected `Succ (k + 0) = Succ k`, but this has type `k + 0 = k`
───╯
```

## Goals: `?`

You don't have to know what a case needs before writing it. Put `?` where a proof (or any expression) is missing, and the checker reports the **goal**: the names in scope with their types, and after `⊢`, what has to go there:

<!-- snippet: errors/hole.sw -->
```stitchwort
import Std (Eq)

theorem plusZero: (n: Nat) → n + 0 = n
  | Zero => rfl
  | Succ k => ?
```

<!-- output: check errors/hole.sw -->
```text
[GOAL] Goal: in `plusZero`
   ╭─[ errors/hole.sw:5:15 ]
   │
 5 │   | Succ k => ?
   │               ┬
   │               ╰── k: Nat
   │                   ⊢ Succ (k + 0) = Succ k
───╯
1 goal open: the declarations with them, and what uses them, aren't finished, so they aren't checked
```

A declaration with a `?` isn't an error, but it isn't finished either: it isn't checked, and `check` fails until every goal is closed. You can state a lemma with `?` as its proof and use it in the main theorem first, then come back to it. In the editor, the goal shows on hover, and "Stitchwort: Show Goals" opens a panel that follows the cursor.

The goal is shown computed, as the checker sees it, so it is often a step further along than what you wrote: `Succ (k + 0)`, not `Succ k + 0`.

## Proofs about lists

The same pattern works for any recursive type. A proof about lists has a `[]` case and a `Cons` case:

<!-- snippet: proofs.sw#lists -->
```stitchwort
def mapList (f: a → b): List a → List b
  | [] => []
  | Cons x rest => Cons (f x) (mapList f rest)

theorem lengthMapList (f: a → b): (xs: List a) → (mapList f xs).length = xs.length
  | [] => rfl
  | Cons x rest => Eq.cong Succ (lengthMapList f rest)
```

`(mapList f xs).length` in the `Cons` case computes to `Succ (mapList f rest).length`, so `Eq.cong Succ` of the hypothesis is the proof.

## Rewriting and chains

`rewrite p in t` uses an equation `p: a = b` to replace `a` with `b` in the goal, then proves what's left with `t`. With no `in`, what's left must hold by computing. Several rules are applied in order:

<!-- snippet: proofs.sw#rewrite -->
```stitchwort
theorem swapWithZero (a: Nat) (b: Nat): a + b + 0 = b + a :=
  rewrite Nat.addZero (a + b), Nat.addComm a b
```

`Nat.addZero (a + b)` turns `a + b + 0` into `a + b`, and `Nat.addComm a b` turns `a + b` into `b + a`, leaving `b + a = b + a`. The library's lemmas are named after what they say: `Nat.addComm`, `Nat.addAssoc`, `List.lengthMap`, `List.lengthAppend`. `rewrite <- p` rewrites from right to left, and `rewrite p at h` rewrites the type of a hypothesis `h` instead of the goal. `rewrite` also goes inside a function passed as an argument, through the congruence lemma of the function it is passed to: `rewrite Nat.addZero _` proves `List.map xs (x => x + 0) = List.map xs (x => x)` by `List.mapCong`, with `_` standing for `x`. Arguments left off a rule's end are filled in the same way, and a premise the rule needs, such as `x <= n` for `Nat.addSubCancel x n`, is proved by a hypothesis or by `omega`; inside `List.sumBy f (List.range n)` the congruence lemma also says that `x` is below `n`, which proves it, so `rewrite Nat.addSubCancel` turns `x + (n - x)` into `n` there.

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
```

On `Int`, an unknown may be negative, while `n.toInt` of a `Nat` is known to be at least 0, so `Nat` and `Int` facts mix; `x / 3` and `x % 3` are unknowns with `3 * (x / 3) + x % 3 = x` and `0 ≤ x % 3 < 3`. `omega [p, q]` adds the facts `p` and `q`, such as lemmas applied to arguments. Anything that isn't linear arithmetic (`x * y`, `xs.length`, a function call) is treated as an unknown number. When `omega` fails, it says which facts it used and gives values that satisfy them but not the goal, which usually points at the missing fact:

<!-- snippet: errors/omega.sw -->
```stitchwort
theorem roomForOne (x: Nat) (y: Nat) (before: x ≤ y) (limit: y ≤ 10): x + 1 ≤ 10 := omega
```

<!-- output: check errors/omega.sw -->
```text
[E-OMEGA] Error: `omega` can't prove `x + 1 ≤ 10`
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
[E-CASES] Error: `cases` can't close the case a = True, (n <= 2) = False
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
   │ Note 3: the goal isn't stuck on anything `cases` can take apart, and neither `rfl`, a contradiction, a hypothesis nor `omega` proves it; give this case's proof as `cases in t`
   │
   │ Note 4: 2 other cases were closed (1 by computation, 1 by contradiction)
   │
   │ Note 5: this statement is false; a counterexample:
   │           a = True
   │           n = 3
   │         `(a && n <= 3) = True` holds
   │         `n ≤ 2` is false
───╯
```

Here the case `a = True` with `n ≤ 2` false is a real counterexample, `n = 3`: the hypothesis should say `n ≤ 2`. `cases` doesn't take apart lists or numbers, which is induction (written as recursion, above), and stops at 64 cases.

## Decisions and facts

`Bool` and statements are different things. `n == 0` is a `Bool`, a value computed at run time. `n = 0` is a statement, a type whose values are proofs. A statement that can be **decided** (equations on types with `==`, comparisons on numbers) can be used as a condition, and then the branches know which way it went:

- `if n != 0 then a else b` makes the fact `n != 0` available in `a`. That's how `/` found its proof in [chapter 2](02-values-and-definitions.md#division-needs-a-reason).
- `if h: P then a else b` also names the fact: `h: P` in `a`, and `h: Not P` in `b`.
- A parameter `[auto ok: P]` asks the caller for a proof of `P`, found automatically from the facts in scope, or by deciding `P` when its values are known.

<!-- snippet: proofs.sw#decide -->
```stitchwort
def firstOr (fallback: Nat) (xs: List Nat): Nat :=
  if nonempty: 0 < xs.length then xs.headOr fallback else fallback

def safeAt (v: Vec Nat 3) (i: Nat): Option Nat :=
  if inRange: i < 3 then Some (v.getLt i) else None
```

`Vec.getLt` takes `[auto ok: i < n]`, so it can't be called out of range. Inside the `then` branch of `if inRange: i < 3`, the fact is in scope and `auto` finds it.

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
   │                   ⊢ n ≤ limit
───╯
[GOAL] Goal: in `clampToAtMost`
   ╭─[ errors/split-goals.sw:8:16 ]
   │
 8 │     | False => ?
   │                ┬
   │                ╰── limit: Nat
   │                    n: Nat
   │                    fits: (n <= limit) = False
   │                    ⊢ limit ≤ limit
───╯
2 goals open: the declarations with them, and what uses them, aren't finished, so they aren't checked
```

On `Nat`, the statement `a <= b` computes to `Nat.leq a b = True`, and goals are shown computed: that is shown as `a ≤ b`, and the `Bool` `Nat.leq a b` alone as `a <= b`. In the `True` branch the goal is then exactly `fits`, and in the `False` branch it is `limit <= limit`, which `Nat.leRefl limit` proves.

## Membership, "if and only if", "there exists"

Three more forms come up in statements, each with a Unicode spelling you may use instead:

<!-- snippet: proofs.sw#logic -->
```stitchwort
theorem headIn (x: Nat) (rest: List Nat): x ∈ Cons x rest := Inl rfl

theorem notInEmpty (x: Nat): x ∉ Nil := none => none

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

The other Unicode spellings are `→ ∧ ∨ ¬ ≤ ≥ ≠` for `-> && || ! <= >= !=`. They mean exactly the same as the ASCII, and messages show the Unicode forms whichever you wrote. To say "for all", use a parameter: `(x: Nat) -> P`. [The syntax reference](../syntax.md#logic-notation-in--and-exists) has the full list and the precedence table.

## Types that mention values

A type can mention values: `Vec Nat 3` is a list of exactly three numbers, and `Fin 3` a number below 3. A function's type can then say more than its name does, and the checker holds callers to it:

<!-- snippet: proofs.sw#dependent -->
```stitchwort
def pick (v: Vec Nat 3): Nat := v.get 2

theorem pickTrio: pick (VCons 1 (VCons 2 (VCons 3 VNil))) = 3 := rfl
```

`v.get 2` needs a `Fin 3`; a `2` is accepted because it's below 3, and `v.get 3` would be an error. A proof is just the most extreme case of this: a type that mentions values, such as `x + 1 <= 10`, with no data in it. You'll find proofs inside ordinary types too, as fields: `type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }` is a number that is known to be in range, everywhere it goes.

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
theorem loopIsSum: (n: Nat) → (total: Nat) → sumFast.loop n total = total + sumTo n
  | Zero, total => Eq.sym (Nat.addZero total)
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
-- Day 1, part 2 as the puzzle states it: turn the dial one click at a time, and
-- count the positions after each click that are 0. The proofs (Proofs/Part2.sw)
-- and the tests (Tests/Spec.sw) compare the program's arithmetic count with it.

namespace Aoc.Year2025.Day01.Spec
import Aoc.Year2025.Day01 (..)
import Std (List, Nat)

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
def zerosPassedSpec (turns: List Turn) (startingDial: Dial n): Nat :=
  turns |> .concatMap Turn.clicks |> zerosLandedOn startingDial
```

The theorem, in `Aoc.Year2025.Day01.Proofs`, says they agree for a dial of any size, any start and any turns, and so for the puzzle's answer:

<!-- snippet: ../../../aoc/src/Aoc/Year2025/Day01/Proofs/Part2.sw@zerosPassedCorrect,part2Puzzle -->
```stitchwort
theorem zerosPassedCorrect [n: Nat] (startingDial: Dial n) (turns: List Turn): zerosPassed turns startingDial = zerosPassedSpec turns startingDial :=
  zerosPassedFrom startingDial turns

theorem part2Puzzle (turns: List Turn): solvePart2 turns = zerosPassedSpec turns startingDial :=
  zerosPassedCorrect startingDial turns
```

The proof ([Proofs/Part2.sw](../../aoc/src/Aoc/Year2025/Day01/Proofs/Part2.sw)) is about 130 lines: induction on the turns, a lemma for one turn split into clicks, and arithmetic lemmas about one click, with `calc`, `rewrite` and `omega` doing the steps. The day is laid out the way the other days are:

- `Aoc/Year2025/Day01/Day01.sw`, namespace `Aoc.Year2025.Day01`: the program, `parseTurns`, `solvePart1`, `solvePart2` and `main`;
- `Spec/Spec.sw`, `Aoc.Year2025.Day01.Spec`: the specification, written the way the puzzle states it;
- `Proofs/`, `Aoc.Year2025.Day01.Proofs`: the theorems, about the parsed model of the input rather than its text;
- `Tests/`, `Aoc.Year2025.Day01.Tests`: the puzzle's example, edge cases, and the real input through `include`.

`stitchwort run Aoc.Year2025.Day01.main` checks only the program; `stitchwort test Aoc.Year2025.Day01` checks the proofs and runs the tests. [docs/aoc-2025.md](../aoc-2025.md) describes each day's proofs and what was hard about them.

More: [syntax.md](../syntax.md) sections [Goals](../syntax.md#goals-), [`calc`](../syntax.md#calc), [`rewrite`](../syntax.md#rewrite), [`omega`](../syntax.md#omega), [`ring`](../syntax.md#ring), [`match`](../syntax.md#match), [Proofs about effectful code](../syntax.md#proofs-about-effectful-code); the design notes [calc-rewrite.md](../proposals/calc-rewrite.md), [omega.md](../proposals/omega.md), [proof-reification.md](../proposals/proof-reification.md) and [indexed-families.md](../proposals/indexed-families.md).
