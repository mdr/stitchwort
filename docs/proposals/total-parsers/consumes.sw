-- Option (a) of total-parsers.md: Idris 2's `Grammar (consumes: Bool)` as
-- a Stitchwort data type. A parser is a function on the input whose reply
-- carries a proof of how much it read: less than the input if `consumes`,
-- no more than the input otherwise. `many` takes only a parser that
-- consumes, so `many (optional p)` is a type error.
import Std (Bool, Char, List, Nat, Option, Text, Void)

-- What a reply's rest may be: shorter than the input if the parser
-- consumes, no longer otherwise.
def Within: Bool → Nat → Nat → Prop
  | True, rest, input => rest < input
  | False, rest, input => rest ≤ input

-- Whether a sequence consumes: if either part does. Matching on the first
-- argument, so `eitherConsumes True c` is `True` without knowing `c`.
def eitherConsumes: Bool → Bool → Bool
  | True, c => True
  | False, c => c

-- Whether a choice consumes: if both alternatives do.
def bothConsume: Bool → Bool → Bool
  | True, c => c
  | False, c => False

type Reply (consumes: Bool) (input: List Char) (a: Type) =
  | Got (value: a) (rest: List Char) (within: Within consumes rest.length input.length)
  | Missed (expected: Text)

type Parser (consumes: Bool) (a: Type) = { run: (input: List Char) → Reply consumes input a }

-- The lemmas the combinators need. Users never see them.
theorem Within.weaken: (c: Bool) → (r: Nat) → (n: Nat) → Within c r n → r ≤ n
  | True, r, n, h => Nat.lessLe r n h
  | False, r, n, h => h

theorem Within.seq: (c1: Bool) → (c2: Bool) → (r2: Nat) → (r1: Nat) → (n: Nat) → Within c1 r1 n → Within c2 r2 r1 →
    Within (eitherConsumes c1 c2) r2 n
  | True, c2, r2, r1, n, h1, h2 => Nat.leTrans (Succ r2) (Succ r1) n (Within.weaken c2 r2 r1 h2) h1
  | False, True, r2, r1, n, h1, h2 => Nat.leTrans (Succ r2) r1 n h2 h1
  | False, False, r2, r1, n, h1, h2 => Nat.leTrans r2 r1 n h2 h1

theorem Within.left: (c1: Bool) → (c2: Bool) → (r: Nat) → (n: Nat) → Within c1 r n → Within (bothConsume c1 c2) r n
  | True, True, r, n, h => h
  | True, False, r, n, h => Nat.lessLe r n h
  | False, c2, r, n, h => h

theorem Within.right: (c1: Bool) → (c2: Bool) → (r: Nat) → (n: Nat) → Within c2 r n → Within (bothConsume c1 c2) r n
  | True, c2, r, n, h => h
  | False, c2, r, n, h => Within.weaken c2 r n h

-- The pieces.

def pure (value: a): Parser False a := { run = input => Got value input (Nat.leRefl input.length) }

def failWith (what: Text): Parser c a := { run = input => Missed what }

def satisfy (what: Text) (passes: Char → Bool): Parser True Char := { run = input =>
  match input with
    | Cons char rest => if passes char then Got char rest (Nat.leRefl (Succ rest.length)) else Missed what
    | Nil => Missed what }

def char (expected: Char): Parser True Char := satisfy "'${Text.fromList [expected]}'" (== expected)

-- Sequencing: `p`, then the parser its value chooses. Consumes if either
-- does.
def seq [c1 c2: Bool] (p: Parser c1 a) (next: a → Parser c2 b): Parser (eitherConsumes c1 c2) b := { run = input =>
  match p.run input with
    | Missed what => Missed what
    | Got x rest h1 =>
      match (next x).run rest with
        | Missed what => Missed what
        | Got y after h2 => Got y after (Within.seq c1 c2 after.length rest.length input.length h1 h2) }

def map (p: Parser c a) (f: a → b): Parser c b := { run = input =>
  match p.run input with
    | Missed what => Missed what
    | Got x rest h => Got (f x) rest h }

-- Choice, backing up: consumes if both alternatives do.
def alt [c1 c2: Bool] (p: Parser c1 a) (q: Parser c2 a): Parser (bothConsume c1 c2) a := { run = input =>
  match p.run input with
    | Got x rest h => Got x rest (Within.left c1 c2 rest.length input.length h)
    | Missed first =>
      match q.run input with
        | Got y rest h => Got y rest (Within.right c1 c2 rest.length input.length h)
        | Missed second => Missed "${first} or ${second}" }

-- Not `alt (map p Some) (pure None)`: its index, `bothConsume c False`,
-- doesn't compute while `c` is a variable, so it isn't `False` (Idris 2
-- writes `option` once for each value of `c` for the same reason).
def optional (p: Parser c a): Parser False (Option a) := { run = input =>
  match p.run input with
    | Got x rest h => Got (Some x) rest (Within.weaken c rest.length input.length h)
    | Missed what => Got None input (Nat.leRefl input.length) }

-- `many` needs a parser that consumes: its proof is the measure.
def manyFrom (p: Parser True a) (input: List Char): Reply False input (List a)
    decreasing input.length
:=
  match p.run input with
    | Missed what => Got [] input (Nat.leRefl input.length)
    | Got x rest shorter =>
      match manyFrom p rest with
        | Got xs after noLonger => Got (Cons x xs) after (Nat.leTrans after.length rest.length input.length noLonger (Nat.lessLe rest.length input.length shorter))
        | Missed what => Missed what

def many (p: Parser True a): Parser False (List a) := { run = input => manyFrom p input }

def many1 (p: Parser True a): Parser True (List a) := seq p (x => map (many p) (xs => Cons x xs))

def digit: Parser True Nat := map (satisfy "a digit" (c => c.digitValue.isSome)) (c => c.digitValue.getOrElse 0)

def nat: Parser True Nat := map (many1 digit) Nat.fromDigits

def parse (p: Parser c a) (text: Text): Option a :=
  match p.run text.toList with
    | Got x rest h => if rest == [] then Some x else None
    | Missed what => None

test "many" := parse (many (char 'a')) "aaa" == Some ['a', 'a', 'a']

test "nat" := parse nat "1203" == Some 1203

test "sequence" := parse (seq nat (x => seq (char ',') (comma => map nat (y => x + y)))) "12,30" == Some 42

-- `many (optional (char 'a'))` is refused: `optional` gives a `Parser
-- False`, and `many` needs a `Parser True` (total-parsers.md §4.1 has the
-- message).

-- Recursive grammars, as agdarsec does them. A parser value can't refer to
-- itself, so a recursive grammar is built by `fix` from a body that gets
-- itself as a parser for inputs shorter than the one it is run on. A
-- `Bounded strict bound` parser runs on inputs `Within strict` the bound:
-- shorter than it if `strict`, no longer otherwise. `Bounded True n` is
-- agdarsec's box.
type Bounded (strict: Bool) (bound: Nat) (consumes: Bool) (a: Type) = {
  run: (input: List Char) → Within strict input.length bound → Reply consumes input a
}

theorem Within.shrink: (s: Bool) → (r: Nat) → (m: Nat) → (n: Nat) → r ≤ m → Within s m n → Within s r n
  | True, r, m, n, le, h => Nat.leTrans (Succ r) (Succ m) n le h
  | False, r, m, n, le, h => Nat.leTrans r m n le h

theorem Within.after: (s: Bool) → (r: Nat) → (m: Nat) → (n: Nat) → r < m → Within s m n → r < n
  | True, r, m, n, lt, h => Nat.leTrans (Succ r) m n lt (Nat.lessLe m n h)
  | False, r, m, n, lt, h => Nat.leTrans (Succ r) m n lt h

theorem Within.strict: (s: Bool) → (r: Nat) → (n: Nat) → r < n → Within s r n
  | True, r, n, lt => lt
  | False, r, n, lt => Nat.lessLe r n lt

-- A parser that doesn't recurse works under any bound.
def lift (p: Parser c a): Bounded s n c a := { run = input => ok => p.run input }

-- A parser for inputs within `n` also runs on inputs shorter than `n`.
def below (p: Bounded s n c a): Bounded True n c a := { run = input => ok => p.run input (Within.strict s input.length n ok) }

-- Sequencing under a bound: the rest is no longer than the input, so
-- still within the bound.
def bseq [c1 c2: Bool] (p: Bounded s n c1 a) (next: a → Bounded s n c2 b): Bounded s n (eitherConsumes c1 c2) b := { run = input => ok =>
  match p.run input ok with
    | Missed what => Missed what
    | Got x rest h1 =>
      match (next x).run rest (Within.shrink s rest.length input.length n (Within.weaken c1 rest.length input.length h1) ok) with
        | Missed what => Missed what
        | Got y after h2 => Got y after (Within.seq c1 c2 after.length rest.length input.length h1 h2) }

-- After a parser that consumes, what follows runs on a shorter input: it
-- may use the grammar's own boxed self. This is Idris 2's `SeqEat`.
def eat (p: Bounded s n True a) (next: a → Bounded True n c b): Bounded s n True b := { run = input => ok =>
  match p.run input ok with
    | Missed what => Missed what
    | Got x rest h1 =>
      match (next x).run rest (Within.after s rest.length input.length n h1 ok) with
        | Missed what => Missed what
        | Got y after h2 => Got y after (Within.seq True c after.length rest.length input.length h1 h2) }

def balt [c1 c2: Bool] (p: Bounded s n c1 a) (q: Bounded s n c2 a): Bounded s n (bothConsume c1 c2) a := { run = input => ok =>
  match p.run input ok with
    | Got x rest h => Got x rest (Within.left c1 c2 rest.length input.length h)
    | Missed first =>
      match q.run input ok with
        | Got y rest h => Got y rest (Within.right c1 c2 rest.length input.length h)
        | Missed second => Missed "${first} or ${second}" }

def bmap (p: Bounded s n c a) (f: a → b): Bounded s n c b := { run = input => ok =>
  match p.run input ok with
    | Missed what => Missed what
    | Got x rest h => Got (f x) rest h }

def bmanyFrom (p: Bounded s n True a) (input: List Char) (ok: Within s input.length n): Reply False input (List a)
    decreasing input.length
:=
  match p.run input ok with
    | Missed what => Got [] input (Nat.leRefl input.length)
    | Got x rest shorter =>
      match bmanyFrom p rest (Within.shrink s rest.length input.length n (Nat.lessLe rest.length input.length shorter) ok) with
        | Got xs after noLonger => Got (Cons x xs) after (Nat.leTrans after.length rest.length input.length noLonger (Nat.lessLe rest.length input.length shorter))
        | Missed what => Missed what

def bmany (p: Bounded s n True a): Bounded s n False (List a) := { run = input => ok => bmanyFrom p input ok }

-- `p`, then `separator` and `p` while both match: at least one value.
def bsepBy1 (p: Bounded s n True a) (separator: Parser True b): Bounded s n True (List a) :=
  bseq p (first => bmap (bmany (eat (lift separator) (u => below p))) (more => Cons first more))

-- The fixed point, by recursion on the bound: at `Succ m`, the body's
-- self is the fixed point at `m`.
def fixAt (body: (n: Nat) → Bounded True n True a → Bounded False n True a): (n: Nat) → Bounded False n True a
  | Zero => body Zero ({ run = input => impossible => Void.absurd (Bool.falseNotTrue impossible) })
  | Succ m => body (Succ m) ({ run = input => ok => (fixAt body m).run input ok })

def fix (body: (n: Nat) → Bounded True n True a → Bounded False n True a): Parser True a := { run = input =>
  (fixAt body input.length).run input (Nat.leRefl input.length) }

def bpure (value: a): Bounded s n False a := lift (pure value)

def boptional (p: Bounded s n c a): Bounded s n False (Option a) := { run = input => ok =>
  match p.run input ok with
    | Got x rest h => Got (Some x) rest (Within.weaken c rest.length input.length h)
    | Missed what => Got None input (Nat.leRefl input.length) }

-- The numbers in nested lists like `[1,[2,[]],3]`, added up. The recursive
-- call, `self`, can only be used after `[` has been read.
def nested: Parser True Nat := fix (n => self =>
  balt (lift nat) (eat (lift (char '[')) (open =>
    bseq (boptional (bsepBy1 self (char ','))) (items =>
      bmap (lift (char ']')) (close => (items.getOrElse []).sum)))))

test "nested" := parse nested "[1,[2,[]],3]" == Some 6

test "nested, unbalanced" := parse nested "[1,[2]" == None

-- Arithmetic with `+`, `*` and brackets, the usual precedence. Only
-- `factor` recurses, after `(`.
def arithmetic: Parser True Nat := fix (n => self =>
  let factor := balt (lift nat) (eat (lift (char '(')) (open => bseq self (value => bmap (lift (char ')')) (close => value))))
  let term := bseq factor (first => bmap (bmany (eat (lift (char '*')) (times => below factor))) (more => (Cons first more).product))
  bseq term (first => bmap (bmany (eat (lift (char '+')) (plus => below term))) (more => (Cons first more).sum)))

test "arithmetic" := parse arithmetic "2*(3+4)+1" == Some 15

-- AoC 2024 day 3 in this style.

-- These characters, in order. It consumes whatever the text: an empty
-- text never matches, which a parser that consumes is allowed to do.
def text (expected: Text): Parser True () :=
  match expected.toList with
    | Nil => failWith "a literal"
    | Cons first more => seq (char first) (c => textRest more)

def textRest: List Char → Parser False ()
  | Nil => pure ()
  | Cons first more => mayNotConsume (seq (char first) (c => textRest more))

-- A parser that consumes is also one that may not. There is no
-- subtyping, so this is written where it's needed.
def mayNotConsume (p: Parser c a): Parser False a := { run = input =>
  match p.run input with
    | Got x rest h => Got x rest (Within.weaken c rest.length input.length h)
    | Missed what => Missed what }

-- Every match of `p` in noise, as `Parse.findAll`: where `p` fails, skip a
-- character. The measure is the input, so `p` must consume.
def findAllFrom (p: Parser True a) (input: List Char): List a
    decreasing input.length
:=
  match p.run input with
    | Got x rest shorter => Cons x (findAllFrom p rest)
    | Missed what =>
      match input with
        | Nil => []
        | Cons skipped rest => findAllFrom p rest

type Instruction =
  | Mul (left: Nat) (right: Nat)
  | Do
  | Dont

-- One to three digits.
def shortNumber: Parser True Nat := seq (many1 digit) (digits => if digits.length ≤ 3 then pure (Nat.fromDigits digits) else failWith "a number of 1 to 3 digits")

def instruction: Parser True Instruction :=
  alt (seq (text "mul(") (u =>
    seq shortNumber (left =>
      seq (char ',') (comma =>
        seq shortNumber (right =>
          map (char ')') (close => Mul left right)))))) (alt (map (text "do()") (u => Do)) (map (text "don't()") (u => Dont)))

def instructions (memory: Text): List Instruction := findAllFrom instruction memory.toList

test "day 3" :=
  instructions "xmul(2,4)&mul[3,7]!^don't()_mul(5,5)+mul(32,64](mul(11,8)undo()?mul(8,5))" == [Mul 2 4, Dont, Mul 5 5, Mul 11 8, Do, Mul 8 5]

test "day 3, four digits" := instructions "mul(1234,5)" == []

-- Proofs. A parser here is a plain function, so the lemma that Std.Parse
-- lacks for `optional` over an arbitrary parser (parser-combinators.md §8,
-- "Not proved") is a `match` on what the parser gives.

-- What a reply gives: its value and rest, or nothing.
def Reply.result: Reply c input a → Option (a, List Char)
  | Got x rest h => Some (x, rest)
  | Missed what => None

def optionalResult (input: List Char): Option (a, List Char) → Option (Option a, List Char)
  | Some (x, rest) => Some (Some x, rest)
  | None => Some (None, input)

theorem optionalResultLemma (p: Parser c a) (input: List Char):
    ((optional p).run input).result = optionalResult input (p.run input).result :=
  match p.run input with
    | Got y after h => rfl
    | Missed what => rfl

def altResult (second: Option (a, List Char)): Option (a, List Char) → Option (a, List Char)
  | Some found => Some found
  | None => second

theorem altResultLemma [c1 c2: Bool] (p: Parser c1 a) (q: Parser c2 a) (input: List Char):
    ((alt p q).run input).result = altResult (q.run input).result (p.run input).result :=
  match p.run input with
    | Got x rest h => rfl
    | Missed first =>
      match q.run input with
        | Got y rest h => rfl
        | Missed second => rfl

theorem day3Example: instructions "mul(2,4)do()" = [Mul 2 4, Do] := rfl
