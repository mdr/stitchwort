"""Write OUT/base.sw (N definitions of 5 arms each) and OUT/eqs.sw (the same
plus one equation theorem per arm: four by `rfl`, one with two overlap
hypotheses proved by a case split), to time what checking one small
generated equation costs. Usage: python3 gen_cost.py 1000 OUT, then
`stitchwort check --no-cache` each file."""
import sys, pathlib

n = int(sys.argv[1])
out = pathlib.Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
head = "import Std (List, Nat, Option)\n\ntype Shape = | Dot | Line (a: Nat) | Box (a: Nat) (b: Nat) | Many (xs: List Nat)\n\n"
defs = []
eqs = []
for i in range(n):
    defs.append(f"""def f{i} (k: Nat): Shape → List Nat → Nat
  | Dot, ys => k + {i}
  | Line a, ys => a + k
  | Box a b, Nil => a + b + {i}
  | Many xs, Nil => 0
  | s, Cons y ys => f{i} k s ys + y
""")
    eqs.append(f"""theorem f{i}Eq1 (k: Nat) (ys: List Nat): f{i} k Dot ys = k + {i} := rfl
theorem f{i}Eq2 (k: Nat) (a: Nat) (ys: List Nat): f{i} k (Line a) ys = a + k := rfl
theorem f{i}Eq3 (k: Nat) (a: Nat) (b: Nat): f{i} k (Box a b) Nil = a + b + {i} := rfl
theorem f{i}Eq4 (k: Nat) (xs: List Nat): f{i} k (Many xs) Nil = 0 := rfl
theorem f{i}Eq5 (k: Nat) (s: Shape) (y: Nat) (ys: List Nat) (h1: s ≠ Dot) (h2: (a: Nat) → s ≠ Line a): f{i} k s (Cons y ys) = f{i} k s ys + y :=
  match s with
    | Dot => Void.exfalso (h1 rfl)
    | Line a => Void.exfalso (h2 a rfl)
    | Box a b => rfl
    | Many xs => rfl
""")
(out / "base.sw").write_text(head + "\n".join(defs))
(out / "eqs.sw").write_text(head.replace("Option)", "Option, Void)") + "\n".join(defs) + "\n" + "\n".join(eqs))
