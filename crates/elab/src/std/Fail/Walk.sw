--| Fail's walk lemmas: what `Fail.toResult` of a body of one to four steps
--| (`Fail.toResultSeqN`, with `Then` and `Let` forms) and of two alike runs
--| (`Fail.toResultAlikeN`) is, once the steps' outcomes are known. They are
--| in their own file because checking them costs millions of evaluation
--| steps, which a program that only uses `Fail.toResult` or `Fail.orElse`
--| shouldn't pay; the formatter's walks use them.

--| Running 1 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq1 ∀ [t1: () → {Fail} a1] [g: a1 → r] [v1: a1]
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => g (t1 ())) = Ok (g v1) :=
  rewrite Fail.toResultThen t1 (x => g x), h1

--| As [`Fail.toResultSeq1`], with the built result given to a further step `k`.
theorem Fail.toResultSeq1Then ∀ [t1: () → {Fail} a1] [g: a1 → r] [k: r → {Fail} q] [v1: a1]
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => k (g (t1 ()))) = Fail.toResult (() => k (g v1)) :=
  rewrite Fail.toResultThen (() => g (t1 ())) k, Fail.toResultSeq1 [g := g] h1

--| Running 2 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq2 ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [g: a1 → a2 → r] [v1: a1] [v2: a2]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => g (t1 ()) (t2 ())) = Ok (g v1 v2) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ())), h1, Fail.toResultSeq1 [g := g v1] h2

--| As [`Fail.toResultSeq2`], with the built result given to a further step `k`.
theorem Fail.toResultSeq2Then ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [g: a1 → a2 → r] [k: r → {Fail} q]
    [v1: a1] [v2: a2]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => k (g (t1 ()) (t2 ()))) = Fail.toResult (() => k (g v1 v2)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ())) k, Fail.toResultSeq2 [g := g] h1 h2

--| Running 3 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq3 ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [t3: () → {Fail} a3] [g: a1 → a2 → a3 → r]
    [v1: a1] [v2: a2] [v3: a3]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ())) = Ok (g v1 v2 v3) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())), h1, Fail.toResultSeq2 [g := g v1] h2 h3

--| As [`Fail.toResultSeq3`], with the built result given to a further step `k`.
theorem Fail.toResultSeq3Then ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [t3: () → {Fail} a3] [g: a1 → a2 → a3 → r]
    [k: r → {Fail} q] [v1: a1] [v2: a2] [v3: a3]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()))) = Fail.toResult (() => k (g v1 v2 v3)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ())) k, Fail.toResultSeq3 [g := g] h1 h2 h3

--| Running 4 steps whose results are known (`Ok`): their `Fail`-free outcome is the function applied to those results.
theorem Fail.toResultSeq4 ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [t3: () → {Fail} a3] [t4: () → {Fail} a4]
    [g: a1 → a2 → a3 → a4 → r] [v1: a1] [v2: a2] [v3: a3] [v4: a4]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3)
    (h4: Fail.toResult t4 = Ok v4):
    Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) = Ok (g v1 v2 v3 v4) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())), h1, Fail.toResultSeq3 [g := g v1] h2 h3 h4

--| As [`Fail.toResultSeq4`], with the built result given to a further step `k`.
theorem Fail.toResultSeq4Then ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [t3: () → {Fail} a3] [t4: () → {Fail} a4]
    [g: a1 → a2 → a3 → a4 → r] [k: r → {Fail} q] [v1: a1] [v2: a2] [v3: a3] [v4: a4]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3)
    (h4: Fail.toResult t4 = Ok v4):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ()))) = Fail.toResult (() => k (g v1 v2 v3 v4)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) k, Fail.toResultSeq4 [g := g] h1 h2 h3 h4

--| As [`Fail.toResultSeq1Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultSeq1Let ∀ [t1: () → {Fail} a1] [g: a1 → r] [k: r → {Fail} q] [v1: a1]
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => (let x1 := t1 (); k (g x1))) = Fail.toResult (() => k (g v1)) :=
  rewrite Fail.toResultThen t1 (x => k (g x)), h1

--| As [`Fail.toResultSeq2Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultSeq2Let ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [g: a1 → a2 → r] [k: r → {Fail} q]
    [v1: a1] [v2: a2]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); k (g x1 x2))) = Fail.toResult (() => k (g v1 v2)) :=
  rewrite Fail.toResultThen t1 (x => (let x2 := t2 (); k (g x x2))), h1, Fail.toResultSeq1Let [g := g v1] [k := k] h2

--| As [`Fail.toResultSeq3Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultSeq3Let ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [t3: () → {Fail} a3] [g: a1 → a2 → a3 → r]
    [k: r → {Fail} q] [v1: a1] [v2: a2] [v3: a3]
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); let x3 := t3 (); k (g x1 x2 x3)))
      = Fail.toResult (() => k (g v1 v2 v3)) :=
  rewrite Fail.toResultThen t1 (x => (let x2 := t2 (); let x3 := t3 (); k (g x x2 x3))),
      h1,
      Fail.toResultSeq2Let [g := g v1] [k := k] h2 h3

--| Steps that fail as another set of 1 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike1 ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)):
    Fail.toResult (() => g2 (s1 ())) = (Fail.toResult (() => g (t1 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x), Fail.toResultThen t1 (x => g x), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => rewrite step v1
      | Err m => byComputing

--| As [`Fail.toResultAlike1`], with the built result given to a further step `k`.
theorem Fail.toResultAlike1Then ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => Fail.toResult (() => k (g2 (bl1 v1))) = (Fail.toResult (() => k (g v1))).map blq):
    Fail.toResult (() => k (g2 (s1 ()))) = (Fail.toResult (() => k (g (t1 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ())) k,
      Fail.toResultThen (() => g (t1 ())) k,
      Fail.toResultThen s1 (x => g2 x),
      Fail.toResultThen t1 (x => g x),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => step v1
      | Err m => byComputing

--| Steps that fail as another set of 2 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike2 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => g2 (bl1 v1) (bl2 v2) = blr (g v1 v2)):
    Fail.toResult (() => g2 (s1 ()) (s2 ())) = (Fail.toResult (() => g (t1 ()) (t2 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ())), Fail.toResultThen t1 (x => g x (t2 ())), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike1 h2 (v2 => step v1 v2)
      | Err m => byComputing

--| As [`Fail.toResultAlike2`], with the built result given to a further step `k`.
theorem Fail.toResultAlike2Then ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2)))
      = (Fail.toResult (() => k (g v1 v2))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()))) = (Fail.toResult (() => k (g (t1 ()) (t2 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ())),
      Fail.toResultThen t1 (x => g x (t2 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x), Fail.toResultThen t2 (x => g v1 x), h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 => step v1 v2
            | Err m => byComputing
      | Err m => byComputing

--| Steps that fail as another set of 3 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike3 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1]
    [bl2: a2 → a2] [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => g2 (bl1 v1) (bl2 v2) (bl3 v3) = blr (g v1 v2 v3)):
    Fail.toResult (() => g2 (s1 ()) (s2 ()) (s3 ())) = (Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ())), Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike2 h2 h3 (v2 v3 => step v1 v2 v3)
      | Err m => byComputing

--| As [`Fail.toResultAlike3`], with the built result given to a further step `k`.
theorem Fail.toResultAlike3Then ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1]
    [bl2: a2 → a2] [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3)))
      = (Fail.toResult (() => k (g v1 v2 v3))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ()) (s3 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x (s3 ())), Fail.toResultThen t2 (x => g v1 x (t3 ())), h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 =>
              rewrite Fail.toResultThen s3 (x => g2 (bl1 v1) (bl2 v2) x), Fail.toResultThen t3 (x => g v1 v2 x), h3 then
                match e3: Fail.toResult t3 with
                  | Ok v3 => step v1 v2 v3
                  | Err m => byComputing
            | Err m => byComputing
      | Err m => byComputing

--| Steps that fail as another set of 4 steps does, or finish with its results changed by `bl`, make the body's run fail alike or finish with its result changed by `blr`, given that the rest of the body does for every result.
theorem Fail.toResultAlike4 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3]
    [t4 s4: () → {Fail} a4] [bl1: a1 → a1] [bl2: a2 → a2] [bl3: a3 → a3] [bl4: a4 → a4]
    [g g2: a1 → a2 → a3 → a4 → r] [blr: r → r]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (h4: Fail.toResult s4 = (Fail.toResult t4).map bl4)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) (v4: a4) => g2 (bl1 v1) (bl2 v2) (bl3 v3) (bl4 v4) = blr (g v1 v2 v3 v4)):
    Fail.toResult (() => g2 (s1 ()) (s2 ()) (s3 ()) (s4 ()))
      = (Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ()))).map blr :=
  rewrite Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ()) (s4 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike3 h2 h3 h4 (v2 v3 v4 => step v1 v2 v3 v4)
      | Err m => byComputing

--| As [`Fail.toResultAlike4`], with the built result given to a further step `k`.
theorem Fail.toResultAlike4Then ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3]
    [t4 s4: () → {Fail} a4] [bl1: a1 → a1] [bl2: a2 → a2] [bl3: a3 → a3] [bl4: a4 → a4] [g g2: a1 → a2 → a3 → a4 → r]
    [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (h4: Fail.toResult s4 = (Fail.toResult t4).map bl4)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) (v4: a4) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3) (bl4 v4)))
      = (Fail.toResult (() => k (g v1 v2 v3 v4))).map blq):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ()) (s4 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ())))).map blq :=
  rewrite Fail.toResultThen (() => g2 (s1 ()) (s2 ()) (s3 ()) (s4 ())) k,
      Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) k,
      Fail.toResultThen s1 (x => g2 x (s2 ()) (s3 ()) (s4 ())),
      Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        rewrite Fail.toResultThen s2 (x => g2 (bl1 v1) x (s3 ()) (s4 ())),
            Fail.toResultThen t2 (x => g v1 x (t3 ()) (t4 ())),
            h2 then
          match e2: Fail.toResult t2 with
            | Ok v2 =>
              rewrite Fail.toResultThen s3 (x => g2 (bl1 v1) (bl2 v2) x (s4 ())),
                  Fail.toResultThen t3 (x => g v1 v2 x (t4 ())),
                  h3 then
                match e3: Fail.toResult t3 with
                  | Ok v3 =>
                    rewrite Fail.toResultThen s4 (x => g2 (bl1 v1) (bl2 v2) (bl3 v3) x),
                        Fail.toResultThen t4 (x => g v1 v2 v3 x),
                        h4 then
                      match e4: Fail.toResult t4 with
                        | Ok v4 => step v1 v2 v3 v4
                        | Err m => byComputing
                  | Err m => byComputing
            | Err m => byComputing
      | Err m => byComputing

--| As [`Fail.toResultAlike1Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultAlike1Let ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (step: ∀ (v1: a1) => Fail.toResult (() => k (g2 (bl1 v1))) = (Fail.toResult (() => k (g v1))).map blq):
    Fail.toResult (() => (let x1 := s1 (); k (g2 x1))) = (Fail.toResult (() => (let x1 := t1 (); k (g x1)))).map blq :=
  rewrite Fail.toResultThen s1 (x => k (g2 x)), Fail.toResultThen t1 (x => k (g x)), h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => step v1
      | Err m => byComputing

--| As [`Fail.toResultAlike2Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultAlike2Let ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (step: ∀ (v1: a1) (v2: a2) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2)))
      = (Fail.toResult (() => k (g v1 v2))).map blq):
    Fail.toResult (() => (let x1 := s1 (); let x2 := s2 (); k (g2 x1 x2)))
      = (Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); k (g x1 x2)))).map blq :=
  rewrite Fail.toResultThen s1 (x => (let x2 := s2 (); k (g2 x x2))),
      Fail.toResultThen t1 (x => (let x2 := t2 (); k (g x x2))),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 => Fail.toResultAlike1Let [g := g v1] [g2 := g2 (bl1 v1)] [k := k] [blq := blq] h2 (v2 => step v1 v2)
      | Err m => byComputing

--| As [`Fail.toResultAlike3Then`], with the steps run in `let`s of the same body.
theorem Fail.toResultAlike3Let ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1]
    [bl2: a2 → a2] [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [k: r → {Fail} q] [blq: q → q]
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (step: ∀ (v1: a1) (v2: a2) (v3: a3) => Fail.toResult (() => k (g2 (bl1 v1) (bl2 v2) (bl3 v3)))
      = (Fail.toResult (() => k (g v1 v2 v3))).map blq):
    Fail.toResult (() => (let x1 := s1 (); let x2 := s2 (); let x3 := s3 (); k (g2 x1 x2 x3)))
      = (Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); let x3 := t3 (); k (g x1 x2 x3)))).map blq :=
  rewrite Fail.toResultThen s1 (x => (let x2 := s2 (); let x3 := s3 (); k (g2 x x2 x3))),
      Fail.toResultThen t1 (x => (let x2 := t2 (); let x3 := t3 (); k (g x x2 x3))),
      h1 then
    match e1: Fail.toResult t1 with
      | Ok v1 =>
        Fail.toResultAlike2Let [g := g v1] [g2 := g2 (bl1 v1)] [k := k] [blq := blq] h2 h3 (v2 v3 => step v1 v2 v3)
      | Err m => byComputing

--| A pure value that is `bl` of another pure value runs, as a `Fail` body, as that one's run changed by `bl`.
theorem Fail.toResultAlikePure ∀ [x y: a] [bl: a → a]
    (same: y = bl x):
    Fail.toResult (() => y) = (Fail.toResult (() => x)).map bl :=
  rewrite same

--| A node rebuilt around one child's run (`g` around the run of `t1`, `g2` around the run of `s1`, which
--| fails as that one does or finishes with its result changed by `bl1`), then given to a step `k` that keeps the
--| change `blr` of the rebuilt node (`deaf`: `k` fails alike or finishes with its result changed by `blq`): when
--| rebuilding around changed children is changing the rebuilt node (`rebuilt`), the node's run through `k` fails
--| alike or finishes with its result changed by `blq`. This is [`Fail.toResultAlike1Then`] with its step done by
--| `deaf` and `rebuilt`; a traversal's arm for each constructor is one call, given its children's induction
--| hypotheses as `h1`.
theorem Fail.toResultRebuilds1 ∀ [t1 s1: () → {Fail} a1] [bl1: a1 → a1] [g g2: a1 → r] [k: r → {Fail} q]
    [blr: r → r] [blq: q → q]
    (deaf: ∀ (z: r) => Fail.toResult (() => k (blr z)) = (Fail.toResult (() => k z)).map blq)
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (rebuilt: ∀ (v1: a1) => g2 (bl1 v1) = blr (g v1)):
    Fail.toResult (() => k (g2 (s1 ()))) = (Fail.toResult (() => k (g (t1 ())))).map blq :=
  Fail.toResultAlike1Then h1 (v1 => rewrite rebuilt v1 then deaf (g v1))

--| As [`Fail.toResultRebuilds1`], for a node rebuilt around two children's runs.
theorem Fail.toResultRebuilds2 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [bl1: a1 → a1] [bl2: a2 → a2]
    [g g2: a1 → a2 → r] [k: r → {Fail} q] [blr: r → r] [blq: q → q]
    (deaf: ∀ (z: r) => Fail.toResult (() => k (blr z)) = (Fail.toResult (() => k z)).map blq)
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (rebuilt: ∀ (v1: a1) (v2: a2) => g2 (bl1 v1) (bl2 v2) = blr (g v1 v2)):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()))) = (Fail.toResult (() => k (g (t1 ()) (t2 ())))).map blq :=
  Fail.toResultAlike2Then h1 h2 (v1 v2 => rewrite rebuilt v1 v2 then deaf (g v1 v2))

--| As [`Fail.toResultRebuilds1`], for a node rebuilt around three children's runs.
theorem Fail.toResultRebuilds3 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3] [bl1: a1 → a1]
    [bl2: a2 → a2] [bl3: a3 → a3] [g g2: a1 → a2 → a3 → r] [k: r → {Fail} q] [blr: r → r] [blq: q → q]
    (deaf: ∀ (z: r) => Fail.toResult (() => k (blr z)) = (Fail.toResult (() => k z)).map blq)
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (rebuilt: ∀ (v1: a1) (v2: a2) (v3: a3) => g2 (bl1 v1) (bl2 v2) (bl3 v3) = blr (g v1 v2 v3)):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ())))).map blq :=
  Fail.toResultAlike3Then h1 h2 h3 (v1 v2 v3 => rewrite rebuilt v1 v2 v3 then deaf (g v1 v2 v3))

--| A node rebuilt around one child's run (`g` around the run of `t1`, which finishes with `v1`), then given to a
--| step `k` that finishes with `f` of whatever it is given (`finishes`): the node's run through `k` finishes with `f`
--| of the node rebuilt around `v1`. This is [`Fail.toResultSeq1Then`] with its step done by `finishes`; a traversal's
--| arm for each constructor is one call, given its children's induction hypotheses as `h1`.
theorem Fail.toResultSeqRebuilds1 ∀ [t1: () → {Fail} a1] [v1: a1] [g: a1 → r] [k: r → {Fail} q] [f: r → q]
    (finishes: ∀ (z: r) => Fail.toResult (() => k z) = Ok (f z))
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => k (g (t1 ()))) = Ok (f (g v1)) :=
  rewrite Fail.toResultSeq1Then [g := g] h1, finishes (g v1)

--| As [`Fail.toResultSeqRebuilds1`], for a node rebuilt around two children's runs.
theorem Fail.toResultSeqRebuilds2 ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [v1: a1] [v2: a2] [g: a1 → a2 → r]
    [k: r → {Fail} q] [f: r → q]
    (finishes: ∀ (z: r) => Fail.toResult (() => k z) = Ok (f z))
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => k (g (t1 ()) (t2 ()))) = Ok (f (g v1 v2)) :=
  rewrite Fail.toResultSeq2Then [g := g] h1 h2, finishes (g v1 v2)

--| As [`Fail.toResultSeqRebuilds1`], for a node rebuilt around three children's runs.
theorem Fail.toResultSeqRebuilds3 ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [t3: () → {Fail} a3] [v1: a1] [v2: a2]
    [v3: a3] [g: a1 → a2 → a3 → r] [k: r → {Fail} q] [f: r → q]
    (finishes: ∀ (z: r) => Fail.toResult (() => k z) = Ok (f z))
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()))) = Ok (f (g v1 v2 v3)) :=
  rewrite Fail.toResultSeq3Then [g := g] h1 h2 h3, finishes (g v1 v2 v3)

--| As [`Fail.toResultSeqRebuilds1`], for a node rebuilt around four children's runs.
theorem Fail.toResultSeqRebuilds4 ∀ [t1: () → {Fail} a1] [t2: () → {Fail} a2] [t3: () → {Fail} a3] [t4: () → {Fail} a4]
    [v1: a1] [v2: a2] [v3: a3] [v4: a4] [g: a1 → a2 → a3 → a4 → r] [k: r → {Fail} q] [f: r → q]
    (finishes: ∀ (z: r) => Fail.toResult (() => k z) = Ok (f z))
    (h1: Fail.toResult t1 = Ok v1)
    (h2: Fail.toResult t2 = Ok v2)
    (h3: Fail.toResult t3 = Ok v3)
    (h4: Fail.toResult t4 = Ok v4):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ()))) = Ok (f (g v1 v2 v3 v4)) :=
  rewrite Fail.toResultSeq4Then [g := g] h1 h2 h3 h4, finishes (g v1 v2 v3 v4)

--| As [`Fail.toResultRebuilds1`], for a node rebuilt around four children's runs.
theorem Fail.toResultRebuilds4 ∀ [t1 s1: () → {Fail} a1] [t2 s2: () → {Fail} a2] [t3 s3: () → {Fail} a3]
    [t4 s4: () → {Fail} a4] [bl1: a1 → a1] [bl2: a2 → a2] [bl3: a3 → a3] [bl4: a4 → a4] [g g2: a1 → a2 → a3 → a4 → r]
    [k: r → {Fail} q] [blr: r → r] [blq: q → q]
    (deaf: ∀ (z: r) => Fail.toResult (() => k (blr z)) = (Fail.toResult (() => k z)).map blq)
    (h1: Fail.toResult s1 = (Fail.toResult t1).map bl1)
    (h2: Fail.toResult s2 = (Fail.toResult t2).map bl2)
    (h3: Fail.toResult s3 = (Fail.toResult t3).map bl3)
    (h4: Fail.toResult s4 = (Fail.toResult t4).map bl4)
    (rebuilt: ∀ (v1: a1) (v2: a2) (v3: a3) (v4: a4) => g2 (bl1 v1) (bl2 v2) (bl3 v3) (bl4 v4) = blr (g v1 v2 v3 v4)):
    Fail.toResult (() => k (g2 (s1 ()) (s2 ()) (s3 ()) (s4 ())))
      = (Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ())))).map blq :=
  Fail.toResultAlike4Then h1 h2 h3 h4 (v1 v2 v3 v4 => rewrite rebuilt v1 v2 v3 v4 then deaf (g v1 v2 v3 v4))
