namespace Fmt.OperatorList
import Std (Bool, DecEq, List, Text)
import Fmt (..)

--| The infix operators of slice 1, each spelling `operatorText1` tests a text against, in its order. A fact about
--| every operator is proved once for this list (`List.allMember` for a test, `List.allMem` for a proposition) and
--| reaches an `operatorText1` text through `operatorListed`.
def operators1: List Text :=
  ["->", "→", "||", "∨", "&&", "∧", "+", "++", "-", "*", "/", "%", "!=", "≠", "<", "<=", "≤", ">", ">=", "≥", "==", "="]

--| A text `operatorTextA1` accepts is on the list `operators1`.
theorem operatorListedA ∀ (text: Text) (listed: operatorTextA1 text = True): text ∈ operators1 :=
  match a0: text == "->" with
    | True => rewrite DecEq.sound a0 then Inl byComputing
    | False =>
      match a1: text == "→" with
        | True => rewrite DecEq.sound a1 then Inr (Inl byComputing)
        | False =>
          match a2: text == "||" with
            | True => rewrite DecEq.sound a2 then Inr (Inr (Inl byComputing))
            | False =>
              match a3: text == "∨" with
                | True => rewrite DecEq.sound a3 then Inr (Inr (Inr (Inl byComputing)))
                | False =>
                  match a4: text == "&&" with
                    | True => rewrite DecEq.sound a4 then Inr (Inr (Inr (Inr (Inl byComputing))))
                    | False =>
                      match a5: text == "∧" with
                        | True => rewrite DecEq.sound a5 then Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))

--| A text `operatorTextB1` accepts is on the list `operators1`.
theorem operatorListedB ∀ (text: Text) (listed: operatorTextB1 text = True): text ∈ operators1 :=
  match a6: text == "+" with
    | True => rewrite DecEq.sound a6 then Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))
    | False =>
      match a7: text == "++" with
        | True => rewrite DecEq.sound a7 then Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))
        | False =>
          match a8: text == "-" with
            | True => rewrite DecEq.sound a8 then Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))))
            | False =>
              match a9: text == "*" with
                | True =>
                  rewrite DecEq.sound a9 then Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))))
                | False =>
                  match a10: text == "/" with
                    | True =>
                      rewrite DecEq.sound a10 then
                        Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))))))
                    | False =>
                      match a11: text == "%" with
                        | True =>
                          rewrite DecEq.sound a11 then
                            Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))))))

--| A text `operatorTextC1` accepts is on the list `operators1`.
theorem operatorListedC ∀ (text: Text) (listed: operatorTextC1 text = True): text ∈ operators1 :=
  match a12: text == "!=" with
    | True =>
      rewrite DecEq.sound a12 then
        Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))))))))
    | False =>
      match a13: text == "≠" with
        | True =>
          rewrite DecEq.sound a13 then
            Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))))))))
        | False =>
          match a14: text == "<" with
            | True =>
              rewrite DecEq.sound a14 then
                Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))))))))))
            | False =>
              match a15: text == "<=" with
                | True =>
                  rewrite DecEq.sound a15 then
                    Inr
                      (Inr
                        (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))))))))))
                | False =>
                  match a16: text == "≤" with
                    | True =>
                      rewrite DecEq.sound a16 then
                        Inr
                          (Inr
                            (Inr
                              (Inr
                                (Inr
                                  (Inr
                                    (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))))))))))))

--| A text `operatorTextD1` accepts is on the list `operators1`.
theorem operatorListedD ∀ (text: Text) (listed: operatorTextD1 text = True): text ∈ operators1 :=
  match a17: text == ">" with
    | True =>
      rewrite DecEq.sound a17 then
        Inr
          (Inr
            (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))))))))))))
    | False =>
      match a18: text == ">=" with
        | True =>
          rewrite DecEq.sound a18 then
            Inr
              (Inr
                (Inr
                  (Inr
                    (Inr
                      (Inr
                        (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))))))))))))))
        | False =>
          match a19: text == "≥" with
            | True =>
              rewrite DecEq.sound a19 then
                Inr
                  (Inr
                    (Inr
                      (Inr
                        (Inr
                          (Inr
                            (Inr
                              (Inr
                                (Inr
                                  (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))))))))))))))
            | False =>
              match a20: text == "==" with
                | True =>
                  rewrite DecEq.sound a20 then
                    Inr
                      (Inr
                        (Inr
                          (Inr
                            (Inr
                              (Inr
                                (Inr
                                  (Inr
                                    (Inr
                                      (Inr
                                        (Inr
                                          (Inr
                                            (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl byComputing))))))))))))))))))))
                | False =>
                  match a21: text == "=" with
                    | True =>
                      rewrite DecEq.sound a21 then
                        Inr
                          (Inr
                            (Inr
                              (Inr
                                (Inr
                                  (Inr
                                    (Inr
                                      (Inr
                                        (Inr
                                          (Inr
                                            (Inr
                                              (Inr
                                                (Inr
                                                  (Inr
                                                    (Inr
                                                      (Inr
                                                        (Inr (Inr (Inr (Inr (Inr (Inl byComputing)))))))))))))))))))))

--| A text slice 1 calls an infix operator is on the list `operators1`.
theorem operatorListed ∀ (text: Text) (listed: operatorText1 text = True): text ∈ operators1 :=
  match first: operatorTextA1 text with
    | True => operatorListedA text first
    | False =>
      match second: operatorTextB1 text with
        | True => operatorListedB text second
        | False =>
          match third: operatorTextC1 text with
            | True => operatorListedC text third
            | False => operatorListedD text listed
