Goal forall A B : Prop, A /\ B -> A. Proof. intros. Fail solve [auto]. Fail solve [eauto]. easy. Qed.
Goal forall A B : Prop, A /\ B -> A. Proof. intros. tauto. Qed.
Goal forall A B : Prop, A /\ B -> A. Proof. intros. tauto. Qed.
Goal forall A B : Prop, A /\ B -> A. Proof. intros. intuition. Qed.
Goal forall A B : Prop, (A -> B) -> A -> B. Proof. intros. info_auto. Qed.
Goal forall A B : Prop, A -> B -> A /\ B. Proof. intros. info_auto. Qed.
Goal forall A B C : Prop, (A -> C) -> A /\ B -> C. Proof. intros. Fail solve [auto]. Fail solve [eauto]. tauto. Qed.
Goal forall A B C : Prop, (A -> C) -> A /\ B -> C. Proof. intros. firstorder. Qed.
Goal forall (P Q : nat -> Prop), (forall x, P x -> Q x) -> P 5 -> Q 5. Proof. intros. Fail tauto. info_auto. Qed.
Goal forall (P Q : nat -> Prop), (forall x, P x -> Q x) -> P 5 -> Q 5. Proof. intros. Fail solve [intuition fail]. firstorder. Qed.
Goal forall (P Q R: nat -> Prop), (forall x y, P x -> Q y -> R y) -> P 5 -> Q 3 -> R 3. Proof. intros. Fail solve [auto]. info_eauto. Qed.
Goal forall a b : bool, andb a b = true -> a = true. Proof. intros. Fail solve [auto]. Fail solve [intuition]. Fail solve [firstorder]. destruct a; auto. Qed.
Goal forall (f : nat -> nat) a b, a = b -> f b = 0 -> f a = 0. Proof. intros. Fail solve [auto]. Fail solve [intuition]. congruence. Qed.
Goal forall (f : nat -> nat) a b, a = b -> f b = 0 -> f a = 0. Proof. intros. Fail solve [firstorder]. subst; auto. Qed.
Axiom lem : forall n, n > 3 -> n > 1.
Goal forall n, n > 3 -> n > 1. Proof. intros. Fail solve [auto]. info_auto using lem. Qed.
Goal forall A B : Prop, A -> B. Proof. intros. auto. Show. Abort.
Goal forall a b c d : Prop, (a -> b) -> (b -> c) -> (c -> d) -> a -> d. Proof. intros. info_auto. Qed.
Goal forall (P Q R : nat -> Prop), (forall x, P x -> Q x -> R x) -> P 3 -> Q 3 -> R 3. Proof. intros. info_auto. Qed.
Goal forall (p q : nat -> Prop), (exists n, p n /\ q n) -> exists n, q n. Proof. intros. Fail solve [auto]. Fail solve [eauto]. firstorder. Qed.
