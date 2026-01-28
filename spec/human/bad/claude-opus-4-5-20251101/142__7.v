Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_transformed_rel : list Z -> nat -> Z -> Prop :=
| str_nil : forall i, sum_transformed_rel [] i 0%Z
| str_cons : forall h t i s_tail term,
   ((Nat.eqb (i mod 3) 0 = true -> term = h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = true -> term = h * h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = false -> term = h)) ->
   sum_transformed_rel t (S i) s_tail ->
   sum_transformed_rel (h :: t) i (term + s_tail).

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.

Example test_142 : problem_142_spec [-1%Z; -5%Z; 2%Z; -1%Z; -5%Z] (-126%Z).
Proof.
  unfold problem_142_spec.
  apply (str_cons (-1) [-5%Z; 2%Z; -1%Z; -5%Z] 0 (-125) 1).
  - split; [| split].
    + intros _. reflexivity.
    + intros [H1 H2]. inversion H1.
    + intros [H1 H2]. inversion H1.
  - apply (str_cons (-5) [2%Z; -1%Z; -5%Z] 1 0 (-5)).
    + split; [| split].
      * intros H. inversion H.
      * intros [H1 H2]. inversion H2.
      * intros [H1 H2]. reflexivity.
    + apply (str_cons 2 [-1%Z; -5%Z] 2 (-2) 2).
      * split; [| split].
        -- intros H. inversion H.
        -- intros [H1 H2]. inversion H2.
        -- intros [H1 H2]. reflexivity.
      * apply (str_cons (-1) [-5%Z] 3 (-1) (-1)).
        -- split; [| split].
           ++ intros _. reflexivity.
           ++ intros [H1 H2]. inversion H1.
           ++ intros [H1 H2]. inversion H1.
        -- apply (str_cons (-5) [] 4 0 (-125)).
           ++ split; [| split].
              ** intros H. inversion H.
              ** intros [H1 H2]. reflexivity.
              ** intros [H1 H2]. inversion H2.
           ++ apply str_nil.
Qed.