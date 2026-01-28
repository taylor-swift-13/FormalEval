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

Example test_142 : problem_142_spec [-56%Z; -99%Z; 1%Z; 0%Z; -2%Z] 3030%Z.
Proof.
  unfold problem_142_spec.
  apply (str_cons (-56) [-99%Z; 1%Z; 0%Z; -2%Z] 0 ((-99)*(-99)*(-99) + (1 + (0 + (-2)))) ((-56)*(-56))).
  - split; [| split].
    + intros _. reflexivity.
    + intros [H1 H2]. simpl in H1. discriminate.
    + intros [H1 H2]. simpl in H1. discriminate.
  - apply (str_cons (-99) [1%Z; 0%Z; -2%Z] 1 (1 + (0 + (-2))) ((-99)*(-99)*(-99))).
    + split; [| split].
      * intros H. simpl in H. discriminate.
      * intros [H1 H2]. simpl in H2. discriminate.
      * intros [H1 H2]. simpl in H2. discriminate.
    + apply (str_cons 1 [0%Z; -2%Z] 2 (0 + (-2)) 1).
      * split; [| split].
        -- intros H. simpl in H. discriminate.
        -- intros [H1 H2]. simpl in H2. discriminate.
        -- intros [H1 H2]. reflexivity.
      * apply (str_cons 0 [-2%Z] 3 (-2) 0).
        -- split; [| split].
           ++ intros H. simpl in H. reflexivity.
           ++ intros [H1 H2]. simpl in H1. discriminate.
           ++ intros [H1 H2]. simpl in H1. discriminate.
        -- apply (str_cons (-2) [] 4 0 (-2)).
           ++ split; [| split].
              ** intros H. simpl in H. discriminate.
              ** intros [H1 H2]. reflexivity.
              ** intros [H1 H2]. simpl in H2. discriminate.
           ++ apply str_nil.
Qed.