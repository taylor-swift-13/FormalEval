Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Lia.
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

Example test_case_sum_squares :
  problem_142_spec [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 1004%Z.
Proof.
  unfold problem_142_spec.
  replace 1004%Z with (1%Z + 1003%Z) by lia.
  apply (str_cons 1%Z [-2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 0%nat 1003%Z 1%Z).
  split; [ intros _; rewrite Z.mul_1_r; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons (-2)%Z [3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 1%nat 1005%Z (-2)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 3%Z [-4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 2%nat 1002%Z 3%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons (-4)%Z [5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 3%nat 986%Z 16%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons 5%Z [-6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 4%nat 861%Z 125%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons (-6)%Z [7%Z; -8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 5%nat 867%Z (-6)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 7%Z [-8%Z; 9%Z; -10%Z; -8%Z; 5%Z] 6%nat 818%Z 49%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons (-8)%Z [9%Z; -10%Z; -8%Z; 5%Z] 7%nat 826%Z (-8)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 9%Z [-10%Z; -8%Z; 5%Z] 8%nat 97%Z 729%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons (-10)%Z [-8%Z; 5%Z] 9%nat (-3)%Z 100%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons (-8)%Z [5%Z] 10%nat 5%Z (-8)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 5%Z [] 11%nat 0%Z 5%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_nil 12%nat).
Qed.