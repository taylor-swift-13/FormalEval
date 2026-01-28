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
  problem_142_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] 1039%Z.
Proof.
  unfold problem_142_spec.
  replace 1039%Z with (1%Z + 1038%Z) by lia.
  apply (str_cons 1%Z [2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] 0%nat 1038%Z 1%Z).
  split; [ intros _; rewrite Z.mul_1_r; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace 1038%Z with (2%Z + 1036%Z) by lia.
  apply (str_cons 2%Z [3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] 1%nat 1036%Z 2%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 1036%Z with (3%Z + 1033%Z) by lia.
  apply (str_cons 3%Z [4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] 2%nat 1033%Z 3%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 1033%Z with (16%Z + 1017%Z) by lia.
  apply (str_cons 4%Z [5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z] 3%nat 1017%Z 16%Z).
  split; [ intros _; change 16%Z with (4%Z * 4%Z); reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 1017%Z with (125%Z + 892%Z) by lia.
  apply (str_cons 5%Z [6%Z; 7%Z; 8%Z; 9%Z; 10%Z] 4%nat 892%Z 125%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; change 125%Z with (5%Z * 5%Z * 5%Z); reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 892%Z with (6%Z + 886%Z) by lia.
  apply (str_cons 6%Z [7%Z; 8%Z; 9%Z; 10%Z] 5%nat 886%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 886%Z with (49%Z + 837%Z) by lia.
  apply (str_cons 7%Z [8%Z; 9%Z; 10%Z] 6%nat 837%Z 49%Z).
  split; [ intros _; change 49%Z with (7%Z * 7%Z); reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 837%Z with (8%Z + 829%Z) by lia.
  apply (str_cons 8%Z [9%Z; 10%Z] 7%nat 829%Z 8%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 829%Z with (729%Z + 100%Z) by lia.
  apply (str_cons 9%Z [10%Z] 8%nat 100%Z 729%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; change 729%Z with (9%Z * 9%Z * 9%Z); reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 100%Z with (100%Z + 0%Z) by lia.
  apply (str_cons 10%Z [] 9%nat 0%Z 100%Z).
  split; [ intros _; change 100%Z with (10%Z * 10%Z); reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_nil 10%nat).
Qed.