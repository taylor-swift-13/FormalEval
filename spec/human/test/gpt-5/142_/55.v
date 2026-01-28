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
  problem_142_spec [7%Z; 1%Z; -2%Z; 3%Z; -4%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; 5%Z] 862%Z.
Proof.
  unfold problem_142_spec.
  replace 862%Z with (49%Z + 813%Z) by lia.
  apply (str_cons 7%Z [1%Z; -2%Z; 3%Z; -4%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; 5%Z] 0%nat 813%Z 49%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace 813%Z with (1%Z + 812%Z) by lia.
  apply (str_cons 1%Z [-2%Z; 3%Z; -4%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; 5%Z] 1%nat 812%Z 1%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 812%Z with (-2%Z + 814%Z) by lia.
  apply (str_cons (-2)%Z [3%Z; -4%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; 5%Z] 2%nat 814%Z (-2)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 814%Z with (9%Z + 805%Z) by lia.
  apply (str_cons 3%Z [-4%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; 5%Z] 3%nat 805%Z 9%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 805%Z with (-64%Z + 869%Z) by lia.
  apply (str_cons (-4)%Z [-6%Z; 7%Z; -8%Z; 9%Z; -10%Z; 5%Z] 4%nat 869%Z (-64)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 869%Z with (-6%Z + 875%Z) by lia.
  apply (str_cons (-6)%Z [7%Z; -8%Z; 9%Z; -10%Z; 5%Z] 5%nat 875%Z (-6)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 875%Z with (49%Z + 826%Z) by lia.
  apply (str_cons 7%Z [-8%Z; 9%Z; -10%Z; 5%Z] 6%nat 826%Z 49%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 826%Z with (-8%Z + 834%Z) by lia.
  apply (str_cons (-8)%Z [9%Z; -10%Z; 5%Z] 7%nat 834%Z (-8)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 834%Z with (729%Z + 105%Z) by lia.
  apply (str_cons 9%Z [-10%Z; 5%Z] 8%nat 105%Z 729%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 105%Z with (100%Z + 5%Z) by lia.
  apply (str_cons (-10)%Z [5%Z] 9%nat 5%Z 100%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 5%Z [] 10%nat 0%Z 5%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_nil 11%nat).
Qed.