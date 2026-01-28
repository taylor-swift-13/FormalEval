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
  problem_142_spec [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z] 1090%Z.
Proof.
  unfold problem_142_spec.
  replace 1090%Z with (4%Z + 1086%Z) by lia.
  apply (str_cons 2%Z [4%Z; 6%Z; 8%Z; 10%Z; 12%Z] 0%nat 1086%Z 4%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace 1086%Z with (4%Z + 1082%Z) by lia.
  apply (str_cons 4%Z [6%Z; 8%Z; 10%Z; 12%Z] 1%nat 1082%Z 4%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 1082%Z with (6%Z + 1076%Z) by lia.
  apply (str_cons 6%Z [8%Z; 10%Z; 12%Z] 2%nat 1076%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 1076%Z with (64%Z + 1012%Z) by lia.
  apply (str_cons 8%Z [10%Z; 12%Z] 3%nat 1012%Z 64%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 1012%Z with (1000%Z + 12%Z) by lia.
  apply (str_cons 10%Z [12%Z] 4%nat 12%Z 1000%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 12%Z with (12%Z + 0%Z) by lia.
  apply (str_cons 12%Z [] 5%nat 0%Z 12%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_nil 6%nat).
Qed.