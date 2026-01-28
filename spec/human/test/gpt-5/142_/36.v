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
  problem_142_spec [3%Z; 3%Z; -8%Z; 6%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z] 16681%Z.
Proof.
  unfold problem_142_spec.
  replace 16681%Z with (9%Z + 16672%Z) by lia.
  apply (str_cons 3%Z [3%Z; -8%Z; 6%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z] 0%nat 16672%Z 9%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons 3%Z [-8%Z; 6%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z] 1%nat 16669%Z 3%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons (-8)%Z [6%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z] 2%nat 16677%Z (-8)%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 6%Z [12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z] 3%nat 16641%Z 36%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 12%Z [15%Z; 18%Z; 21%Z; 24%Z; 27%Z] 4%nat 14913%Z 1728%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 15%Z [18%Z; 21%Z; 24%Z; 27%Z] 5%nat 14898%Z 15%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 18%Z [21%Z; 24%Z; 27%Z] 6%nat 14574%Z 324%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 21%Z [24%Z; 27%Z] 7%nat 14553%Z 21%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 24%Z [27%Z] 8%nat 729%Z 13824%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 27%Z [] 9%nat 0%Z 729%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_nil 10%nat).
Qed.