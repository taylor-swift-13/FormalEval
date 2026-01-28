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
  problem_142_spec [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z] 7534%Z.
Proof.
  unfold problem_142_spec.
  replace 7534%Z with (4%Z + 7530%Z) by lia.
  apply (str_cons 2%Z [4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z] 0%nat 7530%Z 4%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons 4%Z [6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z] 1%nat 7526%Z 4%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 6%Z [8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z] 2%nat 7520%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 8%Z [10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z] 3%nat 7456%Z 64%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 10%Z [12%Z; 14%Z; 16%Z; 18%Z; 20%Z] 4%nat 6456%Z 1000%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 12%Z [14%Z; 16%Z; 18%Z; 20%Z] 5%nat 6444%Z 12%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 14%Z [16%Z; 18%Z; 20%Z] 6%nat 6248%Z 196%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 16%Z [18%Z; 20%Z] 7%nat 6232%Z 16%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 18%Z [20%Z] 8%nat 400%Z 5832%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 20%Z [] 9%nat 0%Z 400%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_nil 10%nat).
Qed.