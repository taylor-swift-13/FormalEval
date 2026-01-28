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
  problem_142_spec [2%Z; 30%Z; 6%Z; 9%Z; 12%Z; 18%Z; 21%Z; 24%Z; 28%Z; 28%Z] 25068%Z.
Proof.
  unfold problem_142_spec.
  replace 25068%Z with (4%Z + 25064%Z) by lia.
  apply (str_cons 2%Z [30%Z; 6%Z; 9%Z; 12%Z; 18%Z; 21%Z; 24%Z; 28%Z; 28%Z] 0%nat 25064%Z 4%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons 30%Z [6%Z; 9%Z; 12%Z; 18%Z; 21%Z; 24%Z; 28%Z; 28%Z] 1%nat 25034%Z 30%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 6%Z [9%Z; 12%Z; 18%Z; 21%Z; 24%Z; 28%Z; 28%Z] 2%nat 25028%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 9%Z [12%Z; 18%Z; 21%Z; 24%Z; 28%Z; 28%Z] 3%nat 24947%Z 81%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 12%Z [18%Z; 21%Z; 24%Z; 28%Z; 28%Z] 4%nat 23219%Z 1728%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 18%Z [21%Z; 24%Z; 28%Z; 28%Z] 5%nat 23201%Z 18%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 21%Z [24%Z; 28%Z; 28%Z] 6%nat 22760%Z 441%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 24%Z [28%Z; 28%Z] 7%nat 22736%Z 24%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 28%Z [28%Z] 8%nat 784%Z 21952%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 28%Z [] 9%nat 0%Z 784%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_nil 10%nat).
Qed.