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
  problem_142_spec [3%Z; 6%Z; 14%Z; 10%Z; 15%Z; 21%Z; 24%Z; 27%Z; 23%Z; 30%Z] 17195%Z.
Proof.
  unfold problem_142_spec.
  replace 17195%Z with (9%Z + 17186%Z) by lia.
  apply (str_cons 3%Z [6%Z; 14%Z; 10%Z; 15%Z; 21%Z; 24%Z; 27%Z; 23%Z; 30%Z] 0%nat 17186%Z 9%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons 6%Z [14%Z; 10%Z; 15%Z; 21%Z; 24%Z; 27%Z; 23%Z; 30%Z] 1%nat 17180%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 14%Z [10%Z; 15%Z; 21%Z; 24%Z; 27%Z; 23%Z; 30%Z] 2%nat 17166%Z 14%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 10%Z [15%Z; 21%Z; 24%Z; 27%Z; 23%Z; 30%Z] 3%nat 17066%Z 100%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 15%Z [21%Z; 24%Z; 27%Z; 23%Z; 30%Z] 4%nat 13691%Z 3375%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 21%Z [24%Z; 27%Z; 23%Z; 30%Z] 5%nat 13670%Z 21%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 24%Z [27%Z; 23%Z; 30%Z] 6%nat 13094%Z 576%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 27%Z [23%Z; 30%Z] 7%nat 13067%Z 27%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 23%Z [30%Z] 8%nat 900%Z 12167%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 30%Z [] 9%nat 0%Z 900%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_nil 10%nat).
Qed.