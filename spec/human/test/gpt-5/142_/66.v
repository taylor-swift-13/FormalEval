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
  problem_142_spec [2%Z; 30%Z; 6%Z; 12%Z; 18%Z; 21%Z; 24%Z; 0%Z; 28%Z] 28565%Z.
Proof.
  unfold problem_142_spec.
  replace 28565%Z with (4%Z + 28561%Z) by lia.
  apply (str_cons 2%Z [30%Z; 6%Z; 12%Z; 18%Z; 21%Z; 24%Z; 0%Z; 28%Z] 0%nat 28561%Z 4%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace 28561%Z with (30%Z + 28531%Z) by lia.
  apply (str_cons 30%Z [6%Z; 12%Z; 18%Z; 21%Z; 24%Z; 0%Z; 28%Z] 1%nat 28531%Z 30%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 28531%Z with (6%Z + 28525%Z) by lia.
  apply (str_cons 6%Z [12%Z; 18%Z; 21%Z; 24%Z; 0%Z; 28%Z] 2%nat 28525%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 28525%Z with (144%Z + 28381%Z) by lia.
  apply (str_cons 12%Z [18%Z; 21%Z; 24%Z; 0%Z; 28%Z] 3%nat 28381%Z 144%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 28381%Z with (5832%Z + 22549%Z) by lia.
  apply (str_cons 18%Z [21%Z; 24%Z; 0%Z; 28%Z] 4%nat 22549%Z 5832%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 22549%Z with (21%Z + 22528%Z) by lia.
  apply (str_cons 21%Z [24%Z; 0%Z; 28%Z] 5%nat 22528%Z 21%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 22528%Z with (576%Z + 21952%Z) by lia.
  apply (str_cons 24%Z [0%Z; 28%Z] 6%nat 21952%Z 576%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace 21952%Z with (0%Z + 21952%Z) by lia.
  apply (str_cons 0%Z [28%Z] 7%nat 21952%Z 0%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace 21952%Z with (21952%Z + 0%Z) by lia.
  apply (str_cons 28%Z [] 8%nat 0%Z 21952%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_nil 9%nat).
Qed.