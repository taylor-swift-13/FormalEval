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
  problem_142_spec [-1%Z; -3%Z; 17%Z; -1%Z; -15%Z; 13%Z; -1%Z; 14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] (-1448%Z).
Proof.
  unfold problem_142_spec.
  apply (str_cons (-1%Z) [-3%Z; 17%Z; -1%Z; -15%Z; 13%Z; -1%Z; 14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 0%nat (-1449%Z) ((-1%Z) * (-1%Z))).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons (-3%Z) [17%Z; -1%Z; -15%Z; 13%Z; -1%Z; 14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 1%nat (-1446%Z) (-3%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 17%Z [-1%Z; -15%Z; 13%Z; -1%Z; 14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 2%nat (-1463%Z) 17%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons (-1%Z) [-15%Z; 13%Z; -1%Z; 14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 3%nat (-1464%Z) ((-1%Z) * (-1%Z))).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons (-15%Z) [13%Z; -1%Z; 14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 4%nat 1911%Z ((-15%Z) * (-15%Z) * (-15%Z))).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 13%Z [-1%Z; 14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 5%nat 1898%Z 13%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons (-1%Z) [14%Z; -14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 6%nat 1897%Z ((-1%Z) * (-1%Z))).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 14%Z [-14%Z; -12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 7%nat 1883%Z 14%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons (-14%Z) [-12%Z; -5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 8%nat 4627%Z ((-14%Z) * (-14%Z) * (-14%Z))).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons (-12%Z) [-5%Z; 14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 9%nat 4483%Z ((-12%Z) * (-12%Z))).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons (-5%Z) [14%Z; -14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 10%nat 4488%Z (-5%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 14%Z [-14%Z; 6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 11%nat 4474%Z 14%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons (-14%Z) [6%Z; 13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 12%nat 4278%Z ((-14%Z) * (-14%Z))).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 6%Z [13%Z; 11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 13%nat 4272%Z 6%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 13%Z [11%Z; 16%Z; 16%Z; 4%Z; 10%Z] 14%nat 4259%Z 13%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 11%Z [16%Z; 16%Z; 4%Z; 10%Z] 15%nat 4138%Z (11%Z * 11%Z)).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 16%Z [16%Z; 4%Z; 10%Z] 16%nat 42%Z (16%Z * 16%Z * 16%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_cons 16%Z [4%Z; 10%Z] 17%nat 26%Z 16%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 4%Z [10%Z] 18%nat 10%Z (4%Z * 4%Z)).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons 10%Z [] 19%nat 0%Z 10%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_nil 20%nat).
Qed.