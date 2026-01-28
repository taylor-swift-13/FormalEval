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
  problem_142_spec [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; -9%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] (-224%Z).
Proof.
  unfold problem_142_spec.
  replace (-224%Z) with (1%Z + -225%Z) by lia.
  apply (str_cons 1%Z [-2%Z; 3%Z; -4%Z; 5%Z; -6%Z; -9%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] 0%nat (-225%Z) 1%Z).
  split; [ intros _; rewrite Z.mul_1_r; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace (-225%Z) with (-2%Z + -223%Z) by lia.
  apply (str_cons (-2%Z) [3%Z; -4%Z; 5%Z; -6%Z; -9%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] 1%nat (-223%Z) (-2%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace (-223%Z) with (3%Z + -226%Z) by lia.
  apply (str_cons 3%Z [-4%Z; 5%Z; -6%Z; -9%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] 2%nat (-226%Z) 3%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace (-226%Z) with (16%Z + -242%Z) by lia.
  apply (str_cons (-4%Z) [5%Z; -6%Z; -9%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] 3%nat (-242%Z) 16%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace (-242%Z) with (125%Z + -367%Z) by lia.
  apply (str_cons 5%Z [-6%Z; -9%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] 4%nat (-367%Z) 125%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace (-367%Z) with (-6%Z + -361%Z) by lia.
  apply (str_cons (-6%Z) [-9%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] 5%nat (-361%Z) (-6%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace (-361%Z) with (81%Z + -442%Z) by lia.
  apply (str_cons (-9%Z) [7%Z; -8%Z; 9%Z; -10%Z; -8%Z] 6%nat (-442%Z) 81%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace (-442%Z) with (7%Z + -449%Z) by lia.
  apply (str_cons 7%Z [-8%Z; 9%Z; -10%Z; -8%Z] 7%nat (-449%Z) 7%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace (-449%Z) with (-512%Z + 63%Z) by lia.
  apply (str_cons (-8%Z) [9%Z; -10%Z; -8%Z] 8%nat 63%Z (-512%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace (63%Z) with (81%Z + -18%Z) by lia.
  apply (str_cons 9%Z [-10%Z; -8%Z] 9%nat (-18%Z) 81%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace (-18%Z) with (-10%Z + -8%Z) by lia.
  apply (str_cons (-10%Z) [-8%Z] 10%nat (-8%Z) (-10%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace (-8%Z) with (-8%Z + 0%Z) by lia.
  apply (str_cons (-8%Z) [] 11%nat 0%Z (-8%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_nil 12%nat).
Qed.