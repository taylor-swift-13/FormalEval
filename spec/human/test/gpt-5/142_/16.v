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

Example test_case_sum_transformed :
  problem_142_spec [-2%Z; 5%Z; -6%Z; 7%Z; -8%Z] (-460%Z).
Proof.
  unfold problem_142_spec.
  replace (-460%Z) with (((-2%Z) * (-2%Z)) + (-464%Z)) by (vm_compute; reflexivity).
  apply (str_cons (-2%Z) [5%Z; -6%Z; 7%Z; -8%Z] 0%nat (-464%Z) ((-2%Z) * (-2%Z))).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace (-464%Z) with (5%Z + (-469%Z)) by lia.
  apply (str_cons 5%Z [-6%Z; 7%Z; -8%Z] 1%nat (-469%Z) 5%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace (-469%Z) with ((-6%Z) + (-463%Z)) by lia.
  apply (str_cons (-6%Z) [7%Z; -8%Z] 2%nat (-463%Z) (-6%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  replace (-463%Z) with ((7%Z * 7%Z) + (-512%Z)) by (vm_compute; reflexivity).
  apply (str_cons 7%Z [-8%Z] 3%nat (-512%Z) (7%Z * 7%Z)).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  replace (-512%Z) with (((-8%Z) * (-8%Z) * (-8%Z)) + 0%Z) by (vm_compute; reflexivity).
  apply (str_cons (-8%Z) [] 4%nat 0%Z ((-8%Z) * (-8%Z) * (-8%Z))).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_nil 5%nat).
Qed.