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

Example test_case_sum_zeros :
  problem_142_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] 0%Z.
Proof.
  unfold problem_142_spec.
  apply (str_cons 0%Z [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] 0%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] 1%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] 2%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [0%Z; 0%Z; 0%Z; 0%Z; 0%Z] 3%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [0%Z; 0%Z; 0%Z; 0%Z] 4%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [0%Z; 0%Z; 0%Z] 5%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [0%Z; 0%Z] 6%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [0%Z] 7%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_cons 0%Z [] 8%nat 0%Z 0%Z).
  split; [ intros _; rewrite Z.mul_0_l; reflexivity
        | split; [ intros _; repeat rewrite Z.mul_0_l; reflexivity
                  | intros _; reflexivity ] ].
  apply (str_nil 9%nat).
Qed.