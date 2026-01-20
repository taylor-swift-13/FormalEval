Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_list_6_1_0_4_7_3_2 :
  sum_product_spec [6; 1; 0; 4; 7; 3; 2] 23 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.