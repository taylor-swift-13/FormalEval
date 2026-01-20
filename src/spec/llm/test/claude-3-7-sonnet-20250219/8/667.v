Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_input_6_20_1_0_7_3_7_2_7 :
  sum_product_spec [6; 20; 1; 0; 7; 3; 7; 2; 7] 53 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.