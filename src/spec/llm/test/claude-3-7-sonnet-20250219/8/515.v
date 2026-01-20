Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_list_21_0_8_0_21 :
  sum_product_spec [21; 0; 8; 0; 21] 50 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.