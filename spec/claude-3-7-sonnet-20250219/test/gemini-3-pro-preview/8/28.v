Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_new : sum_product_spec [3; 3; 5; 13; 0; 14] 38 0.
Proof.
  unfold sum_product_spec.
  split.
  - reflexivity.
  - reflexivity.
Qed.