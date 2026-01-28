Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_values : sum_product_spec [13; 5; 40; 49] 107 127400.
Proof.
  unfold sum_product_spec.
  split.
  - reflexivity.
  - reflexivity.
Qed.