Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_numbers : sum_product_spec [0; 1; 2; 3; 4; 5] 15 0.
Proof.
  unfold sum_product_spec.
  simpl.
  split.
  - reflexivity.
  - reflexivity.
Qed.