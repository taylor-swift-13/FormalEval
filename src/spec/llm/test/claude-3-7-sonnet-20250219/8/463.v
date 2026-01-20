Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [20; 0; 0; 2; 1; 0; 13; 0; 12; 20] 68 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.