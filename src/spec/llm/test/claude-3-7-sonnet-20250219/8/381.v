Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_case :
  sum_product_spec [6; 6; 1; 0; 7; 2; 2] 24 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.