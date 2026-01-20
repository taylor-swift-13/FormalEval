Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [6%nat; 0%nat; 0%nat; 4%nat; 10%nat; 3%nat; 7%nat; 91%nat; 2%nat; 3%nat] 126 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.