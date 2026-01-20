Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_list_6_6_4_4_6 :
  sum_product_spec [6; 6; 4; 4; 6] 26 3456.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.