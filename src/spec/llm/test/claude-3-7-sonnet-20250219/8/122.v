Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_single_list :
  sum_product_spec [20; 0; 0; 0; 1; 0; 0] 21 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. (* sum: 20 + 0 + 0 + 0 + 1 + 0 + 0 = 21 *)
    reflexivity.
  - simpl. (* product: 20 * 0 * 0 * 0 * 1 * 0 * 0 = 0 *)
    reflexivity.
Qed.