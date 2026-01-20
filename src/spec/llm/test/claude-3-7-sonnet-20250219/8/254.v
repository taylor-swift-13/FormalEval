Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1]
    61 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum = number of 1s + 2 + 0 + 0 *)
    reflexivity.
  - simpl.
    (* product includes 0, so fold_left Nat.mul returns 0 *)
    reflexivity.
Qed.