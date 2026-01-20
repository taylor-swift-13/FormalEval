Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list nat) (result_sum result_product : nat) : Prop :=
  result_sum = fold_left Nat.add numbers 0 /\
  result_product = fold_left Nat.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec [6; 1; 0; 4; 10; 3; 7; 2] 33 0.
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    reflexivity.
  - (* product *)
    simpl.
    reflexivity.
Qed.