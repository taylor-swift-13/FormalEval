Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_Z_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_case :
  sum_product_Z_spec [2; 13; 7; 11; 13; 49; 16] 111 20404384.
Proof.
  unfold sum_product_Z_spec.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.