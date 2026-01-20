Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0%Z /\
  result_product = fold_left Z.mul numbers 1%Z.

Example test_sum_product_case :
  sum_product_spec [0%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z] 1%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.