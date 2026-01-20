Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [1%Z; 10%Z; 5%Z; 9%Z; 8%Z; -5%Z; 11%Z; -5%Z; -10%Z] 24%Z (-9900000)%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.