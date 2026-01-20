Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [-1%Z; 20%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] 19%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [-1;20;0;0;0;0;0;0] 0 = ((...((0 + (-1)) + 20) + 0) + ...) = 19 *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [-1;20;0;0;0;0;0;0] 1 = (((...((1 * (-1)) * 20) * 0) * 0) * ...) = 0 *)
    reflexivity.
Qed.