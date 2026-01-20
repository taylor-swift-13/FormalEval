Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negative_list :
  sum_product_spec [-2%Z; -10%Z; -2%Z; -10%Z] (-24)%Z 400%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [-2; -10; -2; -10] 0 = ((0 + -2) + -10 + -2 + -10) = -24 *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [-2; -10; -2; -10] 1 = (((1 * -2) * -10) * -2) * -10 = 400 *)
    reflexivity.
Qed.