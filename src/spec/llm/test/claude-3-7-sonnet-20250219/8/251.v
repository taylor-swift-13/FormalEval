Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_case :
  sum_product_spec [2%Z; -9%Z; 10%Z; -4%Z; 3%Z; -5%Z; 3%Z; 0%Z; -8%Z; -9%Z] (-17) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate the sum manually: 2 + (-9) + 10 + (-4) + 3 + (-5) + 3 + 0 + (-8) + (-9) = -17 *)
    reflexivity.
  - simpl.
    (* Calculate the product manually: 2 * (-9) * 10 * (-4) * 3 * (-5) * 3 * 0 * (-8) * (-9) = 0 *)
    reflexivity.
Qed.