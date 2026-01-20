Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_example :
  sum_product_spec [5%Z; -5%Z; 30%Z; 0%Z; -8%Z; 30%Z; 11%Z] 63 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* compute the sum step by step: 5 + (-5) + 30 + 0 + (-8) + 30 + 11 = 63 *)
    reflexivity.
  - simpl.
    (* compute the product step by step: 5 * (-5) * 30 * 0 * (-8) * 30 * 11 = 0 *)
    reflexivity.
Qed.