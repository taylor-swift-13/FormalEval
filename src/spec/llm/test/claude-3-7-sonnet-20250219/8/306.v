Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_mixed_list :
  sum_product_spec [5%Z; -5%Z; 30%Z; 0%Z; -8%Z; 30%Z; 10%Z] 62 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum stepwise: 5 + (-5) = 0; 0 + 30 = 30; 30 + 0 = 30; 30 + (-8) = 22; 22 + 30 = 52; 52 + 10 = 62 *)
    reflexivity.
  - simpl.
    (* product: 1 * 5 = 5; 5 * (-5) = -25; -25 * 30 = -750; -750 * 0 = 0; from here product is zero *)
    reflexivity.
Qed.