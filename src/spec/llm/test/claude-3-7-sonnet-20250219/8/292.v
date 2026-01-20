Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [2%Z; -9%Z; 10%Z; 3%Z; -5%Z; 3%Z; 0%Z; -8%Z; -9%Z; 10%Z; 2%Z] (-1) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Computing the sum manually: 2 + (-9) + 10 + 3 + (-5) + 3 + 0 + (-8) + (-9) + 10 + 2 = -1 *)
    reflexivity.
  - simpl.
    (* Computing the product manually: 
       2 * (-9) = -18
       -18 * 10 = -180
       -180 * 3 = -540
       -540 * (-5) = 2700
       2700 * 3 = 8100
       8100 * 0 = 0
       Once zero is multiplied, the product is zero *)
    reflexivity.
Qed.