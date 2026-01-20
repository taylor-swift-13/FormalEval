Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_mixed_list :
  sum_product_spec [2%Z; 10%Z; -5%Z; 0%Z; 8%Z; -8%Z; 10%Z; -8%Z; 10%Z] 19 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum: 2 + 10 = 12, 12 + (-5) = 7, 7 + 0 = 7, 7 + 8 = 15, 15 + (-8) = 7, 
       7 + 10 = 17, 17 + (-8) = 9, 9 + 10 = 19 *)
    reflexivity.
  - simpl.
    (* product: 1 * 2 = 2, 2 * 10 = 20, 20 * (-5) = -100, (-100) * 0 = 0, 
       0 * 8 = 0, 0 * (-8) = 0, 0 * 10 = 0, 0 * (-8) = 0, 0 * 10 = 0 *)
    reflexivity.
Qed.