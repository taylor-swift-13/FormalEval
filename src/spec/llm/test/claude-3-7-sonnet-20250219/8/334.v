Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_neg_pos_list :
  sum_product_spec [-8%Z; 2%Z; 4%Z; -6%Z; 0%Z; 8%Z; -10%Z] (-10) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum step by step:
         0 + (-8) = -8
        -8 + 2 = -6
        -6 + 4 = -2
        -2 + (-6) = -8
        -8 + 0 = -8
        -8 + 8 = 0
         0 + (-10) = -10
    *)
    reflexivity.
  - simpl.
    (* Compute the product step by step:
         1 * (-8) = -8
        -8 * 2 = -16
       -16 * 4 = -64
       -64 * (-6) = 384
       384 * 0 = 0
         0 * 8 = 0
         0 * (-10) = 0
    *)
    reflexivity.
Qed.