Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_example :
  sum_product_spec [-2; 5; -10; 5; -2] (-4) (-1000).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum step by step: 
       0 + (-2) = -2
       -2 + 5 = 3
       3 + (-10) = -7
       -7 + 5 = -2
       -2 + (-2) = -4 *)
    reflexivity.
  - simpl.
    (* Compute the product step by step:
       1 * (-2) = -2
       -2 * 5 = -10
       -10 * (-10) = 100
       100 * 5 = 500
       500 * (-2) = -1000 *)
    reflexivity.
Qed.