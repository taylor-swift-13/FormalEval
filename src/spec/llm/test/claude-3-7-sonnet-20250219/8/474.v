Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negative_and_positive :
  sum_product_spec [-2; 5; -10; 10; -2; 10] 11 (-20000).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum: -2 + 5 = 3; 3 + (-10) = -7; -7 + 10 = 3; 3 + (-2) = 1; 1 + 10 = 11 *)
    reflexivity.
  - simpl.
    (* Compute the product: (-2)*5 = -10; -10*(-10) = 100; 100*10 = 1000; 1000*(-2) = -2000; -2000*10 = -20000 *)
    reflexivity.
Qed.