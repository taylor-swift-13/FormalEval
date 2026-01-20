Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; -10; 1; 1; 1; 1; 1; 1; 1; 1; 1]
    47
    (-10).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum of all 1's except one -10: there are 59 numbers in total:
       58 times 1 and one -10, sum = 58 * 1 + (-10) = 48 - 1 = 47 *)
    reflexivity.
  - simpl.
    (* product: all 1's except one -10, product = -10 *)
    reflexivity.
Qed.