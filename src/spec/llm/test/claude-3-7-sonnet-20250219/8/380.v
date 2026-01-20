Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_nontrivial :
  sum_product_spec [-2; 5; -10; 21; 5; -2; 5] 22 (-105000).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* calculate sum: -2 + 5 = 3, 3 + (-10) = -7, -7 + 21 = 14, 14 + 5 = 19, 19 + (-2) = 17, 17 + 5 = 22 *)
    reflexivity.
  - simpl.
    (* calculate product: 1 * (-2) = -2, -2 * 5 = -10, -10 * (-10) = 100, 100 * 21 = 2100, 2100 * 5 = 10500, 10500 * (-2) = -21000, -21000 * 5 = -105000 *)
    reflexivity.
Qed.