Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negative_and_zero :
  sum_product_spec [-10%Z; 0%Z; 10%Z; 5%Z; 9%Z; 8%Z; -5%Z; 8%Z] 25 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: (-10) + 0 + 10 + 5 + 9 + 8 + (-5) + 8 = 25 *)
    reflexivity.
  - simpl.
    (* Calculate product: (-10) * 0 * 10 * 5 * 9 * 8 * (-5) * 8 = 0 *)
    reflexivity.
Qed.