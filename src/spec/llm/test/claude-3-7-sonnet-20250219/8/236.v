Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_case2 :
  sum_product_spec [10%Z; -5%Z; 30%Z; 0%Z; -8%Z; -6%Z; 30%Z; 10%Z] 61 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: 10 + (-5) + 30 + 0 + (-8) + (-6) + 30 + 10 = 61 *)
    reflexivity.
  - simpl.
    (* Compute product: 10 * (-5) * 30 * 0 * (-8) * (-6) * 30 * 10 = 0 *)
    reflexivity.
Qed.