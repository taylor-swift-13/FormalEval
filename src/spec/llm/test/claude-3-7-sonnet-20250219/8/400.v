Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_given_list :
  sum_product_spec [8%Z; -10%Z; 0%Z; 10%Z; -5%Z; -5%Z; -5%Z; 8%Z; 8%Z] 9 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum: 8 + (-10) + 0 + 10 + (-5) + (-5) + (-5) + 8 + 8 = 9 *)
    reflexivity.
  - simpl.
    (* Compute product: 8 * (-10) * 0 * 10 * (-5) * (-5) * (-5) * 8 * 8 = 0 *)
    reflexivity.
Qed.