Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negatives :
  sum_product_spec [2; 3; 10; -5; -10; 0; -8] (-8) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum 2 + 3 + 10 + (-5) + (-10) + 0 + (-8) = -8 *)
    reflexivity.
  - simpl.
    (* Compute product 2 * 3 * 10 * (-5) * (-10) * 0 * (-8) = 0 *)
    reflexivity.
Qed.