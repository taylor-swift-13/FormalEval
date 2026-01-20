Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [2; 4; -6; 0; 8; -10; 4] 2 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum manually: 2 + 4 = 6; 6 + (-6) = 0; 0 + 0 = 0; 0 + 8 = 8; 8 + (-10) = -2; -2 + 4 = 2 *)
    reflexivity.
  - simpl.
    (* Compute product manually: 1 * 2 = 2; 2 * 4 = 8; 8 * (-6) = -48; -48 * 0 = 0; 0 * 8 = 0; 0 * (-10) = 0; 0 * 4 = 0 *)
    reflexivity.
Qed.