Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negatives :
  sum_product_spec [-6%Z; -4%Z; 8%Z; 3%Z; -6%Z; 0%Z; 8%Z; -10%Z] (-7) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum step by step: *)
    (* (((((((0 + (-6)) + (-4)) + 8) + 3) + (-6)) + 0) + 8) + (-10) = -7 *)
    reflexivity.
  - simpl.
    (* Compute product step by step: *)
    (* 1 * (-6) * (-4) * 8 * 3 * (-6) * 0 * 8 * (-10) = 0 *)
    reflexivity.
Qed.