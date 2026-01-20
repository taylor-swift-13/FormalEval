Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_neg_list :
  sum_product_spec [1%Z; -1%Z; -1%Z; 1%Z; -1%Z] (-1) (-1).
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* 1 + (-1) + (-1) + 1 + (-1) = -1 *)
    reflexivity.
  - simpl.
    (* 1 * 1 * (-1) * (-1) * 1 * (-1) = -1 *)
    reflexivity.
Qed.