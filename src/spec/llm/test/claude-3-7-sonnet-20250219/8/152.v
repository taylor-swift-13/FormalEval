Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [0%Z; 8%Z; 0%Z; -1%Z; 0%Z; 0%Z; 0%Z; 8%Z] 15%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* 0 + 8 + 0 + (-1) + 0 + 0 + 0 + 8 = 15 *)
    reflexivity.
  - simpl.
    (* 1 * 0 * 8 * 0 * (-1) * 0 * 0 * 0 * 8 = 0 *)
    reflexivity.
Qed.