Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec [2%Z; 10%Z; 2%Z; -4%Z; 3%Z; -5%Z; 3%Z; 0%Z; -7%Z; -4%Z; 10%Z] 10 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum explicitly *)
    (* 2 + 10 + 2 - 4 + 3 - 5 + 3 + 0 - 7 - 4 + 10 = 10 *)
    reflexivity.
  - simpl.
    (* 2 * 10 * 2 * (-4) * 3 * (-5) * 3 * 0 * (-7) * (-4) * 10 = 0 *)
    reflexivity.
Qed.