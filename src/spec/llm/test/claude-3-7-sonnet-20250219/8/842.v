Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_mixed_list :
  sum_product_spec [2%Z; 4%Z; -8%Z; -6%Z; -5%Z; 0%Z; -6%Z; -5%Z] (-24) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum: 2 + 4 - 8 - 6 - 5 + 0 - 6 - 5 = -24 *)
    reflexivity.
  - simpl.
    (* The product contains 0, so the entire product is 0 *)
    reflexivity.
Qed.