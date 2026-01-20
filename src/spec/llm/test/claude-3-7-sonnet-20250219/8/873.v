Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_neg_zeros :
  sum_product_spec
    [-8%Z; 0%Z; 0%Z; 1%Z; 0%Z; 0%Z; -6%Z; -6%Z; 1%Z; -1%Z; -6%Z; -8%Z; 0%Z; 0%Z; 0%Z; 0%Z; -7%Z; 0%Z; -8%Z]
    (-48)%Z
    0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute sum step-by-step for clarity *)
    reflexivity.
  - simpl.
    (* Multiplication includes zeros, product is zero *)
    reflexivity.
Qed.