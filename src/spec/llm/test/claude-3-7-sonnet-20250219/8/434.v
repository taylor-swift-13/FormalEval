Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_single_list :
  sum_product_spec [1%Z; 1%Z; 0%Z; 0%Z; (-4)%Z; (-1)%Z; 0%Z; 0%Z; 11%Z] 8 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum: 1 + 1 + 0 + 0 + (-4) + (-1) + 0 + 0 + 11 = 8 *)
    reflexivity.
  - simpl.
    (* Compute the product: 1 * 1 * 0 * ... = 0 *)
    reflexivity.
Qed.