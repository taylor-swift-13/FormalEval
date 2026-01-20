Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_single_list :
  sum_product_spec [20%Z; 0%Z; 0%Z; 1%Z; -9%Z; 0%Z; -1%Z; -4%Z] 7 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum 20 + 0 + 0 + 1 + (-9) + 0 + (-1) + (-4) = 7 *)
    reflexivity.
  - simpl.
    (* Calculate product 20 * 0 * 0 * 1 * (-9) * 0 * (-1) * (-4) = 0 *)
    reflexivity.
Qed.