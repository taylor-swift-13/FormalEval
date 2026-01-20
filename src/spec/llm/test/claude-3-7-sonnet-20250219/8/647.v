Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_zero_and_minus_one :
  sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -1%Z] (-1) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate sum: 0 + 0 + 0 + 0 + 0 + (-1) = -1 *)
    reflexivity.
  - simpl.
    (* Calculate product: 1 * 0 * 0 * 0 * 0 * 0 * (-1) = 0 *)
    reflexivity.
Qed.