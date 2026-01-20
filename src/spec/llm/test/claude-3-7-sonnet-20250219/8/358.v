Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_mixed_list :
  sum_product_spec [1%Z; -1%Z; 0%Z; -1%Z; 0%Z; -11%Z; 0%Z] (-12)%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* sum = 1 + (-1) + 0 + (-1) + 0 + (-11) + 0 = -12 *)
    reflexivity.
  - simpl.
    (* product = 1 * 1 * 0 * ... = 0 *)
    reflexivity.
Qed.