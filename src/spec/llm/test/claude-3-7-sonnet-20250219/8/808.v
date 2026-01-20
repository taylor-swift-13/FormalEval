Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_single_list :
  sum_product_spec [1%Z; 0%Z; -10%Z] (-9) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [1;0;-10] 0 = ((0 + 1) + 0) + (-10) = -9 *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [1;0;-10] 1 = ((1 * 1) * 0) * (-10) = 0 *)
    reflexivity.
Qed.