Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_single_list :
  sum_product_spec [30%Z; 0%Z; 5%Z; 8%Z; -5%Z] 38%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [30;0;5;8;-5] 0 = ((((0 + 30) + 0) + 5) + 8) + (-5) = 38 *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [30;0;5;8;-5] 1 = ((((1 * 30) * 0) * 5) * 8) * (-5) = 0 *)
    reflexivity.
Qed.