Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_one_list :
  sum_product_spec [2%Z; 4%Z; 8%Z] 14 64.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [2;4;8] 0 = ((0 + 2) + 4) + 8 = 14 *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [2;4;8] 1 = ((1 * 2) * 4) * 8 = 64 *)
    reflexivity.
Qed.