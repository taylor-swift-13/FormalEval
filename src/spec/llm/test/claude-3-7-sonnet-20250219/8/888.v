Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec [3;7;1;0;4;7;3;7;2;0;2] 36 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* fold_left Z.add [3;7;1;0;4;7;3;7;2;0;2] 0 = 36 *)
    reflexivity.
  - simpl.
    (* fold_left Z.mul [3;7;1;0;4;7;3;7;2;0;2] 1 = 0 *)
    reflexivity.
Qed.