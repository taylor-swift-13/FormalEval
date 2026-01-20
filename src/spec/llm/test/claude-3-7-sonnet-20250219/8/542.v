Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_example :
  sum_product_spec
    [-6%Z; -4%Z; -4%Z; 7%Z; 4%Z; -6%Z; 0%Z; 8%Z; -10%Z; 4%Z; 8%Z; 0%Z] 1 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.