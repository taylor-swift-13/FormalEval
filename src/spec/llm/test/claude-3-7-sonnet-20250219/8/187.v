Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_specific_list :
  sum_product_spec [-10%Z; 1%Z; 10%Z; 5%Z; 9%Z; 8%Z; -5%Z] 18 180000.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.