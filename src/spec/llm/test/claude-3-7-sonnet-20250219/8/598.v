Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negatives :
  sum_product_spec [-3%Z; -7%Z; 8%Z; 1%Z; -4%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-5%Z) 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. (* fold_left Z.add on the list *)
    reflexivity.
  - simpl. (* fold_left Z.mul encounters 0 so product is 0 *)
    reflexivity.
Qed.