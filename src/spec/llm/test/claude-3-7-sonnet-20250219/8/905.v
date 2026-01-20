Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_list :
  sum_product_spec [78%Z; -77%Z; 91%Z; -36%Z; 6%Z; -2%Z; -74%Z; 20%Z; 27%Z; 93%Z] 126 877442962556160.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. ring.
  - simpl. ring.
Qed.