Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_case1 : sum_product_spec [2; 4; 8; 1; 16; 4; 16; 16; 5; -1; 2; 4; 16; 10; 8] 111 (-53687091200).
Proof.
  unfold sum_product_spec.
  split.
  - reflexivity.
  - reflexivity.
Qed.