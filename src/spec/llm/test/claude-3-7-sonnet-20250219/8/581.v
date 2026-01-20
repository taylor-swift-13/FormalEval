Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [-1%Z; 20%Z; 0%Z; 0%Z; 0%Z; 29%Z; 0%Z; 0%Z; 0%Z; 0%Z; 20%Z; 0%Z; 0%Z]
    68%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Evaluate fold_left Z.add on the list *)
    reflexivity.
  - simpl.
    (* Evaluate fold_left Z.mul on the list *)
    reflexivity.
Qed.