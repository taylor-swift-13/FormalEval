Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_large_list :
  sum_product_spec [2%Z; 4%Z; 8%Z; 1%Z; 16%Z; 4%Z; 16%Z; 16%Z; 5%Z; -1%Z; 2%Z; 4%Z; 16%Z; 10%Z; 8%Z] 111 (-53687091200).
Proof.
  unfold sum_product_spec.
  split.
  - (* sum *)
    simpl.
    reflexivity.
  - (* product *)
    simpl.
    reflexivity.
Qed.