Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list (list Z)) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left (fun acc l => acc + fold_left Z.add l 0) numbers 0 /\
  result_product = fold_left (fun acc l => acc * fold_left Z.mul l 1) numbers 1.

Example test_sum_product_single_list :
  sum_product_spec [[-3%Z; 1%Z; 1%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z]] 0 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.