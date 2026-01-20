Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_zeros_and_negatives :
  sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -6%Z; 1%Z; -1%Z; -3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-9) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Calculate fold_left Z.add *)
    reflexivity.
  - simpl.
    (* Calculate fold_left Z.mul *)
    reflexivity.
Qed.