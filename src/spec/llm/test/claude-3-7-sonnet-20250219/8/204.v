Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_negatives :
  sum_product_spec [-9%Z; 3%Z; -5%Z; 0%Z; 3%Z] (-8)%Z 0%Z.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.