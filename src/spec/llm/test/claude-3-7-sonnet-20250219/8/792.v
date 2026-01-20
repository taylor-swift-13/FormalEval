Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_neg_zeros :
  sum_product_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -1%Z; -6%Z; 1%Z; -1%Z; -3%Z; 1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-9) 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    repeat rewrite Z.add_0_l.
    change (-9) with (-9).
    reflexivity.
  - simpl.
    repeat rewrite Z.mul_1_l.
    change 0 with 0%Z.
    reflexivity.
Qed.