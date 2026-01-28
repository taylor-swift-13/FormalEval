Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Definition sum_product (l : list Z) : Z * Z :=
  (fold_left Z.add l 0, fold_left Z.mul l 1).

Example test_sum_product_non_empty : sum_product [-1; 6; 1; 0; 4; 8; 4; 7; 7; 2; -2; -1] = (35, 0).
Proof.
  unfold sum_product.
  simpl.
  reflexivity.
Qed.