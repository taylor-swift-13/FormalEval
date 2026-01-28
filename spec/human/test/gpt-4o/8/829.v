Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Definition sum_product (l : list Z) : Z * Z :=
  (fold_left Z.add l 0, fold_left Z.mul l 1).

Example test_sum_product_case : sum_product [-1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -6%Z; 1%Z; -1%Z; -3%Z; 0%Z; 0%Z; -8%Z; 0%Z; 0%Z; 0%Z; 0%Z] = (-18, 0).
Proof.
  unfold sum_product.
  simpl.
  reflexivity.
Qed.