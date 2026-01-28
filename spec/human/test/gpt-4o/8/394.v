Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Definition sum_product (l : list Z) : Z * Z :=
  (fold_left Z.add l 0, fold_left Z.mul l 1).

Example test_sum_product : sum_product [-9%Z; 4%Z; -10%Z; -6%Z; 5%Z; 8%Z; -10%Z] = (-18, 864000).
Proof.
  unfold sum_product.
  simpl.
  reflexivity.
Qed.