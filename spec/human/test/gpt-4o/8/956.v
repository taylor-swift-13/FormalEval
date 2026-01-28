Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p: Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Definition sum_product (l : list Z) : Z * Z :=
  (fold_left Z.add l 0, fold_left Z.mul l 1).

Example test_sum_product : sum_product [2%Z; -5%Z; 3%Z; 1%Z; 10%Z; -5%Z] = (6, 1500).
Proof.
  unfold sum_product.
  simpl.
  reflexivity.
Qed.