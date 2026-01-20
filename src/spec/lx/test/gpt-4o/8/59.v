Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_pre : Prop := True.

Definition sum_product_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example sum_product_test_new :
  sum_product_spec [2%Z; 4%Z; 8%Z; 16%Z; 16%Z; 4%Z; 16%Z; 16%Z; 5%Z; -1%Z; 4%Z] 90 (-335544320).
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.