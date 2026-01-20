Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_pre : Prop := True.

Definition sum_product_spec (l : list Z) (s: Z) (p: Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example sum_product_test_case :
  sum_product_spec [3%Z; 7%Z; 1%Z; 0%Z; 4%Z; 7%Z; 3%Z; 3%Z; 2%Z; 0%Z; 3%Z] 33 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.