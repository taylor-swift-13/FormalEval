Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_product_pre : Prop := True.

Definition sum_product_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_sum_product_empty :
  sum_product_spec [] 0 1.
Proof.
  unfold sum_product_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.