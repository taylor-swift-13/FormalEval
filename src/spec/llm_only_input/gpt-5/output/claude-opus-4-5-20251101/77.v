Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_spec_test_1 : iscube_spec 1%Z true.
Proof.
  unfold iscube_spec.
  split.
  - intros _.
    exists 1%Z.
    rewrite Z.mul_1_r.
    rewrite Z.mul_1_l.
    reflexivity.
  - intros _.
    reflexivity.
Qed.