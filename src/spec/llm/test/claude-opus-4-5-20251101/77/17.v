Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 1000000%Z true.
Proof.
  unfold iscube_spec.
  split.
  - intros _.
    exists 100%Z.
    reflexivity.
  - intros _.
    reflexivity.
Qed.