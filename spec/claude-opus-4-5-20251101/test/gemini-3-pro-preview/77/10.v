Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example test_iscube_neg8 : iscube_spec (-8) true.
Proof.
  unfold iscube_spec.
  split.
  - intros _.
    exists (-2).
    reflexivity.
  - intros _.
    reflexivity.
Qed.