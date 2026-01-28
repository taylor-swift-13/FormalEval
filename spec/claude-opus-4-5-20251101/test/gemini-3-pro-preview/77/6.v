Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example test_iscube_2 : iscube_spec 1000 true.
Proof.
  unfold iscube_spec.
  split.
  - intros _.
    exists 10.
    reflexivity.
  - intros _.
    reflexivity.
Qed.