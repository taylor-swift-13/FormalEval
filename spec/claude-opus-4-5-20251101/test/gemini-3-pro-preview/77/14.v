Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example test_iscube_1 : iscube_spec 512 true.
Proof.
  unfold iscube_spec.
  split.
  - (* -> direction *)
    intros _.
    exists 8.
    reflexivity.
  - (* <- direction *)
    intros _.
    reflexivity.
Qed.