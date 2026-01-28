Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example test_iscube_1 : iscube_spec 728 false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate.
  - intros [n H].
    assert (9 * 9 * 9 = 729) by reflexivity.
    assert (8 * 8 * 8 = 512) by reflexivity.
    nia.
Qed.