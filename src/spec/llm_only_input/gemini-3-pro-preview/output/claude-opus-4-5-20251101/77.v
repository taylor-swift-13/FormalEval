Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example test_iscube_1: iscube_spec 1 true.
Proof.
  unfold iscube_spec.
  split.
  - (* Left to Right: true = true -> exists n, n^3 = 1 *)
    intros _.
    exists 1.
    simpl.
    reflexivity.
  - (* Right to Left: (exists n, n^3 = 1) -> true = true *)
    intros _.
    reflexivity.
Qed.