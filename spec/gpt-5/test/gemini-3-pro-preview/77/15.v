Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_2 : iscube_spec (-27) true.
Proof.
  unfold iscube_spec.
  split.
  - (* -> direction *)
    intros _.
    exists (-3).
    simpl.
    reflexivity.
  - (* <- direction *)
    intros _.
    reflexivity.
Qed.