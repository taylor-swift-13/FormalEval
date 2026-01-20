Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_1 : iscube_spec 1 true.
Proof.
  unfold iscube_spec.
  split.
  - intros _.
    exists 1.
    simpl.
    reflexivity.
  - intros _.
    reflexivity.
Qed.