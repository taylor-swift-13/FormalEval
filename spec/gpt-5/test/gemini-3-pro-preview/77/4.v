Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_2 : iscube_spec 64 true.
Proof.
  unfold iscube_spec.
  split.
  - intros _.
    exists 4.
    simpl.
    reflexivity.
  - intros _.
    reflexivity.
Qed.