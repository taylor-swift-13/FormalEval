Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_2 : iscube_spec 1000 true.
Proof.
  unfold iscube_spec.
  split.
  - intros _.
    exists 10.
    simpl.
    reflexivity.
  - intros _.
    reflexivity.
Qed.