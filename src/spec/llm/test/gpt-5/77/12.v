Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example iscube_spec_test_1 : iscube_spec 125%Z true.
Proof.
  unfold iscube_spec.
  split.
  - intros _. exists 5%Z.
    cbn.
    reflexivity.
  - intros _. reflexivity.
Qed.