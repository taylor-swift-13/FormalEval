Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example iscube_spec_test_1 : iscube_spec (-9223372036854775808%Z) true.
Proof.
  unfold iscube_spec.
  split.
  - intros _. exists (-2097152)%Z.
    vm_compute. reflexivity.
  - intros _. reflexivity.
Qed.