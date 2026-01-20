Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Axiom not_cube_82 : forall k : Z, Z.pow k 3 <> 82%Z.

Example iscube_spec_test_1 : iscube_spec 82%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    exfalso.
    apply (not_cube_82 k).
    exact Hk.
Qed.