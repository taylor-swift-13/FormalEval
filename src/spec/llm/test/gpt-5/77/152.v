Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zpow_def.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Axiom no_cube_1336 : forall k : Z, Z.pow k 3 <> 1336%Z.

Example iscube_spec_test_1 : iscube_spec 1336%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [k Hk]. exfalso. apply no_cube_1336 with (k := k). exact Hk.
Qed.