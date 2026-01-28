Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_1 : iscube_spec (-999999) false.
Proof.
  unfold iscube_spec.
  split.
  - intros H.
    discriminate.
  - intros [k Hk].
    simpl in Hk.
    nia.
Qed.