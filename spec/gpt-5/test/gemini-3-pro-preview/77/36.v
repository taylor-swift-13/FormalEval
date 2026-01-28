Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_neg6 : iscube_spec (-6) false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    simpl in Hk.
    assert (k <= -2 \/ k = -1 \/ k >= 0) by lia.
    destruct H as [H_le_neg2 | [H_eq_neg1 | H_ge_0]].
    + nia.
    + subst k. discriminate Hk.
    + nia.
Qed.