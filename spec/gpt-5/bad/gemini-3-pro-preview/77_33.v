Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_119 : iscube_spec 119 false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    destruct (Z_le_gt_dec 5 k).
    + assert (5^3 <= k^3) by (apply Z.pow_le_mono_l; lia).
      simpl in H. rewrite Hk in H. lia.
    + destruct (Z_le_gt_dec k 0).
      * assert (k^3 <= 0^3) by (apply Z.pow_le_mono_l; lia).
        simpl in H. rewrite Hk in H. lia.
      * assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
        destruct H as [H | [H | [H | H]]]; rewrite H in Hk; simpl in Hk; discriminate.
Qed.