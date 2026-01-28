Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_510 : iscube_spec 510 false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    assert (k > 0).
    {
      destruct k.
      - simpl in Hk. discriminate.
      - lia.
      - simpl in Hk. lia.
    }
    assert (k <= 7 \/ k >= 8) by lia.
    destruct H0 as [Hle | Hge].
    + assert (Z.pow k 3 <= Z.pow 7 3).
      { apply Z.pow_le_mono_l; lia. }
      rewrite Hk in H0. simpl in H0. lia.
    + assert (Z.pow 8 3 <= Z.pow k 3).
      { apply Z.pow_le_mono_l; lia. }
      rewrite Hk in H0. simpl in H0. lia.
Qed.