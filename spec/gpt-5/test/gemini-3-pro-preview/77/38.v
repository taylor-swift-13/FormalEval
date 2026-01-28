Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, Z.pow k 3 = a.

Example test_iscube_58 : iscube_spec 58 false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    assert (H_range: k <= 3 \/ k >= 4) by lia.
    destruct H_range as [H_le | H_ge].
    + assert (H_cases: k <= 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H_cases as [H_neg | [H1 | [H2 | H3]]].
      * assert (H_pow: k ^ 3 <= 0 ^ 3) by (apply Z.pow_le_mono_l; lia).
        rewrite Hk in H_pow. simpl in H_pow. lia.
      * rewrite H1 in Hk. simpl in Hk. lia.
      * rewrite H2 in Hk. simpl in Hk. lia.
      * rewrite H3 in Hk. simpl in Hk. lia.
    + assert (H_pow: 4 ^ 3 <= k ^ 3) by (apply Z.pow_le_mono_l; lia).
      rewrite Hk in H_pow. simpl in H_pow. lia.
Qed.