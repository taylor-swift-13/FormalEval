Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 16777217 16777216 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H as [H0 | [H1 | H2]].
    + subst. simpl in Hk_eq. lia.
    + subst. simpl in Hk_eq. lia.
    + assert (H_pow : 16777216 ^ k >= 16777216 ^ 2).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk_eq in H_pow.
      simpl in H_pow.
      lia.
Qed.