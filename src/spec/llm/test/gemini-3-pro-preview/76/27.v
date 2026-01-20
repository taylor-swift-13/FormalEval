Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 6 7 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk0 | [Hk1 | Hk2]] by lia.
    + subst k. simpl in Hk_eq. discriminate Hk_eq.
    + subst k. simpl in Hk_eq. discriminate Hk_eq.
    + assert (7 ^ 2 <= 7 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite <- Hk_eq in H.
      lia.
Qed.