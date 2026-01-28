Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk_nonneg Hk_eq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk0 | [Hk1 | Hk2]] by lia.
    + rewrite Hk0 in Hk_eq.
      simpl in Hk_eq.
      discriminate.
    + rewrite Hk1 in Hk_eq.
      simpl in Hk_eq.
      discriminate.
    + assert (3 ^ 2 <= 3 ^ k) as H_pow_le.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow_le.
      rewrite Hk_eq in H_pow_le.
      lia.
Qed.