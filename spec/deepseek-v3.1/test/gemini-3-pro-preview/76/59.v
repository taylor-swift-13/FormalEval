Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 8 64 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k = 0 \/ k >= 1) as [Hk0 | Hk1] by lia.
    + subst k.
      simpl in Hk_eq.
      discriminate Hk_eq.
    + assert (H_pow: 64 ^ 1 <= 64 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow.
      rewrite Hk_eq in H_pow.
      lia.
Qed.