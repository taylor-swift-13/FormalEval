Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 23 15 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_pos Hk_pow]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk0 | [Hk1 | Hk2]] by lia.
    + subst k. simpl in Hk_pow. lia.
    + subst k. simpl in Hk_pow. lia.
    + assert (15 ^ 2 <= 15 ^ k) as H_le.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_le.
      rewrite Hk_pow in H_le.
      lia.
Qed.