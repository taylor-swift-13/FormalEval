Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 19 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hpos Hpow]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk | [Hk | Hk]] by lia.
    + subst. simpl in Hpow. discriminate.
    + subst. simpl in Hpow. discriminate.
    + assert (5 ^ 2 <= 5 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hle.
      rewrite Hpow in Hle.
      lia.
Qed.