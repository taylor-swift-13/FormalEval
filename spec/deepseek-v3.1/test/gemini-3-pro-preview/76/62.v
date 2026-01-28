Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 11 7 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hge Hpow]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk | [Hk | Hk]] by lia.
    + subst k. simpl in Hpow. lia.
    + subst k. simpl in Hpow. lia.
    + assert (7 ^ 2 <= 7 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hpow in Hle.
      simpl in Hle.
      lia.
Qed.