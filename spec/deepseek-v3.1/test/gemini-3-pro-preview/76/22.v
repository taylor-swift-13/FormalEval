Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 23 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hge Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk | [Hk | Hk]] by lia.
    + subst k. simpl in Heq. discriminate Heq.
    + subst k. simpl in Heq. discriminate Heq.
    + assert (5 ^ 2 <= 5 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hle.
      rewrite Heq in Hle.
      lia.
Qed.