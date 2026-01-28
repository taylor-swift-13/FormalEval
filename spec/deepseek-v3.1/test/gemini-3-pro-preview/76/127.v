Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 245 244 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk | [Hk | Hk]] by lia.
    + subst k. simpl in Hk2. lia.
    + subst k. simpl in Hk2. lia.
    + assert (244 ^ 2 <= 244 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in H.
      simpl in H.
      lia.
Qed.