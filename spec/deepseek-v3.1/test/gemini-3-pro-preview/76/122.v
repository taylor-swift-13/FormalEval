Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 243 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k < 8 \/ k >= 8) as [Hlt | Hge] by lia.
    + assert (2 ^ k <= 2 ^ 7).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk_eq in H.
      simpl in H.
      lia.
    + assert (2 ^ 8 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk_eq in H.
      simpl in H.
      lia.
Qed.