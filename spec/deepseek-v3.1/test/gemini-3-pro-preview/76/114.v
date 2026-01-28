Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 245 27 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk_pos Hk_eq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H as [Hk0 | [Hk1 | Hk2]].
    + subst k.
      simpl in Hk_eq.
      discriminate.
    + subst k.
      simpl in Hk_eq.
      discriminate.
    + assert (27 ^ 2 <= 27 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk_eq in H.
      simpl in H.
      lia.
Qed.