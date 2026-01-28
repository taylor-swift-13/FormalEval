Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 6 4722366482869645213696 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk_le Hk_eq]].
    assert (Hk_cases: k = 0 \/ k > 0) by lia.
    destruct Hk_cases as [Hk0 | Hk_pos].
    + subst k. simpl in Hk_eq. discriminate Hk_eq.
    + assert (H_base_pos: 0 < 4722366482869645213696) by reflexivity.
      assert (H_mono: 4722366482869645213696 ^ 1 <= 4722366482869645213696 ^ k).
      { apply Z.pow_le_mono_r. exact H_base_pos. lia. }
      rewrite Z.pow_1_r in H_mono.
      rewrite Hk_eq in H_mono.
      assert (H_contra: 4722366482869645213696 > 6) by reflexivity.
      lia.
Qed.