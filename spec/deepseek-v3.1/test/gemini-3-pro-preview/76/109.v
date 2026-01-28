Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4722366482869645213696 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk_pos Hk_eq]].
    (* We show that 6^27 < x < 6^28, so k cannot be an integer *)
    assert (H_lower: (6 ^ 27 < 4722366482869645213696)%Z) by (vm_compute; reflexivity).
    assert (H_upper: (4722366482869645213696 < 6 ^ 28)%Z) by (vm_compute; reflexivity).
    
    assert (k <= 27 \/ k >= 28) as [Hle | Hge] by lia.
    + (* Case k <= 27 *)
      assert (6 ^ k <= 6 ^ 27)%Z.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk_eq in H.
      lia.
    + (* Case k >= 28 *)
      assert (6 ^ 28 <= 6 ^ k)%Z.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk_eq in H.
      lia.
Qed.