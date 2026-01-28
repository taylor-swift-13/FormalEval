Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 4722366482869645213695 4722366482869645213696 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk_pos Hk_eq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk0 | [Hk1 | Hk2]] by lia.
    + subst k. simpl in Hk_eq. lia.
    + subst k. simpl in Hk_eq. lia.
    + assert (4722366482869645213696 ^ 2 <= 4722366482869645213696 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      assert (4722366482869645213696 < 4722366482869645213696 ^ 2).
      { rewrite Z.pow_2_r. apply Z.lt_mul_diag_r; lia. }
      lia.
Qed.