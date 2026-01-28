Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 82 4722366482869645213696 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [k [Hk Hx]].
    destruct (Z.le_gt_cases 1 k) as [Hk1 | Hk0].
    + assert (Hn: 1 <= 4722366482869645213696).
      { vm_compute. congruence. }
      assert (Hpow: 4722366482869645213696 ^ 1 <= 4722366482869645213696 ^ k).
      { apply Z.pow_le_mono_r; try assumption. split; lia. }
      rewrite Z.pow_1_r in Hpow.
      rewrite <- Hx in Hpow.
      vm_compute in Hpow. congruence.
    + assert (k = 0) by lia. subst k.
      rewrite Z.pow_0_r in Hx.
      discriminate Hx.
Qed.