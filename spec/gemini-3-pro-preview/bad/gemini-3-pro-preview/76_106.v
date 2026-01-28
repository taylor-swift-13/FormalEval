Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 8192 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (H_cases: k <= 6 \/ 7 <= k) by lia.
    destruct H_cases as [H_le_6 | H_ge_7].
    + assert (H_pow : 4 ^ k <= 4 ^ 6).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in H_pow.
      vm_compute in H_pow.
      lia.
    + assert (H_pow : 4 ^ 7 <= 4 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in H_pow.
      vm_compute in H_pow.
      lia.
Qed.