Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 82 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (H_cases: k <= 6 \/ 7 <= k) by lia.
    destruct H_cases as [H_le | H_ge].
    + assert (H_pow: 2 ^ k <= 2 ^ 6).
      { apply Z.pow_le_mono_r; lia. }
      change (2 ^ 6) with 64 in H_pow.
      rewrite <- Hk2 in H_pow.
      lia.
    + assert (H_pow: 2 ^ 7 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      change (2 ^ 7) with 128 in H_pow.
      rewrite <- Hk2 in H_pow.
      lia.
Qed.