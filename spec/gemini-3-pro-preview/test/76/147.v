Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2188 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_nonneg Hk_eq]].
    assert (H_cases: k < 11 \/ k = 11 \/ k > 11) by lia.
    destruct H_cases as [H_lt | [H_eq | H_gt]].
    + assert (H_pow: 2 ^ k < 2 ^ 11).
      { apply Z.pow_lt_mono_r; lia. }
      replace (2 ^ 11) with 2048 in H_pow by reflexivity.
      rewrite <- Hk_eq in H_pow.
      lia.
    + subst k.
      replace (2 ^ 11) with 2048 in Hk_eq by reflexivity.
      lia.
    + assert (H_pow: 2 ^ 12 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      replace (2 ^ 12) with 4096 in H_pow by reflexivity.
      rewrite <- Hk_eq in H_pow.
      lia.
Qed.