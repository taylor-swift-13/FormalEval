Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4 2187 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (H_cases: k = 0 \/ k >= 1) by lia.
    destruct H_cases as [Hk0 | Hk1].
    + subst k. simpl in Hk_eq. discriminate.
    + assert (H_pow: 2187 ^ 1 <= 2187 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_pow.
      rewrite Hk_eq in H_pow.
      lia.
Qed.