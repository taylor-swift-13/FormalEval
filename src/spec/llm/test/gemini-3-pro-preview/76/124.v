Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2189 2188 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge0 Hk_eq]].
    assert (H_cases: k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H_cases as [Hk0 | [Hk1 | Hk2]].
    + subst k. simpl in Hk_eq. lia.
    + subst k. simpl in Hk_eq. lia.
    + assert (H_mono: 2188 ^ 2 <= 2188 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk_eq in H_mono.
      change (2188 ^ 2) with 4787344 in H_mono.
      lia.
Qed.