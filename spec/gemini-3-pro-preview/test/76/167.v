Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 65537 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_nonneg Hk_eq]].
    assert (H_cases: k < 7 \/ k >= 7) by lia.
    destruct H_cases as [H_small | H_large].
    + assert (H_vals: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
      destruct H_vals as [? | [? | [? | [? | [? | [? | ?]]]]]]; subst k; vm_compute in Hk_eq; lia.
    + assert (H_mono: 5 ^ 7 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      change (5 ^ 7) with 78125 in H_mono.
      rewrite <- Hk_eq in H_mono.
      lia.
Qed.