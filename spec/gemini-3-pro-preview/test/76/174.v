Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 65537 245 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (H_cases: k = 0 \/ k = 1 \/ k = 2 \/ k >= 3) by lia.
    destruct H_cases as [H0 | [H1 | [H2 | H3]]].
    + rewrite H0 in Heq. vm_compute in Heq. discriminate.
    + rewrite H1 in Heq. vm_compute in Heq. discriminate.
    + rewrite H2 in Heq. vm_compute in Heq. discriminate.
    + assert (H_mono: 245 ^ 3 <= 245 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Heq in H_mono.
      change (245 ^ 3) with 14706125 in H_mono.
      lia.
Qed.