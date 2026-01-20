Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 19 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (H_cases: k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H_cases as [H0 | [H1 | H2]].
    + rewrite H0 in Hk2. simpl in Hk2. discriminate.
    + rewrite H1 in Hk2. simpl in Hk2. discriminate.
    + assert (H_mono: 5 ^ 2 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in H_mono.
      simpl in H_mono.
      lia.
Qed.