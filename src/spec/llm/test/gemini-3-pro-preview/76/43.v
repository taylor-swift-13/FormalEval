Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 49 8 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (H_range: k < 2 \/ k >= 2) by lia.
    destruct H_range as [H_small | H_large].
    + assert (H_cases: k = 0 \/ k = 1) by lia.
      destruct H_cases as [H0 | H1]; subst k; simpl in Heq; lia.
    + assert (H_mono: 8 ^ 2 <= 8 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite <- Heq in H_mono.
      lia.
Qed.