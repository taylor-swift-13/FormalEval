Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 65 64 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (H_range : k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H_range as [H0 | [H1 | H2]].
    + subst k. simpl in Heq. discriminate Heq.
    + subst k. simpl in Heq. discriminate Heq.
    + assert (Hpow : 64 ^ 2 <= 64 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Heq in Hpow.
      simpl in Hpow.
      lia.
Qed.